import Mathlib

namespace OAI

/-! Exhaustion of successful multipoint paths by nonsingular cutoffs.
Each point is monitored only through its own completion time. Later
swallowing of an already completed point does not enter this lemma. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge.Multipoint

lemma eventually_compact_positive_reciprocal {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K)
    (hpos : ∀ x ∈ K, 0 < f x) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, 1 / ((n : ℝ)+1) < f x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds (hpos x hx))] with n hn
    intro y hy
    exact hn.trans_le (hmin hy)
  · exact Eventually.of_forall (fun _ x hx => False.elim (hne ⟨x, hx⟩))

/-- On a successful path, finitely many individually stopped points admit
one common height, angle, and physical-time cutoff. -/
theorem successful_path_eventually_inside_cutoff
    {ι : Type*} [Finite ι] (T : ι → ℝ) (Y θ : ι → ℝ → ℝ)
    (hY : ∀ i, ContinuousOn (Y i) (Icc 0 (T i)))
    (hθ : ∀ i, ContinuousOn (θ i) (Icc 0 (T i)))
    (hYpos : ∀ i t, t ∈ Icc 0 (T i) → 0 < Y i t)
    (hθpos : ∀ i t, t ∈ Icc 0 (T i) → 0 < θ i t)
    (hθpi : ∀ i t, t ∈ Icc 0 (T i) → θ i t < Real.pi) :
    ∀ᶠ n : ℕ in atTop, ∀ i,
      T i < (n : ℝ)+1 ∧ ∀ t ∈ Icc 0 (T i),
        1 / ((n : ℝ)+1) < Y i t ∧
        1 / ((n : ℝ)+1) < θ i t ∧
        θ i t < Real.pi - 1 / ((n : ℝ)+1) := by
  apply eventually_all.mpr
  intro i
  have htime : ∀ᶠ n : ℕ in atTop, T i < (n : ℝ)+1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (T i)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hheight := eventually_compact_positive_reciprocal isCompact_Icc (hY i) (hYpos i)
  have hangle := eventually_compact_positive_reciprocal isCompact_Icc (hθ i) (hθpos i)
  have hupper := eventually_compact_positive_reciprocal isCompact_Icc
    (continuousOn_const.sub (hθ i)) (fun t ht => sub_pos.mpr (hθpi i t ht))
  filter_upwards [htime, hheight, hangle, hupper] with n hn hy ha hb
  refine ⟨hn, fun t ht => ⟨hy t ht, ha t ht, ?_⟩⟩
  have hupper' : 1 / ((n : ℝ)+1) < Real.pi - θ i t := hb t ht
  linarith

/-- Bounds for nonsingular stopped products pass to the successful event
when each successful path eventually lies inside every cutoff. -/
lemma measure_le_of_eventual_cutoffs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : Set Ω) (cutoff : ℕ → Set Ω) (C : ℝ≥0∞)
    (hcover : ∀ ω ∈ E, ∀ᶠ n : ℕ in atTop, ω ∈ cutoff n)
    (hbound : ∀ n, P (cutoff n) ≤ C) : P E ≤ C := by
  let tail (N : ℕ) := ⋂ n ≥ N, cutoff n
  have hmono : Monotone tail := by
    intro N M hNM ω hω
    simp only [tail, mem_iInter] at hω ⊢
    exact fun n hn => hω n (hNM.trans hn)
  have hsub : E ⊆ ⋃ N, tail N := by
    intro ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hcover ω hω)
    exact mem_iUnion.mpr ⟨N, mem_iInter₂.mpr hN⟩
  apply (measure_mono hsub).trans
  rw [hmono.measure_iUnion]
  apply iSup_le
  intro N
  exact (measure_mono (show tail N ⊆ cutoff N from
    fun ω hω => mem_iInter₂.mp hω N le_rfl)).trans (hbound N)

end SLEExactGauge.Multipoint

end

end OAI
