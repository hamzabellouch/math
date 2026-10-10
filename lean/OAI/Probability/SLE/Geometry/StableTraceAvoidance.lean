import OAI.Probability.SLE.Loewner.RealBoundaryTraceAvoidance
import OAI.Probability.SLE.Loewner.LoewnerCompactDriverNeighborhood
import OAI.Probability.SLE.Loewner.LoewnerTraceHeight

namespace OAI

/-! Local trace exclusions patch to an open tube by compactness. The
bounded rectangle comes directly from the driver and capacity bounds. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

def StableTraceAvoidance (V : ℝ≥0 → ℝ) (T : ℝ≥0) (z : ℂ) : Prop :=
  ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ), Continuous U →
    ∀ (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
    (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) → ∀ t ∈ Icc 0 T, γ t ∉ ball z r

lemma stableTraceAvoidance_of_surviving
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0) {z : ℂ}
    (hz : z ∈ survivingDomain β T) : StableTraceAvoidance V T z := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (isOpen_survivingDomain hv.1 T) z hz
  have hclosed : closedBall z (r/2) ⊆ survivingDomain β T := by
    intro w hw
    apply hball
    rw [mem_ball]
    exact (mem_closedBall.mp hw).trans_lt (half_lt_self hr)
  obtain ⟨δ,hδ,hkeep⟩ := driver_neighborhood_preserves_compact hv T
    (isCompact_closedBall z (r/2)) hclosed
  refine ⟨r/2,δ,by positivity,hδ,?_⟩
  intro U _ γ G F hw hc t ht hb
  have hD := hkeep U γ G F hw hc (ball_subset_closedBall hb)
  exact hD.1.2 ⟨t,ht,rfl⟩

lemma stableTraceAvoidance_of_real_trajectory
    (V : ℝ≥0 → ℝ) (T : ℝ≥0) (q : ℝ → ℝ) {m : ℝ} (hm : 0 < m)
    (hgap : ∀ t ∈ Icc 0 (T : ℝ), m ≤ q t-V t.toNNReal)
    (hqd : ∀ t ∈ Icc 0 (T : ℝ), HasDerivWithinAt q
      (2/(q t-V t.toNNReal)) (Icc 0 (T : ℝ)) t) :
    StableTraceAvoidance V T (q 0 : ℂ) := by
  obtain ⟨ε,hε,hh⟩ := real_boundary_driver_trace_avoidance V T q hm hgap hqd
  exact ⟨ε,ε,hε,hε,hh⟩

theorem driver_neighborhood_trace_containment
    (V : ℝ≥0 → ℝ) (hV : Continuous V) (T : ℝ≥0) (N : Set ℂ) (hN : IsOpen N)
    (hlocal : ∀ z : ℂ, 0 ≤ z.im → z ∉ N → StableTraceAvoidance V T z) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ), Continuous U →
      ∀ (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) → MapsTo γ (Icc 0 T) N := by
  classical
  by_contra hn
  push Not at hn
  have hc (n : ℕ) := hn ((n+1:ℝ)⁻¹) (by positivity)
  choose U hU γ G F hw hclose hfail using hc
  have hbad (n : ℕ) : ∃ t ∈ Icc 0 T, γ n t ∉ N := by
    by_contra hn
    apply hfail n
    intro t ht
    by_contra htn
    exact hn ⟨t,ht,htn⟩
  choose t ht htN using hbad
  obtain ⟨M,hM,hMb⟩ := ((isCompact_Icc.image hV).isBounded).exists_pos_norm_lt
  have hVM (s : ℝ≥0) (hs : s ∈ Icc 0 T) : |V s| < M := by
    simpa only [Real.norm_eq_abs] using hMb (V s) (mem_image_of_mem V hs)
  have hUb (n : ℕ) (s : ℝ≥0) (hs : s ∈ Icc 0 T) : |U n s| ≤ M+1 := by
    have hi : (n+1:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hh := (hclose n s hs).trans hi
    have hab := abs_sub_abs_le_abs_sub (U n s) (V s)
    linarith [hVM s hs]
  let K := closedBall (0 : ℂ) (M+1+2*Real.sqrt T) ∩
    ({z : ℂ | 0 ≤ z.im} ∩ Nᶜ)
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    ((isClosed_le continuous_const Complex.continuous_im).inter hN.isClosed_compl)
  have hmem (n : ℕ) : γ n (t n) ∈ K := by
    have hr := (hw n).trace_abs_re_le (t n)
      (fun s hs => hUb n s ⟨zero_le,hs.2.trans (ht n).2⟩)
    have hi := ((hw n).trace_height_le (t n)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast (ht n).2)) (by norm_num))
    have hn := Complex.norm_le_abs_re_add_abs_im (γ n (t n))
    rw [abs_of_nonneg ((hw n).2.2.1 (t n))] at hn
    refine ⟨?_,(hw n).2.2.1 (t n),htN n⟩
    rw [mem_closedBall,dist_zero_right]
    exact hn.trans (add_le_add hr hi)
  obtain ⟨z,hz,φ,hφ,hlim⟩ := hK.tendsto_subseq hmem
  obtain ⟨r,δ,hr,hδ,havoid⟩ := hlocal z hz.2.1 hz.2.2
  have hdlim : Tendsto (fun n : ℕ => (φ n+1:ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).comp hφ.tendsto_atTop
  have he : ∀ᶠ n in atTop, γ (φ n) (t (φ n)) ∈ ball z r ∧ (φ n+1:ℝ)⁻¹ < δ :=
    (hlim.eventually (ball_mem_nhds z hr)).and (hdlim.eventually (Iio_mem_nhds hδ))
  obtain ⟨n,hnball,hnd⟩ := he.exists
  exact havoid (U (φ n)) (hU (φ n)) (γ (φ n)) (G (φ n)) (F (φ n)) (hw (φ n))
    (fun s hs => (hclose (φ n) s hs).trans hnd.le) _ (ht (φ n)) hnball

end SLEExactGauge

end

end OAI
