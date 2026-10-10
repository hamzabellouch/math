import OAI.Analysis.OperatorAlgebra.ScalarLpSuperlevel

namespace OAI

/-! Interval projections are strong limits of cosine superlevel projections.
Thus commuting with the real character group implies commuting with the
concrete exhausting spectral cutoffs used for modular weights. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace WeakPureInfiniteness

lemma cosineSuperlevel_eventually_interval (n : ℕ) (t : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      (t ∈ scalarCosineSuperlevel ((k + 1 : ℕ) : ℝ)⁻¹
        (Real.cos ((n : ℝ) / (k + 1 : ℕ))) ↔ t ∈ Icc (-(n : ℝ)) n) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max |t| (n : ℝ) / Real.pi)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hd : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hNk : (N : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (hk.trans (Nat.le_succ k))
  have hmax : max |t| (n : ℝ) < ((k + 1 : ℕ) : ℝ) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (hN.trans_le hNk)
  have ht : |t| / ((k + 1 : ℕ) : ℝ) ∈ Icc 0 Real.pi := by
    constructor
    · positivity
    · apply (div_le_iff₀ hd).mpr
      simpa only [mul_comm] using (le_max_left |t| (n : ℝ)).trans hmax.le
  have hn : (n : ℝ) / ((k + 1 : ℕ) : ℝ) ∈ Icc 0 Real.pi := by
    constructor
    · positivity
    · apply (div_le_iff₀ hd).mpr
      simpa only [mul_comm] using (le_max_right |t| (n : ℝ)).trans hmax.le
  change (Real.cos ((n : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤
    Real.cos (((k + 1 : ℕ) : ℝ)⁻¹ * t)) ↔ _
  have hct : Real.cos (t / ((k + 1 : ℕ) : ℝ)) =
      Real.cos (|t| / ((k + 1 : ℕ) : ℝ)) := by
    rw [← Real.cos_abs (t / ((k + 1 : ℕ) : ℝ)), abs_div, abs_of_pos hd]
  rw [mul_comm _ t, ← div_eq_mul_inv, hct]
  rw [Real.strictAntiOn_cos.le_iff_ge hn ht, div_le_div_iff_of_pos_right hd]
  exact abs_le

lemma scalarCosineSuperlevel_interval_strong (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun k => scalarCosineSuperlevelProjection ((k + 1 : ℕ) : ℝ)⁻¹
      (Real.cos ((n : ℝ) / (k + 1 : ℕ))) f) atTop (𝓝 (scalarIntervalProjection n f)) := by
  let b (k : ℕ) : ℝ → ℂ :=
    (scalarCosineSuperlevel ((k + 1 : ℕ) : ℝ)⁻¹
      (Real.cos ((n : ℝ) / (k + 1 : ℕ)))).indicator (fun _ => 1)
  let a : ℝ → ℂ := (Icc (-(n : ℝ)) n).indicator (fun _ => 1)
  have hb (k : ℕ) : AEStronglyMeasurable (b k) volume :=
    (measurable_const.indicator (scalarCosineSuperlevel_measurable _ _)).aestronglyMeasurable
  have ha : AEStronglyMeasurable a volume :=
    (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
  have hbn (k : ℕ) (t : ℝ) : ‖b k t‖ ≤ 1 := by
    change ‖(scalarCosineSuperlevel ((k + 1 : ℕ) : ℝ)⁻¹
      (Real.cos ((n : ℝ) / (k + 1 : ℕ)))).indicator (fun _ : ℝ => (1 : ℂ)) t‖ ≤ 1
    by_cases ht : t ∈ scalarCosineSuperlevel ((k + 1 : ℕ) : ℝ)⁻¹
      (Real.cos ((n : ℝ) / (k + 1 : ℕ)))
    · rw [Set.indicator_of_mem ht]
      norm_num
    · rw [Set.indicator_of_notMem ht]
      norm_num
  have han (t : ℝ) : ‖a t‖ ≤ 1 := by
    dsimp only [a]
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  have hlim (t : ℝ) : Tendsto (fun k => b k t) atTop (𝓝 (a t)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [cosineSuperlevel_eventually_interval n t] with k hk
    change (Icc (-(n : ℝ)) n).indicator (fun _ : ℝ => (1 : ℂ)) t =
      (scalarCosineSuperlevel ((k + 1 : ℕ) : ℝ)⁻¹
        (Real.cos ((n : ℝ) / (k + 1 : ℕ)))).indicator (fun _ : ℝ => (1 : ℂ)) t
    by_cases ht : t ∈ Icc (-(n : ℝ)) n
    · have hk' := hk.mpr ht
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem hk']
    · have hk' : t ∉ scalarCosineSuperlevel ((k + 1 : ℕ) : ℝ)⁻¹
          (Real.cos ((n : ℝ) / (k + 1 : ℕ))) := fun h => ht (hk.mp h)
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hk']
  have heq (k : ℕ) : boundedScalarLp volume (b k) (hb k) 1 (hbn k) =
      scalarCosineSuperlevelProjection ((k + 1 : ℕ) : ℝ)⁻¹
        (Real.cos ((n : ℝ) / (k + 1 : ℕ))) := by
    rfl
  have heqa : boundedScalarLp volume a ha 1 han = scalarIntervalProjection n := by rfl
  simpa only [heq, heqa] using
    boundedScalarLp_strong b a hb ha 1 zero_le_one hbn han hlim f

theorem scalarLp_commute_intervalProjection
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hc : ∀ s, Commute T
      (modularDualUnitary (H := ℂ) volume s : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume))
    (n : ℕ) : Commute T (scalarIntervalProjection n) :=
  commute_of_strong_limit T (scalarIntervalProjection n)
    (fun k => scalarCosineSuperlevelProjection ((k + 1 : ℕ) : ℝ)⁻¹
      (Real.cos ((n : ℝ) / (k + 1 : ℕ))))
    (fun _k => scalarLp_commute_cosine_superlevel T hc _ _)
    (scalarCosineSuperlevel_interval_strong n)

end WeakPureInfiniteness

end

end OAI
