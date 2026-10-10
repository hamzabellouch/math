import OAI.Analysis.Pureness.Stabilization.RankBounds

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter Topology
open scoped NNReal ENNReal
variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def positiveRamp (a : Positive D) (δ : ℝ≥0) : Positive D :=
  ⟨cfcₙ (fun t : ℝ => min (t / δ) 1) a.1, cfcₙ_nonneg (fun t ht =>
    le_min (div_nonneg (quasispectrum_nonneg_of_nonneg a.1 a.2 t ht) δ.2) zero_le_one)⟩

lemma positiveRamp_norm_le (a : Positive D) (δ : ℝ≥0) : ‖(positiveRamp a δ).1‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t ht
  have ht0 : 0 ≤ min (t / (δ : ℝ)) 1 := le_min
    (div_nonneg (quasispectrum_nonneg_of_nonneg a.1 a.2 t ht) δ.2) zero_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg ht0]
  exact min_le_right _ _

lemma positiveRamp_le_smul (a : Positive D) (δ : ℝ≥0) :
    positiveRamp a δ ≤ Positive.smul δ⁻¹ a := by
  change cfcₙ (fun t : ℝ => min (t / δ) 1) a.1 ≤ ((δ⁻¹ : ℝ≥0) : ℝ) • a.1
  rw [← cfcₙ_const_mul_id (↑(δ⁻¹) : ℝ) a.1 (ha := IsSelfAdjoint.of_nonneg a.2)]
  apply (cfcₙ_le_iff _ _ a.1 (hf0 := by simp)
    (ha := IsSelfAdjoint.of_nonneg a.2)).mpr
  intro t _
  simpa only [NNReal.coe_inv, div_eq_mul_inv, mul_comm] using min_le_left (t/(δ : ℝ)) 1

lemma positive_cut_power_le_ramp (a : Positive D) (δ : ℝ≥0) (hδ : 0 < δ)
    (r : ℝ≥0) (hr : 0 < r) :
    Positive.power r (Positive.cut δ a) ≤
      Positive.smul ((max ‖a.1‖₊ 1) ^ (r : ℝ)) (positiveRamp a δ) := by
  change (Positive.cut δ a).1 ^ r ≤
    (((max ‖a.1‖₊ 1) ^ (r : ℝ) : ℝ≥0) : ℝ) • cfcₙ (fun t : ℝ => min (t/δ) 1) a.1
  rw [CFC.nnrpow_eq_cfcₙ_real _ _ (Positive.cut δ a).2]
  change cfcₙ (fun t : ℝ => t ^ (r : ℝ))
    (cfcₙ (fun t : ℝ => max (t-δ) 0) a.1) ≤
    (((max ‖a.1‖₊ 1) ^ (r : ℝ) : ℝ≥0) : ℝ) • cfcₙ (fun t : ℝ => min (t/δ) 1) a.1
  rw [← cfcₙ_comp' (fun t : ℝ => t ^ (r : ℝ)) (fun t : ℝ => max (t-δ) 0)
    a.1 (hg0 := Real.zero_rpow (by exact_mod_cast hr.ne'))]
  rw [← cfcₙ_const_mul (↑((max ‖a.1‖₊ 1) ^ (r : ℝ)) : ℝ)
    (fun t : ℝ => min (t/δ) 1) a.1 (h0 := by simp)]
  apply (cfcₙ_le_iff _ _ a.1
    (hf0 := by simp [Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')])
    (ha := IsSelfAdjoint.of_nonneg a.2)).mpr
  intro t ht
  have htM : t ≤ max ‖a.1‖ 1 := (le_abs_self t).trans
    ((NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a.1 ht
      (IsSelfAdjoint.of_nonneg a.2)).trans (le_max_left _ _))
  have hM : 0 ≤ max ‖a.1‖ 1 := (norm_nonneg _).trans (le_max_left _ _)
  simp only [NNReal.coe_rpow, NNReal.coe_max, coe_nnnorm, NNReal.coe_one]
  by_cases htδ : t ≤ δ
  · rw [max_eq_right (sub_nonpos.mpr htδ),
      Real.zero_rpow (show (r : ℝ) ≠ 0 by exact_mod_cast hr.ne')]
    exact mul_nonneg (Real.rpow_nonneg hM _) (le_min
      (div_nonneg (quasispectrum_nonneg_of_nonneg a.1 a.2 t ht) δ.2) zero_le_one)
  · rw [min_eq_right ((one_le_div (show (0 : ℝ) < δ from hδ)).mpr (lt_of_not_ge htδ).le), mul_one]
    exact Real.rpow_le_rpow (le_max_right _ _) (max_le ((sub_le_self t (show (0 : ℝ) ≤ δ from δ.2)).trans htM) hM) r.2

theorem trace_ramp_envelope (τ : ExtendedTrace D) (a : Positive D)
    (δ : ℝ≥0) (hδ : 0 < δ) :
    τ.rank (Positive.cut δ a) ≤ τ (positiveRamp a δ) ∧
      τ (positiveRamp a δ) ≤ τ.rank a := by
  constructor
  · let M : ℝ≥0 := max ‖a.1‖₊ 1
    have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have ht := ENNReal.Tendsto.mul (ExtendedTrace.root_scalars_tendsto_one M hM)
      (Or.inl one_ne_zero) (tendsto_const_nhds (x := τ (positiveRamp a δ)))
      (Or.inr ENNReal.one_ne_top)
    rw [one_mul] at ht
    apply le_of_tendsto_of_tendsto (τ.tendsto_roots_rank_all (Positive.cut δ a)) ht
    apply Eventually.of_forall
    intro j
    simpa only [τ.map_smul] using
      τ.monotone (positive_cut_power_le_ramp a δ hδ _ (Positive.rootExponent_pos j))
  · exact (τ.apply_le_rank _ (positiveRamp_norm_le a δ)).trans
      ((τ.rank_monotone (positiveRamp_le_smul a δ)).trans_eq
        (τ.rank_smul δ⁻¹ (inv_pos.mpr hδ) a))
end CuntzPureness

end

end OAI
