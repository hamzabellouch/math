import OAI.Analysis.Pureness.Completion.CompletedTraceScaling

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal
variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

noncomputable def nonUnitalNormalize (a : A) : A := ‖a‖⁻¹ • a

lemma nonUnitalNormalize_nonneg (a : A) (ha : 0 ≤ a) : 0 ≤ nonUnitalNormalize a :=
  smul_nonneg (inv_nonneg.mpr (norm_nonneg a)) ha

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma nonUnitalNormalize_zero : nonUnitalNormalize (0 : A) = 0 := by
  simp [nonUnitalNormalize]

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonUnitalNormalize_norm_le (a : A) : ‖nonUnitalNormalize a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [nonUnitalNormalize, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma nonUnitalNormalize_smul (a : A) (t : ℝ) (ht : 0 < t) :
    nonUnitalNormalize (t • a) = nonUnitalNormalize a := by
  simp only [nonUnitalNormalize, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    smul_smul, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

noncomputable def nonUnitalRoot (a : A) (j : ℕ) : A :=
  CFC.nnrpow (nonUnitalNormalize a) (((j : ℝ≥0) + 1)⁻¹)

lemma nonUnitalRoot_monotone (a : A) (ha : 0 ≤ a) : Monotone (nonUnitalRoot a) := by
  intro j k hjk
  have hjpos : 0 < ((j : ℝ≥0) + 1)⁻¹ := by positivity
  have hkpos : 0 < ((k : ℝ≥0) + 1)⁻¹ := by positivity
  have hexp : ((k : ℝ≥0) + 1)⁻¹ ≤ ((j : ℝ≥0) + 1)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hjk 1
  simp only [nonUnitalRoot, CFC.nnrpow_eq_pow, CFC.nnrpow_def]
  apply cfcₙ_mono
  · intro z hz
    have hz1 : z ≤ 1 :=
      (NonUnitalIsometricContinuousFunctionalCalculus.quasispectrum_le _ hz
        (nonUnitalNormalize_nonneg a ha)).trans (by exact_mod_cast nonUnitalNormalize_norm_le a)
    by_cases hz0 : z = 0
    · subst z
      change (0 : ℝ≥0) ^ (((j : ℝ≥0) + 1)⁻¹ : ℝ) ≤
        (0 : ℝ≥0) ^ (((k : ℝ≥0) + 1)⁻¹ : ℝ)
      rw [NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos)),
        NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))]
    · apply NNReal.rpow_le_rpow_of_exponent_ge (pos_iff_ne_zero.mpr hz0) hz1
      exact_mod_cast hexp
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos))
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))

lemma nonUnital_nnrpow_map (φ : A →⋆ₙₐ[ℂ] B) (hφ : Continuous φ)
    (a : A) (ha : 0 ≤ a) (r : ℝ≥0) (hr : 0 < r) :
    CFC.nnrpow (φ a) r = φ (CFC.nnrpow a r) := by
  have hb : 0 ≤ φ a := by
    have he : star (CFC.sqrt a) * CFC.sqrt a = a := by
      rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
    rw [← he, map_mul, map_star]
    exact star_mul_self_nonneg _
  simp only [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real a r ha,
    CFC.nnrpow_eq_cfcₙ_real (φ a) r hb]
  exact (φ.map_cfcₙ _ a (Real.continuous_rpow_const (by positivity)).continuousOn
    (Real.zero_rpow (by exact_mod_cast hr.ne')) hφ ha.isSelfAdjoint hb.isSelfAdjoint).symm

lemma nonUnital_nnrpow_smul (a : A) (ha : 0 ≤ a) (s : ℝ) (hs : 0 ≤ s)
    (r : ℝ≥0) (hr : 0 < r) :
    CFC.nnrpow (s • a) r = s ^ (r : ℝ) • CFC.nnrpow a r := by
  have hf0 : (0 : ℝ) ^ (r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  simp only [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real (s • a) r (smul_nonneg hs ha),
    CFC.nnrpow_eq_cfcₙ_real a r ha]
  rw [← cfcₙ_comp_const_mul s (fun t : ℝ => t ^ (r : ℝ)) a
      (hf := (Real.continuous_rpow_const (by positivity)).continuousOn)
      (hf0 := hf0) (ha := ha.isSelfAdjoint),
    ← cfcₙ_const_mul (s ^ (r : ℝ)) (fun t : ℝ => t ^ (r : ℝ)) a]
  apply cfcₙ_congr
  intro t ht
  exact Real.mul_rpow hs (quasispectrum_nonneg_of_nonneg a ha t ht)

end CuntzPureness

end

end OAI
