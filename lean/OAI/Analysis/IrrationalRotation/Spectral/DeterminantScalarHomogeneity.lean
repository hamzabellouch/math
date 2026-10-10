import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentDeterminantReduction
import OAI.Analysis.IrrationalRotation.Spectral.SpectralNaturality

namespace OAI

noncomputable section
open scoped ENNReal CStarAlgebra
namespace Invariant233
variable {A : Type*} [CStarAlgebra A]

theorem star_smul_mul_smul_normSquare (z : ℂ) (a : A) :
    star (z • a) * (z • a) = (‖z‖ ^ 2 : ℝ) • (star a * a) := by
  simp only [star_smul, smul_mul_smul, Complex.star_def, Complex.conj_mul']
  rw [← Complex.ofReal_pow, Complex.coe_smul]

theorem fugledeKadisonDeterminant_smul_of_isUnit
    (τ : TracialState A) (a : A) (ha : IsUnit a) (z : ℂ) (hz : z ≠ 0) :
    fugledeKadisonDeterminant τ (z • a) =
      ENNReal.ofReal ‖z‖ * fugledeKadisonDeterminant τ a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hza : IsUnit (z • a) := by
    simpa only [Algebra.smul_def] using
      ((isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ A)).mul ha
  have hp : IsStrictlyPositive (star a * a) :=
    ⟨star_mul_self_nonneg a, ha.star.mul ha⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have ht (r : ℝ) : τ (algebraMap ℝ A r) = (r : ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using
      τ.map_complex (r : ℂ)
  rw [fugledeKadisonDeterminant_of_isUnit τ _ hza,
      fugledeKadisonDeterminant_of_isUnit τ a ha,
      star_smul_mul_smul_normSquare,
      CFC.log_smul' (star a * a) (sq_pos_of_pos hn) hp]
  change ENNReal.ofReal (Real.exp
    ((τ.toContinuousLinearMap (algebraMap ℝ A (Real.log (‖z‖ ^ 2)) +
      CFC.log (star a * a))).re / 2)) = _
  rw [map_add, ht, Complex.add_re, Complex.ofReal_re, Real.log_pow]
  have he : ((2 : ℝ) * Real.log ‖z‖ + (τ (CFC.log (star a * a))).re) / 2 =
      Real.log ‖z‖ + (τ (CFC.log (star a * a))).re / 2 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.exp_add, Real.exp_log hn,
    ENNReal.ofReal_mul (norm_nonneg z)]

theorem fugledeKadisonDeterminant_sub_scalar_of_normQuasinilpotent
    (τ : TracialState A) {a : A} (ha : NormQuasinilpotent a)
    (z : ℂ) (hz : z ≠ 0) :
    fugledeKadisonDeterminant τ (a - algebraMap ℂ A z) =
      ENNReal.ofReal ‖z‖ * fugledeKadisonDeterminant τ (1 - z⁻¹ • a) := by
  have he : a - algebraMap ℂ A z = (-z) • (1 - z⁻¹ • a) := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hz,
      neg_smul, one_smul]
    abel
  rw [he, fugledeKadisonDeterminant_smul_of_isUnit τ _
    (ha.isUnit_one_sub_smul z⁻¹) (-z) (neg_ne_zero.mpr hz), norm_neg]

end Invariant233

end

end OAI
