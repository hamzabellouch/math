import OAI.Analysis.Pureness.Comparison.SpectralMeasure
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

namespace OAI
open scoped BigOperators ComplexOrder ENNReal
namespace CuntzComparison
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι] [DecidableEq ι]

noncomputable instance matrixRealCFC : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable instance matrixRealNonUnitalCFC :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

instance matrixRealNonnegSpectrum : NonnegSpectrumClass ℝ (CStarMatrix ι ι A) :=
  CStarAlgebra.instNonnegSpectrumClass

noncomputable def TracialState.matrixTraceLinear (τ : TracialState A) : CStarMatrix ι ι A →ₗ[ℂ] ℂ where
  toFun M := ∑ i, τ.toPositiveLinearMap (M i i)
  map_add' M N := by simp [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c M := by simp [CStarMatrix.smul_apply, map_smul, Finset.mul_sum]

omit [StarOrderedRing A] in
lemma TracialState.matrixTrace_one (τ : TracialState A) :
    τ.matrixTraceLinear (1 : CStarMatrix ι ι A) = Fintype.card ι := by
  simp [TracialState.matrixTraceLinear, CStarMatrix.one_apply_eq, τ.normalized]

omit [StarOrderedRing A] [DecidableEq ι] in
lemma TracialState.matrixTrace_cyclic (τ : TracialState A) (M N : CStarMatrix ι ι A) :
    τ.matrixTraceLinear (M * N) = τ.matrixTraceLinear (N * M) := by
  simp only [TracialState.matrixTraceLinear, LinearMap.coe_mk, AddHom.coe_mk,
    CStarMatrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact τ.tracial _ _

lemma TracialState.matrixTrace_nonneg (τ : TracialState A) {M : CStarMatrix ι ι A}
    (hM : 0 ≤ M) : 0 ≤ τ.matrixTraceLinear M := by
  have hfactor : M = star (CFC.sqrt M) * CFC.sqrt M := by
    rw [(CFC.sqrt_nonneg M).star_eq, CFC.sqrt_mul_sqrt_self M hM]
  rw [hfactor]
  simp only [TracialState.matrixTraceLinear, LinearMap.coe_mk, AddHom.coe_mk,
    CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum]
  exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
    τ.toPositiveLinearMap.map_nonneg (star_mul_self_nonneg _)

noncomputable def TracialState.matrixTracePositive (τ : TracialState A) :
    CStarMatrix ι ι A →ₚ[ℂ] ℂ where
  toLinearMap := τ.matrixTraceLinear
  monotone' M N h := by
    apply sub_nonneg.mp
    change 0 ≤ τ.matrixTraceLinear N - τ.matrixTraceLinear M
    rw [← map_sub]
    exact τ.matrixTrace_nonneg (sub_nonneg.mpr h)

noncomputable def TracialState.normalizedMatrixTrace (τ : TracialState A) [Nonempty ι] :
    TracialState (CStarMatrix ι ι A) where
  toPositiveLinearMap :=
    { toFun M := (Fintype.card ι : ℝ)⁻¹ • τ.matrixTraceLinear M
      map_add' M N := by rw [map_add, smul_add]
      map_smul' c M := by rw [map_smul, smul_comm]; rfl
      monotone' M N h := by
        exact smul_le_smul_of_nonneg_left (τ.matrixTracePositive.monotone h) (by positivity) }
  normalized := by
    change (Fintype.card ι : ℝ)⁻¹ • τ.matrixTraceLinear (1 : CStarMatrix ι ι A) = 1
    rw [τ.matrixTrace_one, ← Complex.coe_smul, smul_eq_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := ι))
  tracial M N := congrArg ((Fintype.card ι : ℝ)⁻¹ • ·) (τ.matrixTrace_cyclic M N)

noncomputable def TracialState.matrixSupportMass (τ : TracialState A) [Nonempty ι]
    (M : CStarMatrix ι ι A) (hM : 0 ≤ M) : ℝ≥0∞ :=
  (Fintype.card ι : ℝ≥0∞) * τ.normalizedMatrixTrace.spectralSupportMass M hM

end CuntzComparison

end OAI
