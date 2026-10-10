import OAI.Analysis.Pureness.Comparison.MatrixTrace
import OAI.Analysis.Pureness.Comparison.SupportApproximation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Data.Matrix.Basic

namespace OAI
open scoped BigOperators ComplexOrder ENNReal
open Filter Topology
namespace CuntzComparison
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι] [DecidableEq ι]

noncomputable local instance : ContinuousFunctionalCalculus ℝ (ι → A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable def matrixDiagonalHom : (ι → A) →⋆ₐ[ℂ] CStarMatrix ι ι A :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    { Matrix.diagonalAlgHom (n := ι) (α := A) ℂ with
      map_star' v := by
        ext i j
        by_cases h : i = j
        · subst j; simp
        · simp [h, Ne.symm h] }

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixDiagonal_apply (v : ι → A) (i j : ι) :
    matrixDiagonalHom v i j = if i = j then v i else 0 := rfl

lemma matrixDiagonal_nonneg (v : ι → A) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ matrixDiagonalHom v := by
  let w : ι → A := fun i => CFC.sqrt (v i)
  have h : star w * w = v := by
    funext i
    change star (CFC.sqrt (v i)) * CFC.sqrt (v i) = v i
    rw [(CFC.sqrt_nonneg _).star_eq, CFC.sqrt_mul_sqrt_self _ (hv i)]
  rw [← h, map_mul, map_star]
  exact star_mul_self_nonneg _

lemma matrixDiagonal_cfc (v : ι → A) (hv : ∀ i, IsSelfAdjoint (v i))
    (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (matrixDiagonalHom v) = matrixDiagonalHom (fun i => cfc f (v i)) := by
  have hv' : IsSelfAdjoint v := by change star v = v; funext i; exact (hv i).star_eq
  have hm : IsSelfAdjoint (matrixDiagonalHom v) := hv'.map matrixDiagonalHom
  rw [← matrixDiagonalHom.map_cfc f v hf.continuousOn (by
    change Continuous (fun v : ι → A => fun i j => if i = j then v i else 0)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    split_ifs <;> fun_prop) hv' hm,
    cfc_map_pi (S := ℂ) f v hf.continuousOn hv' hv]

omit [StarOrderedRing A] in
lemma TracialState.matrixTrace_diagonal (τ : TracialState A) (v : ι → A) :
    τ.matrixTraceLinear (matrixDiagonalHom v) = ∑ i, τ.toPositiveLinearMap (v i) := by
  simp [TracialState.matrixTraceLinear]

lemma TracialState.normalizedMatrixTrace_scale (τ : TracialState A) [Nonempty ι]
    (M : CStarMatrix ι ι A) :
    (Fintype.card ι : ℝ) * (τ.normalizedMatrixTrace.toPositiveLinearMap M).re =
      (τ.matrixTraceLinear M).re := by
  change (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ • τ.matrixTraceLinear M).re = _
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := ι)), one_mul]

theorem TracialState.matrixSupportMass_diagonal (τ : TracialState A) [Nonempty ι]
    (v : ι → A) (hv : ∀ i, 0 ≤ v i) :
    (τ.matrixSupportMass (matrixDiagonalHom v) (matrixDiagonal_nonneg v hv)).toReal =
      ∑ i, (τ.spectralSupportMass (v i) (hv i)).toReal := by
  have h1 := (τ.normalizedMatrixTrace.supportApprox_trace_tendsto
    (matrixDiagonal_nonneg v hv)).const_mul (Fintype.card ι : ℝ)
  have h2 := tendsto_finsetSum Finset.univ fun i hi => τ.supportApprox_trace_tendsto (hv i)
  have hseq (n : ℕ) : (Fintype.card ι : ℝ) *
      (τ.normalizedMatrixTrace.toPositiveLinearMap (supportApprox (matrixDiagonalHom v) n)).re =
        ∑ i, (τ.toPositiveLinearMap (supportApprox (v i) n)).re := by
    rw [τ.normalizedMatrixTrace_scale]
    unfold supportApprox
    erw [matrixDiagonal_cfc v (fun i => (hv i).isSelfAdjoint) _ (supportCutoff_continuous n),
      τ.matrixTrace_diagonal, Complex.re_sum]
  have heq := tendsto_nhds_unique (h1.congr fun n => hseq n) h2
  simpa only [TracialState.matrixSupportMass, ENNReal.toReal_mul, ENNReal.toReal_natCast] using heq
end CuntzComparison

end OAI
