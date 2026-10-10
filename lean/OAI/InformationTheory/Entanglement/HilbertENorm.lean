import OAI.InformationTheory.Entanglement.HilbertCanonicalRecovery

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder ENNReal
open ContinuousLinearMap Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n : Type} [Fintype n] [DecidableEq n]

def hilbertENorm (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (inner ℂ (b i) ((CFC.abs T) (b i))).re
lemma hilbertENorm_eq (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hT : HasFinitePositiveTrace b (CFC.abs T)) :
    hilbertENorm b T=ENNReal.ofReal (hilbertTraceNorm b T) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun i => (nonneg_iff_isPositive.mp hT.1).re_inner_nonneg_right _) hT.2).symm
lemma finite_abs_of_hilbertENorm (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hT : hilbertENorm b T ≠ ⊤) : HasFinitePositiveTrace b (CFC.abs T) := by
  refine ⟨CFC.abs_nonneg T,?_⟩
  have hs := ENNReal.summable_toReal hT
  convert hs using 1
  ext i
  exact (ENNReal.toReal_ofReal
    ((nonneg_iff_isPositive.mp (CFC.abs_nonneg T)).re_inner_nonneg_right (b i))).symm

lemma hilbertErase_econtract (b : HilbertBasis ι ℂ H) (v : n → H)
    (hv : Orthonormal ℂ v) (i₀ : n) {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) :
    ENNReal.ofReal (traceNorm (hilbertErase b v i₀ T))≤hilbertENorm b T := by
  by_cases hf : hilbertENorm b T=⊤
  · rw [hf]; exact le_top
  rw [hilbertENorm_eq b (finite_abs_of_hilbertENorm b hf)]
  exact ENNReal.ofReal_le_ofReal (hilbertErase_contract b v hv i₀
    ⟨hT,finite_abs_of_hilbertENorm b hf⟩)
lemma hilbertErase_positive_difference_econtract (b : HilbertBasis ι ℂ H)
    (v : n → H) (hv : Orthonormal ℂ v) (i₀ : n) {A B : H →L[ℂ] H}
    (hA : HasFinitePositiveTrace b A) (hB : HasFinitePositiveTrace b B) :
    ENNReal.ofReal (traceNorm (hilbertErase b v i₀ A-hilbertErase b v i₀ B))≤hilbertENorm b (A-B) := by
  rw [← hilbertErase_sub b v i₀ A B hA.2 hB.2]
  exact hilbertErase_econtract b v hv i₀ (hA.1.isSelfAdjoint.sub hB.1.isSelfAdjoint)

end SecretKey

end

end OAI
