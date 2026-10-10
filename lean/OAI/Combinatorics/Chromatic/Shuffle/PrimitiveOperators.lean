import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveSpace
import OAI.Combinatorics.Chromatic.Walls.PrimitiveStrings

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open CommonTranslation
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma derivativeB_properFiltered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) :
    derivativeB a (SlopeArithmetic.slope c η) d f∈properSourceFiltration a c η hc θ d W := by
  apply polynomial_coeff_mem (properSourceFiltration a c η hc θ d W) (taylorB a _ d f)
  intro t
  rw [taylorB_eval]
  exact properSourceFiltration_translation_mem a c η hc θ d W f hf t

lemma meanMultiplyB_properFiltered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈properSourceFiltration a c η hc θ d W) :
    meanMultiplyB a (SlopeArithmetic.slope c η) d f∈properSourceFiltration a c η hc θ d W := by
  change meanB a (SlopeArithmetic.slope c η) d*f∈_
  rw [mul_comm]
  exact properSourceFiltration_mul_mem a c η hc θ d W f _ hf

lemma gradeDerivative_primitive (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) (hf : f∈primitiveSpace a c η hc θ hχ d W) :
    gradeDerivative a c η hc θ d W f∈primitiveSpace a c η hc θ hχ d W := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [primitiveSpace_mk_iff] at hf
    let y : sourceFiltration a c η hc θ d W :=
      ⟨derivativeB a (SlopeArithmetic.slope c η) d f.val,
        derivativeB_filtered a c η hc θ d W f.val f.property⟩
    change (Submodule.Quotient.mk y : SourceAssociatedGrade a c η hc θ d W)∈_
    exact (primitiveSpace_mk_iff a c η hc θ hχ d W y).mpr
      (derivativeB_properFiltered a c η hc θ d (W+1) f.val hf)

lemma gradeMeanMultiply_primitive (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : SourceAssociatedGrade a c η hc θ d W) (hf : f∈primitiveSpace a c η hc θ hχ d W) :
    gradeMeanMultiply a c η hc θ d W f∈primitiveSpace a c η hc θ hχ d W := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    rw [primitiveSpace_mk_iff] at hf
    let y : sourceFiltration a c η hc θ d W :=
      ⟨meanMultiplyB a (SlopeArithmetic.slope c η) d f.val,
        meanMultiplyB_filtered a c η hc θ d W f.val f.property⟩
    change (Submodule.Quotient.mk y : SourceAssociatedGrade a c η hc θ d W)∈_
    exact (primitiveSpace_mk_iff a c η hc θ hχ d W y).mpr
      (meanMultiplyB_properFiltered a c η hc θ d (W+1) f.val hf)

lemma gradeDerivative_locally_nilpotent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : SourceAssociatedGrade a c η hc θ d W) :
    ∃ N : ℕ,(gradeDerivative a c η hc θ d W^N) f=0 :=
  LinearFiltration.map_locally_nilpotent _ _ _ _ _
    (derivativeB_locally_nilpotent a (SlopeArithmetic.slope c η) d) f

noncomputable def primitiveDerivative (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    Module.End ℚ (primitiveSpace a c η hc θ hχ d W) :=
  LinearFiltration.restrict _ _ (gradeDerivative a c η hc θ d W)
    (gradeDerivative_primitive a c η hc θ hχ d W)

noncomputable def primitiveMeanMultiply (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ) :
    Module.End ℚ (primitiveSpace a c η hc θ hχ d W) :=
  LinearFiltration.restrict _ _ (gradeMeanMultiply a c η hc θ d W)
    (gradeMeanMultiply_primitive a c η hc θ hχ d W)

lemma primitive_weyl (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (hd : d≠0) (W : ℤ)
    (f : primitiveSpace a c η hc θ hχ d W) :
    primitiveDerivative a c η hc θ hχ d W (primitiveMeanMultiply a c η hc θ hχ d W f)=
      primitiveMeanMultiply a c η hc θ hχ d W (primitiveDerivative a c η hc θ hχ d W f)+f := by
  apply Subtype.ext
  exact gradeDerivative_meanMultiply_weyl a c η hc θ d hd W f.val

lemma primitiveDerivative_locally_nilpotent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d : I → ℕ) (W : ℤ)
    (f : primitiveSpace a c η hc θ hχ d W) :
    ∃ N : ℕ,(primitiveDerivative a c η hc θ hχ d W^N) f=0 := by
  obtain ⟨N,hN⟩:=gradeDerivative_locally_nilpotent a c η hc θ d W f.val
  refine ⟨N,Subtype.ext ?_⟩
  change ((LinearFiltration.restrict _ _ _ _^N) f).val=0
  rw [LinearFiltration.restrict_pow_val,hN]

noncomputable def primitiveStringDecomposition (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (d : I → ℕ) (hd : d≠0) (W : ℤ) :
    PrimitiveStrings.Strings (primitiveDerivative a c η hc θ hχ d W) ≃ₗ[ℚ]
      primitiveSpace a c η hc θ hχ d W :=
  PrimitiveStrings.decomposition (primitiveDerivative a c η hc θ hχ d W)
    (primitiveMeanMultiply a c η hc θ hχ d W)
    (primitive_weyl a c η hc θ hχ d hd W)
    (primitiveDerivative_locally_nilpotent a c η hc θ hχ d W)

end ElementaryPositivity.RawShuffle

end

end OAI
