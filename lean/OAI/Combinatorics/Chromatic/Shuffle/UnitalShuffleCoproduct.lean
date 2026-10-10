import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.DimensionGrid
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGradeAlgebra

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration
open scoped TensorProduct DirectSum
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

abbrev SlopeSplit (c η : I → ℝ) (_hc : ∀ i,0<c i) (θ : ℝ) (d : I → ℕ) :=
  {s : DimensionSplit d // OnSlopeOrZero c η θ (left s) ∧ OnSlopeOrZero c η θ (right s)}

noncomputable def globalTensorGradeInclusion (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ) :
    UnitalSourceTensorGrade a c η hc θ d.val e.val W →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  (DirectSum.toModule ℚ ℤ
    (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)
    (fun u=>TensorProduct.map
      (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) (d,u))
      (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) (e,W-u)))).comp
    (unitalSourceTensorGradeEquiv a c η hc θ d.val e.val W).symm.toLinearMap

noncomputable def globalSplitCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  (globalTensorGradeInclusion a c η hc θ ⟨left s.val,s.property.1⟩
    ⟨right s.val,s.property.2⟩ k.2).comp
    ((unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2).comp
      (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl).toLinearMap)

noncomputable def globalHomogeneousCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  ∑ s : SlopeSplit c η hc θ k.1.val,globalSplitCoproduct a c η hc θ k s

noncomputable def globalCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) :
    UnitalShuffle a c η hc θ →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  DirectSum.toModule ℚ (SlopeWeight c η hc θ)
    (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)
    (globalHomogeneousCoproduct a c η hc θ)

lemma globalCoproduct_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    globalCoproduct a c η hc θ
      (DirectSum.lof ℚ (SlopeWeight c η hc θ) (unitalComponent a c η hc θ) k x)=
      ∑ s : SlopeSplit c η hc θ k.1.val,globalSplitCoproduct a c η hc θ k s x := by
  rw [globalCoproduct,DirectSum.toModule_lof]
  exact LinearMap.sum_apply _ _ _

end ElementaryPositivity.RawShuffle

end

end OAI
