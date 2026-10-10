import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TensorGradeFiniteSum

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def globalGradeLof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d : slopeDimensions c η hc θ) (u : ℤ) :
    FGrade (unitalSourceFiltration a c η hc θ d.val) u →ₗ[ℚ] UnitalShuffle a c η hc θ :=
  DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (d,u)

noncomputable def globalSplitGradeCoproduct (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d : slopeDimensions c η hc θ)
    (s : SlopeSplit c η hc θ d.val) (u : ℤ) :
    FGrade (unitalSourceFiltration a c η hc θ d.val) u →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  globalSplitCoproduct a c η hc θ (d,u) s

lemma globalCoproduct_tensor_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id
      (globalTensorGradeInclusion a c η hc θ d e W x)=
      ∑ s : SlopeSplit c η hc θ d.val,
        tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
          (unitalSourceFiltration a c η hc θ e.val)
          (unitalSourceFiltration_antitone a c η hc θ d.val)
          (unitalSourceFiltration_antitone a c η hc θ e.val)
          (fun u=>globalSplitGradeCoproduct a c η hc θ d s u)
          (fun v=>globalGradeLof a c η hc θ e v) W x := by
  have hh : (fun u=>(globalCoproduct a c η hc θ).comp
      (globalGradeLof a c η hc θ d u))=
      (fun u=>∑ s : SlopeSplit c η hc θ d.val,globalSplitGradeCoproduct a c η hc θ d s u) := by
    funext u
    apply LinearMap.ext
    intro y
    change globalCoproduct a c η hc θ (globalGradeLof a c η hc θ d u y)=_
    exact (globalCoproduct_lof a c η hc θ (d,u) y).trans
      (LinearMap.sum_apply Finset.univ (fun s : SlopeSplit c η hc θ d.val=>
        globalSplitCoproduct a c η hc θ (d,u) s) y).symm
  have H := tensorGradeLift_comp
    (unitalSourceFiltration a c η hc θ d.val) (unitalSourceFiltration a c η hc θ e.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ e.val)
    (fun u=>globalGradeLof a c η hc θ d u)
    (fun v=>globalGradeLof a c η hc θ e v)
    (globalCoproduct a c η hc θ) LinearMap.id W x
  simp only [LinearMap.id_comp,hh] at H
  exact H.trans (tensorGradeLift_sum_left _ _ _ _
    (fun s u=>globalSplitGradeCoproduct a c η hc θ d s u)
    (fun v=>globalGradeLof a c η hc θ e v) W x)

lemma globalCoproduct_tensor_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : slopeDimensions c η hc θ) (W : ℤ)
    (x : UnitalSourceTensorGrade a c η hc θ d.val e.val W) :
    TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ)
      (globalTensorGradeInclusion a c η hc θ d e W x)=
      ∑ s : SlopeSplit c η hc θ e.val,
        tensorGradeLift (unitalSourceFiltration a c η hc θ d.val)
          (unitalSourceFiltration a c η hc θ e.val)
          (unitalSourceFiltration_antitone a c η hc θ d.val)
          (unitalSourceFiltration_antitone a c η hc θ e.val)
          (fun v=>globalGradeLof a c η hc θ d v)
          (fun u=>globalSplitGradeCoproduct a c η hc θ e s u) W x := by
  have hh : (fun u=>(globalCoproduct a c η hc θ).comp
      (globalGradeLof a c η hc θ e u))=
      (fun u=>∑ s : SlopeSplit c η hc θ e.val,globalSplitGradeCoproduct a c η hc θ e s u) := by
    funext u
    apply LinearMap.ext
    intro y
    change globalCoproduct a c η hc θ (globalGradeLof a c η hc θ e u y)=_
    exact (globalCoproduct_lof a c η hc θ (e,u) y).trans
      (LinearMap.sum_apply Finset.univ (fun s : SlopeSplit c η hc θ e.val=>
        globalSplitCoproduct a c η hc θ (e,u) s) y).symm
  have H := tensorGradeLift_comp
    (unitalSourceFiltration a c η hc θ d.val) (unitalSourceFiltration a c η hc θ e.val)
    (unitalSourceFiltration_antitone a c η hc θ d.val)
    (unitalSourceFiltration_antitone a c η hc θ e.val)
    (fun u=>globalGradeLof a c η hc θ d u)
    (fun v=>globalGradeLof a c η hc θ e v)
    LinearMap.id (globalCoproduct a c η hc θ) W x
  simp only [LinearMap.id_comp,hh] at H
  exact H.trans (tensorGradeLift_sum_right _ _ _ _
    (fun v=>globalGradeLof a c η hc θ d v)
    (fun s u=>globalSplitGradeCoproduct a c η hc θ e s u) W x)

noncomputable def globalIteratedLeftSplit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (left s.val)) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      (UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ)⊗[ℚ]UnitalShuffle a c η hc θ :=
  (tensorGradeLift (unitalSourceFiltration a c η hc θ (left s.val))
    (unitalSourceFiltration a c η hc θ (right s.val))
    (unitalSourceFiltration_antitone a c η hc θ (left s.val))
    (unitalSourceFiltration_antitone a c η hc θ (right s.val))
    (fun u=>globalSplitCoproduct a c η hc θ (⟨left s.val,s.property.1⟩,u) t)
    (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨right s.val,s.property.2⟩,v)) k.2).comp
      ((unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
        (s.property.1.compatible s.property.2) k.2).comp
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl).toLinearMap)

noncomputable def globalIteratedRightSplit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (s : SlopeSplit c η hc θ k.1.val) (t : SlopeSplit c η hc θ (right s.val)) :
    unitalComponent a c η hc θ k →ₗ[ℚ]
      UnitalShuffle a c η hc θ⊗[ℚ](UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ) :=
  (tensorGradeLift (unitalSourceFiltration a c η hc θ (left s.val))
    (unitalSourceFiltration a c η hc θ (right s.val))
    (unitalSourceFiltration_antitone a c η hc θ (left s.val))
    (unitalSourceFiltration_antitone a c η hc θ (right s.val))
    (fun v=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (⟨left s.val,s.property.1⟩,v))
    (fun u=>globalSplitCoproduct a c η hc θ (⟨right s.val,s.property.2⟩,u) t) k.2).comp
      ((unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
        (s.property.1.compatible s.property.2) k.2).comp
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl).toLinearMap)

lemma globalCoproduct_iterated_left_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map (globalCoproduct a c η hc θ) LinearMap.id
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (left s.val),
        globalIteratedLeftSplit a c η hc θ k s t x := by
  rw [globalCoproduct_lof,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact globalCoproduct_tensor_left a c η hc θ ⟨left s.val,s.property.1⟩
    ⟨right s.val,s.property.2⟩ k.2
    (unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x))

lemma globalCoproduct_iterated_right_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map LinearMap.id (globalCoproduct a c η hc θ)
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      ∑ s : SlopeSplit c η hc θ k.1.val,∑ t : SlopeSplit c η hc θ (right s.val),
        globalIteratedRightSplit a c η hc θ k s t x := by
  rw [globalCoproduct_lof,map_sum]
  apply Finset.sum_congr rfl
  intro s _
  exact globalCoproduct_tensor_right a c η hc θ ⟨left s.val,s.property.1⟩
    ⟨right s.val,s.property.2⟩ k.2
    (unitalGradeCoproduct a c η hc θ (left s.val) (right s.val)
      (s.property.1.compatible s.property.2) k.2
        (unitalGradeCast a c η hc θ (left_add_right s.val).symm rfl x))
end ElementaryPositivity.RawShuffle

end

end OAI
