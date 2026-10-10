import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.Product

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma OnSlopeOrZero.mass_eq {c η : I → ℝ} (hc : ∀ i,0<c i)
    {θ : ℝ} {d : I → ℕ} (h : OnSlopeOrZero c η θ d) :
    mass η d=θ*mass c d := by
  rcases h with rfl|h
  · simp only [mass_zero,mul_zero]
  · rw [ElementaryPositivity.SlopeArithmetic.mass_eq c η hc d,h]

lemma high_mass_destabilizes_onSlope (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : OnSlopeOrZero c η θ (d+e))
    (h : mass η d > θ*mass c d) :
    d≠0 ∧ e≠0 ∧ slope c η d>slope c η (d+e) := by
  have hne : d+e≠0 := by
    intro hz
    have hd : d=0 := by
      funext i
      have hi:=congrFun hz i
      simp only [Pi.add_apply,Pi.zero_apply] at hi
      change d i=0
      omega
    simp only [hd,mass_zero,mul_zero,lt_self_iff_false] at h
  have hθ := hs.resolve_left hne
  exact high_mass_destabilizes c η hc d e (by simpa only [hθ] using h)

theorem offSlope_destabilizes_onSlope (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht₁ : OnSlopeOrZero c η θ (d₁+e₁)) (ht₂ : OnSlopeOrZero c η θ (d₂+e₂))
    (hs : OnSlopeOrZero c η θ (d₁+d₂))
    (hoff : ¬CellsOnSlope c η θ d₁ e₁ d₂ e₂) :
    (d₁≠0 ∧ e₁≠0 ∧ slope c η d₁>slope c η (d₁+e₁)) ∨
    (d₂≠0 ∧ e₂≠0 ∧ slope c η d₂>slope c η (d₂+e₂)) := by
  by_cases h₁ : mass η d₁>θ*mass c d₁
  · exact Or.inl (high_mass_destabilizes_onSlope c η hc θ d₁ e₁ ht₁ h₁)
  by_cases h₂ : mass η d₂>θ*mass c d₂
  · exact Or.inr (high_mass_destabilizes_onSlope c η hc θ d₂ e₂ ht₂ h₂)
  have hsrc:=hs.mass_eq hc
  have htar₁:=ht₁.mass_eq hc
  have htar₂:=ht₂.mass_eq hc
  simp only [mass_add] at hsrc htar₁ htar₂
  have hd₁ : mass η d₁=θ*mass c d₁ := by nlinarith
  have hd₂ : mass η d₂=θ*mass c d₂ := by nlinarith
  have he₁ : mass η e₁=θ*mass c e₁ := by nlinarith
  have he₂ : mass η e₂=θ*mass c e₂ := by nlinarith
  exact (hoff ⟨onSlopeOrZero_of_mass c η hc θ d₁ hd₁,
    onSlopeOrZero_of_mass c η hc θ e₁ he₁,onSlopeOrZero_of_mass c η hc θ d₂ hd₂,
    onSlopeOrZero_of_mass c η hc θ e₂ he₂⟩).elim
end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

lemma quotient_cellTransfer_offSlope_unital (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht₁ : OnSlopeOrZero c η θ (d₁+e₁)) (ht₂ : OnSlopeOrZero c η θ (d₂+e₂))
    (hs : OnSlopeOrZero c η θ (d₁+d₂))
    (hoff : ¬CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p)=0 :=
  quotient_cellTransfer_zero a (slope c η) _ _ _ _
    (offSlope_destabilizes_onSlope c η hc θ _ _ _ _ ht₁ ht₂ hs hoff) p

omit [(index : I) → Fintype (A index)] in
lemma quotient_gridShapeTensor_offSlope_unital (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d)
    (hoff : ¬CellsOnSlope c η θ
      (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v)=0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val)+(fun i=>(v i).val)=d
  · apply quotient_cellTransfer_offSlope_unital a c η hc θ
    · rwa [(shape_add_complement u).trans (realization_card R)]
    · rwa [(shape_add_complement v).trans (realization_card T)]
    · rwa [hsum]
    · exact hoff
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [(index : I) → Fintype (A index)] in
theorem quotient_gridTensor_unital_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d) :
    quotientTensor a (slope c η) α β (gridTensor a f g p R T)=
      ∑ u : CutShape (left p),∑ v : CutShape (right p),
        if CellsOnSlope c η θ
          (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)
        then quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) else 0 := by
  classical
  simp only [gridTensor,map_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with hon
  · rfl
  · exact quotient_gridShapeTensor_offSlope_unital a c η hc θ f g p R T u v hα hβ hd hon
end ElementaryPositivity.RawShuffle

end

end OAI
