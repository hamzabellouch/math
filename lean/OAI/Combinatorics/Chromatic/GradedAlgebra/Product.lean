import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.CanonicalCard

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

def OnSlopeOrZero (c η : I → ℝ) (θ : ℝ) (d : I → ℕ) : Prop :=
  d = 0 ∨ slope c η d = θ

lemma onSlopeOrZero_of_mass (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (h : mass η d = θ * mass c d) : OnSlopeOrZero c η θ d := by
  by_cases hd : d=0
  · exact Or.inl hd
  · exact Or.inr ((div_eq_iff (mass_pos c hc d hd).ne').mpr h)

lemma high_mass_destabilizes (c η : I → ℝ) (hc : ∀ i,0<c i) (d e : I → ℕ)
    (h : mass η d > slope c η (d+e) * mass c d) :
    d≠0 ∧ e≠0 ∧ slope c η d > slope c η (d+e) := by
  have hd : d≠0 := by intro hh; simp [hh] at h
  have he : e≠0 := by
    intro hh
    rw [hh,add_zero,mass_eq c η hc d] at h
    exact lt_irrefl _ h
  exact ⟨hd,he,(lt_div_iff₀ (mass_pos c hc d hd)).mpr h⟩

def CellsOnSlope (c η : I → ℝ) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) : Prop :=
  OnSlopeOrZero c η θ d₁ ∧ OnSlopeOrZero c η θ e₁ ∧
    OnSlopeOrZero c η θ d₂ ∧ OnSlopeOrZero c η θ e₂

theorem offSlope_destabilizes (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht : slope c η (d₁+e₁) = slope c η (d₂+e₂))
    (hs : slope c η (d₁+d₂) = slope c η (d₁+e₁))
    (hoff : ¬ CellsOnSlope c η (slope c η (d₁+e₁)) d₁ e₁ d₂ e₂) :
    (d₁≠0 ∧ e₁≠0 ∧ slope c η d₁ > slope c η (d₁+e₁)) ∨
    (d₂≠0 ∧ e₂≠0 ∧ slope c η d₂ > slope c η (d₂+e₂)) := by
  let θ := slope c η (d₁+e₁)
  by_cases h₁ : mass η d₁ > θ * mass c d₁
  · exact Or.inl (high_mass_destabilizes c η hc d₁ e₁ h₁)
  by_cases h₂ : mass η d₂ > θ * mass c d₂
  · exact Or.inr (high_mass_destabilizes c η hc d₂ e₂ (by simpa only [θ,ht] using h₂))
  have hsrc : mass η d₁ + mass η d₂ = θ * (mass c d₁ + mass c d₂) := by
    have h := mass_eq c η hc (d₁+d₂)
    rwa [mass_add,mass_add,hs] at h
  have htar₁ : mass η d₁ + mass η e₁ = θ * (mass c d₁ + mass c e₁) := by
    have h := mass_eq c η hc (d₁+e₁)
    rwa [mass_add,mass_add] at h
  have htar₂ : mass η d₂ + mass η e₂ = θ * (mass c d₂ + mass c e₂) := by
    have h := mass_eq c η hc (d₂+e₂)
    rwa [mass_add,mass_add,← ht] at h
  have hd₁ : mass η d₁ = θ * mass c d₁ := by nlinarith
  have hd₂ : mass η d₂ = θ * mass c d₂ := by nlinarith
  have he₁ : mass η e₁ = θ * mass c e₁ := by nlinarith
  have he₂ : mass η e₂ = θ * mass c e₂ := by nlinarith
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

lemma quotient_cellTransfer_offSlope (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht : slope c η (d₁+e₁) = slope c η (d₂+e₂))
    (hs : slope c η (d₁+d₂) = slope c η (d₁+e₁))
    (hoff : ¬ CellsOnSlope c η (slope c η (d₁+e₁)) d₁ e₁ d₂ e₂)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p) = 0 :=
  quotient_cellTransfer_zero a (slope c η) _ _ _ _ (offSlope_destabilizes c η hc _ _ _ _ ht hs hoff) p

omit [(index : I) → Fintype (A index)] in
lemma quotient_gridShapeTensor_offSlope (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (ht : slope c η α = slope c η β) (hs : slope c η d = slope c η α)
    (hoff : ¬ CellsOnSlope c η (slope c η α)
      (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) = 0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val) + (fun i=>(v i).val) = d
  · apply quotient_cellTransfer_offSlope a c η hc
    · rw [(shape_add_complement u).trans (realization_card R),
        (shape_add_complement v).trans (realization_card T)]
      exact ht
    · rw [hsum,(shape_add_complement u).trans (realization_card R)]
      exact hs
    · rwa [(shape_add_complement u).trans (realization_card R)]
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [(index : I) → Fintype (A index)] in
theorem quotient_gridTensor_sameSlope_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (ht : slope c η α = slope c η β) (hs : slope c η d = slope c η α) :
    quotientTensor a (slope c η) α β (gridTensor a f g p R T) =
      ∑ u : CutShape (left p), ∑ v : CutShape (right p),
        if CellsOnSlope c η (slope c η α)
          (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)
        then quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) else 0 := by
  classical
  simp only [gridTensor,map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with hon
  · rfl
  · exact quotient_gridShapeTensor_offSlope a c η hc f g p R T u v ht hs hon

theorem cleared_restriction_sameSlope_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) {d e α β : I → ℕ} (h : d+e=α+β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) (u : Cut α β)
    (ht : slope c η α = slope c η β) (hs : slope c η d = slope c η α) :
    quotientTensor a (slope c η) α β (crossTensor α β) *
      quotientTensor a (slope c η) α β
        (restrictTensor u (castS h (shufflePolynomial a f g))) =
    crossSign α β •
      ∑ x : CutShape (left (cutRealizationEquiv R u).val),
        ∑ y : CutShape (right (cutRealizationEquiv R u).val),
          if CellsOnSlope c η (slope c η α)
            (fun i=>(x i).val) (shapeComplement x) (fun i=>(y i).val) (shapeComplement y)
          then quotientTensor a (slope c η) α β
            (gridShapeTensor a f g (cutRealizationEquiv R u).val
              (leftRealization R u) (rightRealization R u) x y) else 0 := by
  rw [← map_mul,cleared_restrictTensor a h f g R u,map_smul]
  rw [quotient_gridTensor_sameSlope_support a c η hc f g _ _ _ ht hs]

end ElementaryPositivity.RawShuffle

end

end OAI
