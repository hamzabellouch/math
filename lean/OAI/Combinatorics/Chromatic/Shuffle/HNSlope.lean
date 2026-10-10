import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.IndexedUnit
import OAI.Combinatorics.Chromatic.GradedAlgebra.FintypeEnergyProduct
import OAI.Combinatorics.Chromatic.Shuffle.HNThreshold

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic EnergyLaurent
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [Fact (∀ θ,SlopeEulerSymmetric a c η θ)]

def slopeValue (θ : ℝ) (d : I → ℕ) : ℝ := mass η d-θ*mass c d
@[simp] lemma slopeValue_zero (θ : ℝ) : slopeValue c η θ 0=0 := by simp [slopeValue]
lemma slopeValue_add (θ : ℝ) (d e : I → ℕ) :
    slopeValue c η θ (d+e)=slopeValue c η θ d+slopeValue c η θ e := by
  simp only [slopeValue,mass_add]
  ring
include hc in
lemma slopeValue_pos_iff (θ : ℝ) (d : I → ℕ) (hd : d≠0) :
    0<slopeValue c η θ d ↔ θ<slope c η d := by
  rw [slopeValue,sub_pos,SlopeArithmetic.slope,lt_div_iff₀ (mass_pos c hc d hd)]
include hc in
lemma slopeValue_nonpos_iff (θ : ℝ) (d : I → ℕ) (hd : d≠0) :
    slopeValue c η θ d≤0 ↔ slope c η d≤θ := by
  rw [slopeValue,sub_nonpos,SlopeArithmetic.slope,div_le_iff₀ (mass_pos c hc d hd)]

variable [DecidableEq I]

lemma decorated_zero_empty (w : DecoratedHN a c η hc 0) : w.val=[] := by
  have H:=HNComposition.length_le 0
    (⟨w.val.map Sigma.fst,⟨w.property.1,w.property.2.1⟩⟩ : HNComposition (0 : I→ℕ))
  simpa only [List.length_map,hnSize_zero,Nat.le_zero,List.length_eq_zero_iff] using H

def highEmpty (θ : ℝ) : HighHNIndex a c η hc θ 0 :=
  ⟨⟨⟨[],by simp⟩,by simp⟩,rfl⟩
def lowEmpty (θ : ℝ) : LowHNIndex a c η hc θ 0 :=
  ⟨⟨⟨[],by simp⟩,by simp⟩,rfl⟩

lemma high_zero_unique (θ : ℝ) (w : HighHNIndex a c η hc θ 0) : w=highEmpty a c η hc θ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact decorated_zero_empty a c η hc (highDecorated a c η hc θ 0 w)
lemma low_zero_unique (θ : ℝ) (w : LowHNIndex a c η hc θ 0) : w=lowEmpty a c η hc θ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact decorated_zero_empty a c η hc (lowDecorated a c η hc θ 0 w)

lemma highSeries_zero (θ : ℝ) : highSeries a κ c η hc θ 0=1 := by
  let : Unique (HighHNIndex a c η hc θ 0):=⟨⟨highEmpty a c η hc θ⟩,high_zero_unique a c η hc θ⟩
  change (family _ _).hsum=1
  rw [HahnSeries.SummableFamily.hsum_unique]
  change HahnSeries.single (-(0:ℤ)) (1:ℚ)=1
  simp
lemma lowSeries_zero (θ : ℝ) : lowSeries a κ c η hc θ 0=1 := by
  let : Unique (LowHNIndex a c η hc θ 0):=⟨⟨lowEmpty a c η hc θ⟩,low_zero_unique a c η hc θ⟩
  change (family _ _).hsum=1
  rw [HahnSeries.SummableFamily.hsum_unique]
  change HahnSeries.single (-(0:ℤ)) (1:ℚ)=1
  simp

lemma decorated_value_nonpos (θ : ℝ) (l : List (RowBlock a c η hc))
    (h : ∀b∈l,slopeValue c η θ b.1≤0) :
    slopeValue c η θ (decoratedDimension a c η hc l)≤0 := by
  induction l with
  | nil=>simp [decoratedDimension]
  | cons b l ih=>
    change slopeValue c η θ (b.1+decoratedDimension a c η hc l)≤0
    rw [slopeValue_add]
    exact add_nonpos (h b (by simp)) (ih (fun e he=>h e (by simp [he])))

lemma decorated_value_pos (θ : ℝ) (l : List (RowBlock a c η hc)) (hl : l≠[])
    (h : ∀b∈l,0<slopeValue c η θ b.1) :
    0<slopeValue c η θ (decoratedDimension a c η hc l) := by
  induction l with
  | nil=>exact (hl rfl).elim
  | cons b l ih=>
    change 0<slopeValue c η θ (b.1+decoratedDimension a c η hc l)
    rw [slopeValue_add]
    have hb:=h b (by simp)
    by_cases hnil : l=[]
    · subst l
      simpa [decoratedDimension] using hb
    · exact add_pos hb (ih hnil (fun e he=>h e (by simp [he])))

lemma highIndex_sign (θ : ℝ) (d : I → ℕ) (w : HighHNIndex a c η hc θ d) :
    d=0 ∨ 0<slopeValue c η θ d := by
  by_cases H : w.val.val.val=[]
  · left
    simpa only [H,decoratedDimension,List.map_nil,List.sum_nil] using w.property.symm
  · right
    rw [←w.property]
    exact decorated_value_pos a c η hc θ _ H (fun b hb=>
      (slopeValue_pos_iff c η hc θ b.1 (w.val.val.property.1 b hb)).mpr (w.val.property b hb))

lemma lowIndex_sign (θ : ℝ) (d : I → ℕ) (w : LowHNIndex a c η hc θ d) :
    slopeValue c η θ d≤0 := by
  rw [←w.property]
  exact decorated_value_nonpos a c η hc θ _ (fun b hb=>
    (slopeValue_nonpos_iff c η hc θ b.1 (w.val.val.property.1 b hb)).mpr (w.val.property b hb))

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open UnitSelections EnergyLaurent WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)

def inputUnitEquiv (d : I → ℕ) : InputIndexLists ε d ≃
    (∀i,UnitIndex (elementaryDiagonal ε i) (d i)) :=
  Equiv.piCongrRight (fun i=>Equiv.subtypeEquivRight (fun f=>by
    cases hi : ε i <;> simp [elementaryDiagonal,hi]))

lemma inputUnit_energy (d : I → ℕ) (x : InputIndexLists ε d) :
    (∑i,unitEnergy (elementaryDiagonal ε i) (d i) (κ i) (inputUnitEquiv ε d x i))+
      crossInteraction a d=inputTorusEnergy a κ ε d x := by
  simp only [unitEnergy,unitWeight,weight,inputUnitEquiv,Equiv.piCongrRight_apply,Pi.map,
    Equiv.subtypeEquivRight_apply,inputTorusEnergy,inputLinearEnergy,
    listIndexSum,Nat.cast_sum,Finset.sum_sub_distrib,←Finset.mul_sum]
  congr 1
  apply congrArg₂ (·-·)
  · apply Finset.sum_congr rfl; intro i hi; ring
  · rfl

def literalInputCoefficient (d : I → ℕ) : LaurentSeries ℚ :=
  (∏i,LaurentRay.atInfinity (PowerSeries.coeff (d i) (indexedUnit (elementaryDiagonal ε i) (κ i)))) *
      HahnSeries.single (-crossInteraction a d) 1

theorem literalInputCoefficient_eq (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    literalInputCoefficient a κ ε d=inputReorderingSeries a κ ε ha d := by
  unfold literalInputCoefficient
  simp only [indexedUnit_literal_expansion,indexedUnitSeries]
  rw [series_pi]
  rw [←series_shift]
  apply series_equiv _ _ (inputUnitEquiv ε d).symm
  intro x
  have H:=inputUnit_energy a κ ε d ((inputUnitEquiv ε d).symm x)
  simpa only [Equiv.apply_symm_apply] using H.symm
end
end ElementaryPositivity.RawShuffle

end

end OAI
