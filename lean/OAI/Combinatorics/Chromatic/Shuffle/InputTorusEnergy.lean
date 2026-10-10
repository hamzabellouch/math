import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveUnitRows

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ)

def crossInteraction (d : I → ℕ) : ℤ :=
  (∑ i,∑ j,(a i j:ℤ)*d i*d j)-∑ i,(a i i:ℤ)*(d i:ℤ)^2

def staircaseShift (d : I → ℕ) : ℤ :=
  ∑ i,((1:ℤ)-a i i)*(d i:ℤ)*((d i:ℤ)-1)

def inputLinearEnergy (d : I → ℕ) : ℤ := ∑ i,κ i*(d i:ℤ)

omit [DecidableEq I] in
lemma normalization_diagonal (d : I → ℕ) :
    inputShift a κ d-eulerForm a d d=
      inputLinearEnergy κ d-staircaseShift a d+crossInteraction a d := by
  have H : (∑ i,(d i:ℤ)*(κ i+1-a i i))-(∑ i,(d i:ℤ)*(d i:ℤ))=
      (∑ i,κ i*(d i:ℤ))-(∑ i,((1:ℤ)-a i i)*(d i:ℤ)*((d i:ℤ)-1))-
        ∑ i,(a i i:ℤ)*(d i:ℤ)^2 := by
    simp only [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i hi
    ring
  unfold inputShift eulerForm inputLinearEnergy staircaseShift crossInteraction
  linear_combination H

lemma crossInteraction_offdiagonal (d : I → ℕ) :
    crossInteraction a d=∑ i,∑ j,if i=j then 0 else (a i j:ℤ)*d i*d j := by
  unfold crossInteraction
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i hi
  have H : (∑ j,(a i j:ℤ)*d i*d j)=
      (a i i:ℤ)*(d i:ℤ)^2+∑ j,if i=j then 0 else (a i j:ℤ)*d i*d j := by
    calc
      _ = ∑ j,((if i=j then (a i i:ℤ)*(d i:ℤ)^2 else 0)+
          if i=j then 0 else (a i j:ℤ)*d i*d j) := by
        apply Finset.sum_congr rfl; intro j hj
        by_cases h : i=j
        · subst j; simp [pow_two,mul_assoc]
        · simp [h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linear_combination H

variable (ε : I → Bool) (d : I → ℕ)
def inputTorusEnergy (x : InputIndexLists ε d) : ℤ :=
  inputLinearEnergy κ d-2*(listIndexSum ε d x:ℤ)+crossInteraction a d

omit [DecidableEq I] in
theorem inputListEnergy_normalized (ha : ∀ i,a i i=elementaryDiagonal ε i)
    (x : SortedPackExponent d) :
    inputTorusEnergy a κ ε d (inputListEquiv ε d x)=
      normalizedEnergy a κ d (sortedPackDegree d x) := by
  have H:=inputListIndexSum ε d x
  have Hs : (∑ i,((1:ℤ)-elementaryDiagonal ε i)*(d i:ℤ)*((d i:ℤ)-1))=
      staircaseShift a d := by simp only [staircaseShift,ha]
  rw [Hs] at H
  unfold inputTorusEnergy normalizedEnergy
  rw [normalization_diagonal]
  linear_combination -H
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance outputSlopeSymmetricFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

abbrev OutputStart := Σ d : {d : I → ℕ // d≠0},
  Σ W : ℤ,StringBaseIndex a c η hc (slope c η d.val) (hχ.out _) d.val W
noncomputable def outputParameter (κ : I → ℤ) (i : OutputStart a c η hc) : ℤ :=
  normalizedEnergy a κ i.1.val
    (stringBaseDegree a c η hc (slope c η i.1.val) (hχ.out _) i.1.val i.2.1 i.2.2)

lemma outputParameter_upper (κ : I → ℤ) (i : OutputStart a c η hc) :
    outputParameter a c η hc κ i ≤ inputShift a κ i.1.val-eulerForm a i.1.val i.1.val := by
  have H:=stringBaseDegree_nonneg a c η hc (slope c η i.1.val) (hχ.out _) i.1.val i.2.1 i.2.2
  dsimp only [outputParameter,normalizedEnergy]
  omega

lemma finite_nonzero_dimensions_le (D : I → ℕ) : Finite {d : I → ℕ // d≤D ∧ d≠0} := by
  exact Finite.of_injective (fun d : {d : I → ℕ // d≤D ∧ d≠0}=>
    (⟨d.val,d.property.1⟩ : {d : I → ℕ // d≤D})) (by intro x y h; exact Subtype.ext (congrArg (fun z : {d : I → ℕ // d≤D}=>z.val) h))

theorem outputStarts_bounded_finite (κ : I → ℤ) (D : I → ℕ) (L : ℤ) :
    Finite {i : OutputStart a c η hc // i.1.val≤D ∧ L≤outputParameter a c η hc κ i} := by
  let m (d : I → ℕ) := inputShift a κ d-eulerForm a d d-L
  let T := Σ d : {d : I → ℕ // d≤D ∧ d≠0},
    {j : (Σ W : ℤ,StringBaseIndex a c η hc (slope c η d.val) (hχ.out _) d.val W) //
      stringBaseDegree a c η hc (slope c η d.val) (hχ.out _) d.val j.1 j.2 ≤ m d.val}
  let := finite_nonzero_dimensions_le D
  let (d : {d : I → ℕ // d≤D ∧ d≠0}) := stringStarts_bounded_finite a c η hc
    (slope c η d.val) (hχ.out _) d.val d.property.2 rfl (m d.val)
  let f : {i : OutputStart a c η hc // i.1.val≤D ∧ L≤outputParameter a c η hc κ i} → T := fun i=>
    ⟨⟨i.val.1.val,i.property.1,i.val.1.property⟩,⟨i.val.2,by
      have H:=i.property.2
      have Hn:=stringBaseDegree_nonneg a c η hc (slope c η i.val.1.val)
        (hχ.out _) i.val.1.val i.val.2.1 i.val.2.2
      dsimp only [outputParameter,normalizedEnergy] at H
      dsimp only [m]
      omega⟩⟩
  apply Finite.of_injective f
  intro x y h
  have H:=congrArg (fun z : T=>
    (⟨⟨z.1.val,z.1.property.2⟩,z.2.val⟩ : OutputStart a c η hc)) h
  exact Subtype.ext H
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma euler_skew_sum (a : I → I → ℕ) (d e : I → ℕ) :
    eulerForm a d e-eulerForm a e d=
      ∑ i,∑ j,((a j i:ℤ)-a i j)*d i*e j := by
  have H₁ : (∑ i,(d i:ℤ)*e i)=(∑ i,(e i:ℤ)*d i) := by
    apply Finset.sum_congr rfl; intro i hi; ring
  have H₂ : (∑ i,∑ j,(a i j:ℤ)*e i*d j)=(∑ i,∑ j,(a j i:ℤ)*d i*e j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  simp only [eulerForm,H₁,H₂,sub_mul,Finset.sum_sub_distrib]
  ring

omit [DecidableEq I] in
lemma euler_skew_plane (a : I → I → ℕ) (c η : I → ℝ) (t : ℝ)
    (ha : ∀ i j,(a j i:ℝ)-a i j=t*(η i*c j-c i*η j)) (d e : I → ℕ) :
    (eulerForm a d e:ℝ)-eulerForm a e d=
      t*(mass η d*mass c e-mass c d*mass η e) := by
  have H:=congrArg (fun k : ℤ=>(k:ℝ)) (euler_skew_sum a d e)
  push_cast at H
  rw [H]
  simp only [ha]
  have HS (f g : I → ℝ) : (∑ i,∑ j,f i*g j)=(∑ i,f i)*(∑ j,g j) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  calc
    _ = t*((∑ i,∑ j,(d i:ℝ)*η i*((e j:ℝ)*c j))-
        ∑ i,∑ j,(d i:ℝ)*c i*((e j:ℝ)*η j)) := by
      simp only [mul_sub,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      ring
    _ = _ := by rw [HS,HS]; rfl

omit [DecidableEq I] in
theorem slopeEulerSymmetric_of_plane (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (t : ℝ)
    (ha : ∀ i j,(a j i:ℝ)-a i j=t*(η i*c j-c i*η j)) :
    ∀ θ,SlopeEulerSymmetric a c η θ := by
  intro θ d e hd he hs ht
  have H:=euler_skew_plane a c η t ha d e
  rw [mass_eq c η hc d,mass_eq c η hc e,hs,ht] at H
  have Hz : (eulerForm a d e:ℝ)-eulerForm a e d=0 := by
    rw [H]; ring
  exact_mod_cast sub_eq_zero.mp Hz
end ElementaryPositivity.RawShuffle

end

end OAI
