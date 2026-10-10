import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.FinitelySupportedUnitRows
import OAI.Combinatorics.Chromatic.Walls.StringReorderingEnergy

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic SignedMultiplicity UnitSelections
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  (θ : ℝ) [hχ : Fact (SlopeEulerSymmetric a c η θ)]
local instance : DecidableEq (GlobalStringIndex a c η hc θ) :=
  (globalStringIndexLinearOrder a c η hc θ).toDecidableEq

abbrev SlopeStringStart := Σ k : NonzeroSlopeWeight c η hc θ,
  StringBaseIndex a c η hc θ hχ.out k.val.1.val k.val.2

def stringLetterStartEquiv : GlobalStringIndex a c η hc θ ≃ SlopeStringStart a c η hc θ × ℕ where
  toFun i:=⟨⟨i.1,i.2.2⟩,i.2.1⟩
  invFun i:=⟨i.1.1,i.2,i.1.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

def slopeStartParameter (i : SlopeStringStart a c η hc θ) : ℤ :=
  normalizedEnergy a κ i.1.val.1.val
    (stringBaseDegree a c η hc θ hχ.out i.1.val.1.val i.1.val.2 i.2)

def slopeStartRowType (i : SlopeStringStart a c η hc θ) : ℕ :=
  if Even (eulerForm a i.1.val.1.val i.1.val.1.val) then 1 else 0

lemma slopeStartEven_iff (i : GlobalStringIndex a c η hc θ) :
    globalColorSign a c η hc θ i.1.val i.1.val=1 ↔
      slopeStartRowType a c η hc θ (stringLetterStartEquiv a c η hc θ i).1≠0 := by
  rw [stringStartParity]
  dsimp only [slopeStartRowType,stringLetterStartEquiv]
  split_ifs <;> simp_all

def primitiveCountEquiv : StringPBWIndex a c η hc θ ≃
    CountSelection (fun i : SlopeStringStart a c η hc θ × ℕ=>
      slopeStartRowType a c η hc θ i.1≠0) :=
  ((stringSelectionEquiv a c η hc θ).trans
    (selectionCountEquiv _)).trans
      (countReindex (stringLetterStartEquiv a c η hc θ) _ _ (slopeStartEven_iff a c η hc θ))

def primitiveRowsEquiv : StringPBWIndex a c η hc θ ≃
    SupportedUnitRows (slopeStartRowType a c η hc θ) :=
  (primitiveCountEquiv a c η hc θ).trans (allUnitRowsEquiv _)

lemma primitiveCount_energy (w : StringPBWIndex a c η hc θ) :
    (primitiveCountEquiv a c η hc θ w).val.sum (fun i n=>
      n • (slopeStartParameter a κ c η hc θ i.1-2*(i.2:ℤ)))=
      normalizedEnergy a κ (stringPBWGrade a c η hc θ w).1.1.val
        (stringPBWGrade a c η hc θ w).2 := by
  change (countReindex _ _ _ (slopeStartEven_iff a c η hc θ) _).val.sum _=_
  rw [countReindex_sum]
  change ((stringSelectionEquiv a c η hc θ w).val).toFinsupp.sum _=_
  rw [multiset_count_sum]
  rw [stringWordEnergy]
  rfl

lemma stringWord_dimension (w : List (GlobalStringIndex a c η hc θ)) :
    (w.map (fun i=>i.1.val.1.val)).sum=
      (wordWeight c η hc θ (fun i : GlobalStringIndex a c η hc θ=>i.1.val) w).1.val := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa only [List.map_cons,List.sum_cons,wordWeight,Prod.fst_add,AddSubmonoid.coe_add] using congrArg (i.1.val.1.val+·) ih

lemma primitiveCount_dimension (w : StringPBWIndex a c η hc θ) :
    (primitiveCountEquiv a c η hc θ w).val.sum (fun i n=>n • i.1.1.val.1.val)=
      (stringPBWGrade a c η hc θ w).1.1.val := by
  change (countReindex _ _ _ (slopeStartEven_iff a c η hc θ) _).val.sum _=_
  rw [countReindex_sum]
  change ((stringSelectionEquiv a c η hc θ w).val).toFinsupp.sum _=_
  rw [multiset_count_sum]
  exact stringWord_dimension a c η hc θ w.val

theorem primitiveRows_energy (w : StringPBWIndex a c η hc θ) :
    rowsEnergy (slopeStartRowType a c η hc θ) (slopeStartParameter a κ c η hc θ)
      (primitiveRowsEquiv a c η hc θ w)=
      normalizedEnergy a κ (stringPBWGrade a c η hc θ w).1.1.val
        (stringPBWGrade a c η hc θ w).2 := by
  rw [primitiveRowsEquiv,Equiv.trans_apply,rowsEnergy_equiv]
  exact primitiveCount_energy a κ c η hc θ w

theorem primitiveRows_dimension (w : StringPBWIndex a c η hc θ) :
    rowsDimension (slopeStartRowType a c η hc θ) (fun i=>i.1.val.1.val)
      (primitiveRowsEquiv a c η hc θ w)=(stringPBWGrade a c η hc θ w).1.1.val := by
  rw [primitiveRowsEquiv,Equiv.trans_apply,rowsDimension_equiv]
  exact primitiveCount_dimension a c η hc θ w
end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable

lemma strict_fin_nat_bound {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) (i : Fin n) : i.val≤f i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      have H:=hf (Fin.castSucc_lt_succ (i := i))
      change i.val≤f i.castSucc at ih
      change i.val+1≤f i.succ
      omega

noncomputable def weakStrictListEquiv (n : ℕ) :
    {f : Fin n → ℕ // Monotone f} ≃ {f : Fin n → ℕ // StrictMono f} where
  toFun f := ⟨fun i=>f.val i+i.val,by
    intro i j hij
    have H:=f.property hij.le
    have Hij : i.val<j.val := hij
    dsimp
    omega⟩
  invFun f := ⟨fun i=>f.val i-i.val,by
    cases n with
    | zero => intros i; exact Fin.elim0 i
    | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have H:=f.property (Fin.castSucc_lt_succ (i := i))
      change f.val i.castSucc-i.val≤f.val i.succ-(i.val+1)
      omega⟩
  left_inv f := by apply Subtype.ext; funext i; dsimp; omega
  right_inv f := by
    apply Subtype.ext; funext i
    have H:=strict_fin_nat_bound f.property i
    dsimp
    omega

abbrev UnitIndexList (elementary : Bool) (n : ℕ) :=
  {f : Fin n → ℕ // if elementary then StrictMono f else Monotone f}
noncomputable def weakUnitListEquiv (elementary : Bool) (n : ℕ) :
    {f : Fin n → ℕ // Monotone f} ≃ UnitIndexList elementary n := by
  cases elementary
  · exact Equiv.refl _
  · exact weakStrictListEquiv n

lemma weakUnitListEquiv_val (elementary : Bool) (n : ℕ)
    (f : {f : Fin n → ℕ // Monotone f}) (i : Fin n) :
    (weakUnitListEquiv elementary n f).val i=f.val i+(if elementary then i.val else 0) := by
  cases elementary <;> rfl

lemma fin_staircase_sum (n : ℕ) :
    2*(∑ j : Fin n,(j.val:ℤ))=(n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    nlinarith

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ε : I → Bool) (d : I → ℕ)
abbrev InputIndexLists := ∀ i,UnitIndexList (ε i) (d i)
noncomputable def inputListEquiv : SortedPackExponent d ≃ InputIndexLists ε d :=
  Equiv.piCongrRight (fun i=>weakUnitListEquiv (ε i) (d i))

def elementaryDiagonal (i : I) : ℕ := if ε i then 0 else 1

def listIndexSum (x : InputIndexLists ε d) : ℕ := ∑ i,∑ j,(x i).val j

omit [DecidableEq I] in
lemma inputListIndexSum (x : SortedPackExponent d) :
    2*(listIndexSum ε d (inputListEquiv ε d x):ℤ)=
      2*(sortedPackDegree d x:ℤ)+
        ∑ i,((1:ℤ)-elementaryDiagonal ε i)*(d i:ℤ)*((d i:ℤ)-1) := by
  simp only [listIndexSum,inputListEquiv,Equiv.piCongrRight_apply,Pi.map,weakUnitListEquiv_val,
    sortedPackDegree,Nat.cast_sum,Nat.cast_add,Finset.sum_add_distrib,mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  cases h : ε i with
  | false => simp [h,elementaryDiagonal]
  | true => simpa [h,elementaryDiagonal] using fin_staircase_sum (d i)
end ElementaryPositivity.RawShuffle

end

end OAI
