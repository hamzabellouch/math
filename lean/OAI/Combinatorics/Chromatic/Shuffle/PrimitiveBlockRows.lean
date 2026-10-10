import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.CompleteUnit
import OAI.Combinatorics.Chromatic.Walls.FiniteReorderingEnergy

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic UnitSelections
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance blockRowsFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

def blockWordEquiv (d : I → ℕ) : StringBlockIndex a c η hc d ≃
    {w : StringPBWIndex a c η hc (slope c η d) //
      (stringPBWGrade a c η hc (slope c η d) w).1.1.val=d} where
  toFun i:=⟨i.2.2.val,congrArg (fun g : SlopeWeight c η hc (slope c η d) × ℤ=>g.1.1.val) i.2.2.property⟩
  invFun w:=⟨(stringPBWGrade a c η hc (slope c η d) w.val).2,
    (stringPBWGrade a c η hc (slope c η d) w.val).1.2,⟨w.val,by
      apply Prod.ext
      · apply Prod.ext
        · exact Subtype.ext w.property
        · rfl
      · rfl⟩⟩
  left_inv i:=by
    rcases i with ⟨k,W,w,hw⟩
    dsimp only
    have hk := congrArg Prod.snd hw
    have hW := congrArg (fun g : SlopeWeight c η hc (slope c η d) × ℤ => g.1.2) hw
    dsimp only at hk hW
    subst k
    subst W
    rfl
  right_inv _:=rfl

abbrev BlockRows (d : I → ℕ) :=
  {r : SupportedUnitRows (slopeStartRowType a c η hc (slope c η d)) //
    rowsDimension (slopeStartRowType a c η hc (slope c η d))
      (fun i=>i.1.val.1.val) r=d}

def blockRowsEquiv (d : I → ℕ) : StringBlockIndex a c η hc d ≃ BlockRows a c η hc d :=
  (blockWordEquiv a c η hc d).trans
    ((primitiveRowsEquiv a c η hc (slope c η d)).subtypeEquiv (fun w=>by
      rw [primitiveRows_dimension]))

def blockRowsEnergy (d : I → ℕ) (r : BlockRows a c η hc d) : ℤ :=
  rowsEnergy (slopeStartRowType a c η hc (slope c η d))
    (slopeStartParameter a κ c η hc (slope c η d)) r.val

lemma blockRowsEquiv_energy (d : I → ℕ) (w : StringBlockIndex a c η hc d) :
    blockRowsEnergy a κ c η hc d (blockRowsEquiv a c η hc d w)=
      stringBlockEnergy a κ c η hc d w := by
  change rowsEnergy _ _ (primitiveRowsEquiv a c η hc (slope c η d) w.2.2.val)=_
  rw [primitiveRows_energy,w.2.2.property,stringBlockEnergy_normalized]

def HNRowsIndex : List (I → ℕ) → Type u
  | []=>ULift.{u} Unit
  | d::l=>BlockRows a c η hc d × HNRowsIndex l

def hnRowsEquiv : (l : List (I → ℕ)) → HNStringIndex a c η hc l ≃ HNRowsIndex a c η hc l
  | []=>Equiv.refl _
  | d::l=>Equiv.prodCongr (blockRowsEquiv a c η hc d) (hnRowsEquiv l)

def hnRowsEnergy : (l : List (I → ℕ)) → HNRowsIndex a c η hc l → ℤ
  | [],_=>0
  | d::l,r=>blockRowsEnergy a κ c η hc d r.1+hnRowsEnergy l r.2+
      (eulerForm a d l.sum-eulerForm a l.sum d)

lemma hnRowsEquiv_energy (l : List (I → ℕ)) (w : HNStringIndex a c η hc l) :
    hnRowsEnergy a κ c η hc l (hnRowsEquiv a c η hc l w)=hnStringEnergy a κ c η hc l w := by
  induction l with
  | nil=>rfl
  | cons d l ih=>
    change blockRowsEnergy a κ c η hc d (blockRowsEquiv a c η hc d w.1)+
      hnRowsEnergy a κ c η hc l (hnRowsEquiv a c η hc l w.2)+_=_
    rw [blockRowsEquiv_energy,ih]
    rfl

def outputRowsEquiv (d : I → ℕ) :
    (Σ l : HNIndex c η d,HNStringIndex a c η hc l.val) ≃
      Σ l : HNIndex c η d,HNRowsIndex a c η hc l.val :=
  Equiv.sigmaCongrRight (fun l=>hnRowsEquiv a c η hc l.val)

lemma outputRows_admissible (d : I → ℕ) : EnergyLaurent.Admissible
    (fun r : Σ l : HNIndex c η d,HNRowsIndex a c η hc l.val=>hnRowsEnergy a κ c η hc r.1.val r.2) :=
  EnergyLaurent.admissible_equiv (outputEnergy_admissible a κ c η hc d)
    (outputRowsEquiv a c η hc d) (fun w=>hnRowsEquiv_energy a κ c η hc w.1.val w.2)

def outputRowsSeries (d : I → ℕ) : LaurentSeries ℚ := EnergyLaurent.series _
  (outputRows_admissible a κ c η hc d)

theorem finiteReordering_rows (ε : I → Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    inputReorderingSeries a κ ε ha d=outputRowsSeries a κ c η hc d := by
  rw [finiteReordering_laurent a κ c η hc ε ha]
  exact EnergyLaurent.series_equiv _ _ (outputRowsEquiv a c η hc d)
    (fun w=>hnRowsEquiv_energy a κ c η hc w.1.val w.2)
end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀i,0<c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance decoratedFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

abbrev RowBlock := Σ d : I → ℕ,BlockRows a c η hc d

def rowsDecorate : (l : List (I → ℕ)) → HNRowsIndex a c η hc l → List (RowBlock a c η hc)
  | [],_=>[]
  | d::l,r=>⟨d,r.1⟩::rowsDecorate l r.2

@[simp] lemma rowsDecorate_dim (l : List (I → ℕ)) (r : HNRowsIndex a c η hc l) :
    (rowsDecorate a c η hc l r).map Sigma.fst=l := by
  induction l with
  | nil=>rfl
  | cons d l ih=>simpa only [rowsDecorate,List.map_cons] using congrArg (List.cons d) (ih r.2)

def rowsUndecorate : (l : List (RowBlock a c η hc)) → HNRowsIndex a c η hc (l.map Sigma.fst)
  | []=>⟨()⟩
  | b::l=>(b.2,rowsUndecorate l)

@[simp] lemma rowsDecorate_undecorate (l : List (RowBlock a c η hc)) :
    rowsDecorate a c η hc (l.map Sigma.fst) (rowsUndecorate a c η hc l)=l := by
  induction l with
  | nil=>rfl
  | cons b l ih=>
    change b::rowsDecorate a c η hc (l.map Sigma.fst) (rowsUndecorate a c η hc l)=b::l
    rw [ih]

lemma rowsDecorate_injective (l : List (I → ℕ)) :
    Function.Injective (rowsDecorate a c η hc l) := by
  induction l with
  | nil=>intro x y _; exact @Subsingleton.elim (ULift Unit) inferInstance x y
  | cons d l ih=>
    intro x y H
    simp only [rowsDecorate,List.cons.injEq] at H
    apply Prod.ext
    · exact eq_of_heq (Sigma.mk.inj H.1).2
    · exact ih H.2

def rowsCons (d : I → ℕ) (r : BlockRows a c η hc d)
    (x : Σ l : List (I → ℕ),HNRowsIndex a c η hc l) :
    Σ l : List (I → ℕ),HNRowsIndex a c η hc l := ⟨d::x.1,(r,x.2)⟩

lemma rowsUndecorate_decorate (l : List (I → ℕ)) (r : HNRowsIndex a c η hc l) :
    (⟨(rowsDecorate a c η hc l r).map Sigma.fst,
      rowsUndecorate a c η hc (rowsDecorate a c η hc l r)⟩ :
      Σ l : List (I → ℕ),HNRowsIndex a c η hc l)=⟨l,r⟩ := by
  induction l with
  | nil=>
    have H : r=(⟨()⟩ : ULift Unit) := @Subsingleton.elim (ULift Unit) inferInstance r ⟨()⟩
    cases H
    rfl
  | cons d l ih=>exact congrArg (rowsCons a c η hc d r.1) (ih r.2)

abbrev DecoratedHN (d : I → ℕ) :=
  {l : List (RowBlock a c η hc) // (l.map Sigma.fst).sum=d ∧ HNOrdered c η (l.map Sigma.fst)}

def decorateOutput (d : I → ℕ) :
    (Σ l : HNIndex c η d,HNRowsIndex a c η hc l.val) ≃ DecoratedHN a c η hc d where
  toFun x:=⟨rowsDecorate a c η hc x.1.val x.2,by simpa only [rowsDecorate_dim] using x.1.property⟩
  invFun l:=⟨⟨l.val.map Sigma.fst,l.property⟩,rowsUndecorate a c η hc l.val⟩
  left_inv x:=by
    have H:=rowsUndecorate_decorate a c η hc x.1.val x.2
    exact Sigma.ext (Subtype.ext (Sigma.mk.inj H).1) (Sigma.mk.inj H).2
  right_inv l:=Subtype.ext (rowsDecorate_undecorate a c η hc l.val)

def decoratedDimension (l : List (RowBlock a c η hc)) : I → ℕ := (l.map Sigma.fst).sum

def decoratedEnergy : List (RowBlock a c η hc) → ℤ
  | []=>0
  | b::l=>blockRowsEnergy a κ c η hc b.1 b.2+decoratedEnergy l+
    (eulerForm a b.1 (decoratedDimension a c η hc l)-eulerForm a (decoratedDimension a c η hc l) b.1)

lemma decoratedEnergy_rows (l : List (I → ℕ)) (r : HNRowsIndex a c η hc l) :
    decoratedEnergy a κ c η hc (rowsDecorate a c η hc l r)=hnRowsEnergy a κ c η hc l r := by
  induction l with
  | nil=>rfl
  | cons d l ih=>
    simp only [rowsDecorate,decoratedEnergy,decoratedDimension,rowsDecorate_dim,ih,hnRowsEnergy]

lemma decoratedDimension_append (l r : List (RowBlock a c η hc)) :
    decoratedDimension a c η hc (l++r)=decoratedDimension a c η hc l+decoratedDimension a c η hc r := by
  simp [decoratedDimension]

lemma decoratedEnergy_append (l r : List (RowBlock a c η hc)) :
    decoratedEnergy a κ c η hc (l++r)=
      decoratedEnergy a κ c η hc l+decoratedEnergy a κ c η hc r+
        (eulerForm a (decoratedDimension a c η hc l) (decoratedDimension a c η hc r)-
          eulerForm a (decoratedDimension a c η hc r) (decoratedDimension a c η hc l)) := by
  induction l with
  | nil=>simp [decoratedEnergy,decoratedDimension,eulerForm]
  | cons b l ih=>
    simp only [List.cons_append,decoratedEnergy,ih,
      decoratedDimension,List.map_cons,List.sum_cons,List.map_append,List.sum_append,eulerForm_add_left,eulerForm_add_right]
    ring

lemma decoratedEnergy_admissible (d : I → ℕ) :
    EnergyLaurent.Admissible (fun l : DecoratedHN a c η hc d=>decoratedEnergy a κ c η hc l.val) :=
  EnergyLaurent.admissible_equiv (outputRows_admissible a κ c η hc d)
    (decorateOutput a c η hc d) (fun l=>decoratedEnergy_rows a κ c η hc l.1.val l.2)

end
end ElementaryPositivity.RawShuffle

end

end OAI
