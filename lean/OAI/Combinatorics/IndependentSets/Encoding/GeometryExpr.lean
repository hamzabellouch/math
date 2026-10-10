import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LCTable
import OAI.Combinatorics.IndependentSets.Geometry.GeometryNaming

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC
open scoped Classical BigOperators
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

abbrev staticCount := Fintype.card (StaticPoint L R n D)
abbrev size (t : Table L R) := (t.nu^n*t.nv^n)*staticCount L R n D

lemma staticCount_pos : 0<staticCount L R n D := by
  let : Nonempty (StaticPoint L R n D) := ⟨⟨⟨0,by omega⟩,fun _ => 0⟩⟩
  exact Fintype.card_pos
lemma size_pos (t : Table L R) : 0<size L R n D t := by
  exact Nat.mul_pos (Nat.mul_pos (pow_pos t.hu _) (pow_pos t.hv _)) (staticCount_pos L R n D)

def sizeExpr : Expr := .mul (.mul (Expr.power nuExpr n) (Expr.power nvExpr n)) (.const (staticCount L R n D))
def pointExpr (x : Expr) : Expr := Expr.remainder x (.const (staticCount L R n D))
def uExpr (x : Expr) (k : Fin n) : Expr :=
  Expr.remainder (Expr.quotient
    (Expr.quotient (Expr.quotient x (.const (staticCount L R n D))) (Expr.power nvExpr n))
    (Expr.power nuExpr k.val)) nuExpr

def vExpr (x : Expr) (k : Fin n) : Expr :=
  Expr.remainder (Expr.quotient
    (Expr.remainder (Expr.quotient x (.const (staticCount L R n D))) (Expr.power nvExpr n))
    (Expr.power nvExpr k.val)) nvExpr

@[simp] lemma sizeExpr_eval (t : Table L R) (a : ℕ → ℕ) :
    (sizeExpr L R n D).eval t.bits a=size L R n D t := by simp [sizeExpr,Expr.eval,size]

lemma uExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) (k : Fin n) :
    (uExpr L R n D x k).eval t.bits a=(((nodeEquiv L R n D t.nu t.nv).symm i).1.1 k).val := by
  simp only [uExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,nuExpr_eval,nvExpr_eval,Expr.eval,hi]
  rfl
lemma vExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) (k : Fin n) :
    (vExpr L R n D x k).eval t.bits a=(((nodeEquiv L R n D t.nu t.nv).symm i).1.2 k).val := by
  simp only [vExpr,Expr.remainder_eval,Expr.quotient_eval,Expr.power_eval,nvExpr_eval,Expr.eval,hi]
  rfl
lemma pointExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (pointExpr L R n D x).eval t.bits a=
      (Fintype.equivFin (StaticPoint L R n D) ((nodeEquiv L R n D t.nu t.nv).symm i).2).val := by
  simp only [pointExpr,Expr.remainder_eval,Expr.eval,hi]
  change _=(Fintype.equivFin _ ((Fintype.equivFin _).symm _)).val
  rw [Equiv.apply_symm_apply]
  rfl

def sameQuestion {U V : Type} (u u' : Fin n → U) (v v' : Fin n → V)
    (a b : StaticPoint L R n D) : Prop :=
  a.1=b.1 ∧ ∀ k, if k.val<a.1.val then v k=v' k else u k=u' k

omit [Fintype L] [Fintype R] [NeZero D] in
lemma sameQuestion_iff {U V : Type} (u u' : Fin n → U) (v v' : Fin n → V)
    (a b : StaticPoint L R n D) :
    sameQuestion L R n D u u' v v' a b ↔ (decode u v a).1=(decode u' v' b).1 := by
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  simp only [sameQuestion,decode]
  constructor
  · rintro ⟨rfl,h⟩
    congr 1
    apply Subtype.ext
    funext k
    have hk := h k
    by_cases hl : k.val < i.val <;> simpa [mixed_val,hl] using hk
  · intro h
    have hij : i=j := congrArg Sigma.fst h
    subst j
    refine ⟨rfl,?_⟩
    have hq : mixed u v i.val=mixed u' v' i.val := Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
    intro k
    have hh := congrFun (congrArg Subtype.val hq) k
    by_cases hl : k.val < i.val <;> simpa [mixed_val,hl] using hh

end
end LargeIndependentSets.GeometryNames

end OAI
