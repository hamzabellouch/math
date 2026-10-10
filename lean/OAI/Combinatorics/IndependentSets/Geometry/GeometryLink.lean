import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.ExprTables
import OAI.Combinatorics.IndependentSets.Encoding.GeometryExpr

namespace OAI

namespace LargeIndependentSets.GeometryNames
open IndependentSetsCut.CounterMachine UniformLC ShortestPaths
open scoped Classical BigOperators
noncomputable section

variable (L R : Type) [Fintype L] [Fintype R] (n D : ℕ) [NeZero D]

def pointCost (a b : StaticPoint L R n D) : ℕ :=
  (Capped.clip D (copyCost (decode (fun _ => ()) (fun _ => ()) a)
    (decode (fun _ => ()) (fun _ => ()) b))).val

omit [NeZero D] in
lemma copyCost_same {U V : Type} [DecidableEq U] [DecidableEq V]
    (u u' : Fin n → U) (v v' : Fin n → V) (a b : StaticPoint L R n D) :
    (Capped.clip D (copyCost (decode u v a) (decode u' v' b))).val =
      if sameQuestion L R n D u u' v v' a b then pointCost L R n D a b else D+1 := by
  by_cases hq : sameQuestion L R n D u u' v v' a b
  · rw [ite_eq_left hq]
    have hh := (sameQuestion_iff L R n D u u' v v' a b).mp hq
    rcases a with ⟨i,a⟩
    rcases b with ⟨j,b⟩
    have hij : i=j := congrArg (fun w => w.1) hh
    subst j
    have hq' : mixed u v i.val=mixed u' v' i.val :=
      eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    have hcopy (q q' : MixedTuple U V n i.val) (he : q=q') :
        copyCost (M:=LayerAnswer L R) (⟨⟨i,q⟩,a⟩ : GridLocation _ D) ⟨⟨i,q'⟩,b⟩ =
          (Finset.univ.sup (fun k => circleCost (a k) (b k)) : ℕ) := by
      subst q'
      simp [copyCost]
    rw [show copyCost (decode u v ⟨i,a⟩) (decode u' v' ⟨i,b⟩)=
      (Finset.univ.sup (fun k => circleCost (a k) (b k)) : ℕ) from hcopy _ _ hq']
    simp [pointCost,copyCost,decode]
    rfl
  · have hh := (sameQuestion_iff L R n D u u' v v' a b).not.mp hq
    simp [hq,copyCost,hh]

def questionExpr (x y c : Expr) (h : Fin n) : Expr :=
  .mul (Expr.equal (uExpr L R n D x h) (fieldExpr c 0))
    (.mul (Expr.equal (vExpr L R n D y h) (fieldExpr c 1))
      (Expr.listAll (List.finRange n) (fun k => if k=h then .const 1 else
        if k.val<h.val then Expr.equal (vExpr L R n D x k) (vExpr L R n D y k)
        else Expr.equal (uExpr L R n D x k) (uExpr L R n D y k))))

lemma questionExpr_nonzero (t : Table L R) (x y c : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (e : Fin t.ne)
    (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) (he : c.eval t.bits a=e.val) (h : Fin n) :
    (questionExpr L R n D x y c h).eval t.bits a≠0 ↔
      QuestionStep t.lc h e ((nodeEquiv L R n D t.nu t.nv).symm i).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm i).1.2
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.2 := by
  simp only [questionExpr,Expr.eval,Expr.equal_eval,Expr.listAll_eval,
    uExpr_eval L R n D t x a i hi,vExpr_eval L R n D t y a j hj,
    fieldExpr_eval t a c e he ⟨0,by omega⟩,fieldExpr_eval t a c e he ⟨1,by omega⟩]
  have indicator (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)≠0 ↔ P := by
    split_ifs <;> simp_all
  simp only [↓reduceIte,Nat.one_ne_zero,mul_ne_zero_iff,indicator,Fin.val_inj]
  unfold QuestionStep Table.lc
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  simp only [List.mem_finRange,forall_true_left]
  apply forall_congr'
  intro k
  by_cases hk : k=h
  · simp [hk,Expr.eval]
  · by_cases hl : k.val<h.val <;> simp [hk,hl,Expr.equal_eval,
      uExpr_eval L R n D t x a i hi,uExpr_eval L R n D t y a j hj,
      vExpr_eval L R n D t x a i hi,vExpr_eval L R n D t y a j hj,Fin.val_inj]

def pointStepExpr (x y c : Expr) (h : Fin n) : Expr :=
  Expr.static3 (fun (a b : StaticPoint L R n D) (f : L → R) => if PointStep h f a b then 1 else 0)
    (pointExpr L R n D x) (pointExpr L R n D y) (fieldExpr c 2)

lemma pointStepExpr_eval (t : Table L R) (x y c : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (e : Fin t.ne)
    (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) (he : c.eval t.bits a=e.val) (h : Fin n) :
    (pointStepExpr L R n D x y c h).eval t.bits a =
      if PointStep h (t.project e) ((nodeEquiv L R n D t.nu t.nv).symm i).2
        ((nodeEquiv L R n D t.nu t.nv).symm j).2 then 1 else 0 := by
  apply Expr.static3_eval
  · exact pointExpr_eval L R n D t x a i hi
  · exact pointExpr_eval L R n D t y a j hj
  · exact fieldExpr_eval t a c e he ⟨2,by omega⟩

def forwardExpr (x y : Expr) : Expr :=
  .sum neExpr (Expr.listSum (List.finRange n) (fun h =>
    .mul (pointStepExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)
      (questionExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)))

lemma forwardExpr_nonzero (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (forwardExpr L R n D x y).eval t.bits a≠0 ↔
      (layeredSystem t.lc n).ForwardZero D (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j) := by
  dsimp only [names,nodeDecode]
  rw [forward_iff]
  change _ ↔ ∃ h e, PointStep h (t.project e) ((nodeEquiv L R n D t.nu t.nv).symm i).2
    ((nodeEquiv L R n D t.nu t.nv).symm j).2 ∧ QuestionStep t.lc h e _ _ _ _
  simp only [forwardExpr,Expr.sum_ne_zero,neExpr_eval,Expr.listSum_ne_zero,List.mem_finRange,true_and]
  have each (c : ℕ) (hc : c<t.ne) (h : Fin n) :
      (Expr.mul (pointStepExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)
        (questionExpr L R n D (x.rename Nat.succ) (y.rename Nat.succ) (.arg 0) h)).eval
        t.bits (Expr.bind a c)≠0 ↔
      PointStep h (t.project ⟨c,hc⟩) ((nodeEquiv L R n D t.nu t.nv).symm i).2
        ((nodeEquiv L R n D t.nu t.nv).symm j).2 ∧ QuestionStep t.lc h ⟨c,hc⟩
          ((nodeEquiv L R n D t.nu t.nv).symm i).1.1
          ((nodeEquiv L R n D t.nu t.nv).symm j).1.1
          ((nodeEquiv L R n D t.nu t.nv).symm i).1.2
          ((nodeEquiv L R n D t.nu t.nv).symm j).1.2 := by
    have hx : (x.rename Nat.succ).eval t.bits (Expr.bind a c)=i.val := by simpa [Expr.bind] using hi
    have hy : (y.rename Nat.succ).eval t.bits (Expr.bind a c)=j.val := by simpa [Expr.bind] using hj
    rw [Expr.eval,mul_ne_zero_iff,pointStepExpr_eval L R n D t _ _ _ _ i j ⟨c,hc⟩ hx hy rfl h,
      questionExpr_nonzero L R n D t _ _ _ _ i j ⟨c,hc⟩ hx hy rfl h]
    split_ifs <;> simp_all
  constructor
  · rintro ⟨c,hc,h,hh⟩; exact ⟨h,⟨c,hc⟩,(each c hc h).mp hh⟩
  · rintro ⟨h,e,hh⟩; exact ⟨e.val,e.isLt,h,(each e.val e.isLt h).mpr hh⟩

def levelExpr (x : Expr) : Expr :=
  Expr.staticLookup (fun a : StaticPoint L R n D => a.1.val) (pointExpr L R n D x)

lemma levelExpr_eval (t : Table L R) (x : Expr) (a : ℕ → ℕ) (i : Fin (size L R n D t))
    (hi : x.eval t.bits a=i.val) :
    (levelExpr L R n D x).eval t.bits a=((nodeEquiv L R n D t.nu t.nv).symm i).2.1.val := by
  exact Expr.staticLookup_eval _ _ _ _ _ (pointExpr_eval L R n D t x a i hi)

def sameQuestionExpr (x y : Expr) : Expr :=
  .mul (Expr.equal (levelExpr L R n D x) (levelExpr L R n D y))
    (Expr.listAll (List.finRange n) (fun k =>
      Expr.cond (Expr.lt (.const k.val) (levelExpr L R n D x))
        (Expr.equal (vExpr L R n D x k) (vExpr L R n D y k))
        (Expr.equal (uExpr L R n D x k) (uExpr L R n D y k))))

lemma sameQuestionExpr_nonzero (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (sameQuestionExpr L R n D x y).eval t.bits a≠0 ↔
      sameQuestion L R n D ((nodeEquiv L R n D t.nu t.nv).symm i).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.1
        ((nodeEquiv L R n D t.nu t.nv).symm i).1.2
        ((nodeEquiv L R n D t.nu t.nv).symm j).1.2
        ((nodeEquiv L R n D t.nu t.nv).symm i).2
        ((nodeEquiv L R n D t.nu t.nv).symm j).2 := by
  have indicator (P : Prop) [Decidable P] : (if P then (1:ℕ) else 0)≠0 ↔ P := by
    split_ifs <;> simp_all
  simp only [sameQuestionExpr,Expr.eval,mul_ne_zero_iff,Expr.equal_eval,Expr.listAll_eval,
    levelExpr_eval L R n D t x a i hi,levelExpr_eval L R n D t y a j hj,
    indicator,Fin.val_inj,List.mem_finRange,forall_true_left,sameQuestion]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro k
  simp only [Expr.cond_eval,Expr.lt_eval,Expr.eval,levelExpr_eval L R n D t x a i hi,
    indicator,Expr.equal_eval,vExpr_eval L R n D t x a i hi,vExpr_eval L R n D t y a j hj,
    uExpr_eval L R n D t x a i hi,uExpr_eval L R n D t y a j hj]
  split_ifs <;> simp_all [Fin.val_inj]

def copyCostExpr (x y : Expr) : Expr :=
  Expr.cond (sameQuestionExpr L R n D x y)
    (Expr.static2 (pointCost L R n D) (pointExpr L R n D x) (pointExpr L R n D y))
    (.const (D+1))

lemma copyCostExpr_eval (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (copyCostExpr L R n D x y).eval t.bits a=
      (Capped.clip D (copyCost (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j))).val := by
  dsimp only [names,nodeDecode]
  rw [copyCost_same]
  simp only [copyCostExpr,Expr.cond_eval,sameQuestionExpr_nonzero L R n D t x y a i j hi hj,
    Expr.static2_eval _ _ _ _ _ _ _ (pointExpr_eval L R n D t x a i hi)
      (pointExpr_eval L R n D t y a j hj),Expr.eval]

def costExpr (x y : Expr) : Expr :=
  Expr.cond (.add (forwardExpr L R n D x y) (forwardExpr L R n D y x))
    (.const 0) (copyCostExpr L R n D x y)

lemma costExpr_eval (t : Table L R) (x y : Expr) (a : ℕ → ℕ)
    (i j : Fin (size L R n D t)) (hi : x.eval t.bits a=i.val) (hj : y.eval t.bits a=j.val) :
    (costExpr L R n D x y).eval t.bits a=
      (Capped.clip D (linkCost (layeredSystem t.lc n)
        (names L R n D t.nu t.nv i) (names L R n D t.nu t.nv j))).val := by
  have add_ne (a b : ℕ) : a+b≠0 ↔ a≠0 ∨ b≠0 := by omega
  simp only [costExpr,Expr.cond_eval,Expr.eval,add_ne,
    forwardExpr_nonzero L R n D t x y a i j hi hj,
    forwardExpr_nonzero L R n D t y x a j i hj hi,
    copyCostExpr_eval L R n D t x y a i j hi hj,linkCost,ProjectionSystem.ZeroLink]
  split_ifs <;> simp_all [Capped.clip]

end
end LargeIndependentSets.GeometryNames

end OAI
