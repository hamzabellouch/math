import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LCTable

namespace OAI

namespace IndependentSetsCut.CounterMachine.Expr

section
open scoped BigOperators

def finTable2 {m n : ℕ} (f : Fin m → Fin n → ℕ) (x y : Expr) : Expr :=
  finLookup (fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (.add y (.mul (.const n) x))
lemma finTable2_eval {m n : ℕ} (f : Fin m → Fin n → ℕ) (x y : Expr) (s : List Bool)
    (a : ℕ → ℕ) (i : Fin m) (j : Fin n) (hi : x.eval s a=i.val) (hj : y.eval s a=j.val) :
    (finTable2 f x y).eval s a=f i j := by
  unfold finTable2
  rw [finLookup_eval _ _ _ _ (finProdFinEquiv (i,j)) (by simp [eval,hi,hj])]
  rw [Equiv.symm_apply_apply]

def finTable3 {l m n : ℕ} (f : Fin l → Fin m → Fin n → ℕ) (x y z : Expr) : Expr :=
  finTable2 (fun k => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (.add y (.mul (.const m) x)) z
lemma finTable3_eval {l m n : ℕ} (f : Fin l → Fin m → Fin n → ℕ) (x y z : Expr) (s : List Bool)
    (a : ℕ → ℕ) (i : Fin l) (j : Fin m) (k : Fin n)
    (hi : x.eval s a=i.val) (hj : y.eval s a=j.val) (hk : z.eval s a=k.val) :
    (finTable3 f x y z).eval s a=f i j k := by
  unfold finTable3
  rw [finTable2_eval _ _ _ _ _ (finProdFinEquiv (i,j)) k (by simp [eval,hi,hj]) hk]
  rw [Equiv.symm_apply_apply]

noncomputable def static2 {α β : Type} [Fintype α] [Fintype β]
    (f : α → β → ℕ) (x y : Expr) : Expr :=
  finTable2 (fun i j => f ((Fintype.equivFin α).symm i) ((Fintype.equivFin β).symm j)) x y
lemma static2_eval {α β : Type} [Fintype α] [Fintype β]
    (f : α → β → ℕ) (x y : Expr) (s : List Bool) (a : ℕ → ℕ) (i : α) (j : β)
    (hi : x.eval s a=(Fintype.equivFin α i).val) (hj : y.eval s a=(Fintype.equivFin β j).val) :
    (static2 f x y).eval s a=f i j := by
  rw [static2,finTable2_eval _ _ _ _ _ _ _ hi hj]
  simp

noncomputable def static3 {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℕ) (x y z : Expr) : Expr :=
  finTable3 (fun i j k => f ((Fintype.equivFin α).symm i) ((Fintype.equivFin β).symm j)
    ((Fintype.equivFin γ).symm k)) x y z
lemma static3_eval {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℕ) (x y z : Expr) (s : List Bool) (a : ℕ → ℕ) (i : α) (j : β) (k : γ)
    (hi : x.eval s a=(Fintype.equivFin α i).val) (hj : y.eval s a=(Fintype.equivFin β j).val)
    (hk : z.eval s a=(Fintype.equivFin γ k).val) :
    (static3 f x y z).eval s a=f i j k := by
  rw [static3,finTable3_eval _ _ _ _ _ _ _ _ _ hi hj hk]
  simp

lemma sum_ne_zero (bound body : Expr) (s : List Bool) (a : ℕ → ℕ) :
    (Expr.sum bound body).eval s a≠0 ↔
      ∃ i<bound.eval s a, body.eval s (bind a i)≠0 := by
  simp only [eval,ne_eq,Finset.sum_eq_zero_iff,Finset.mem_range]
  push Not
  rfl

lemma listSum_ne_zero {α : Type} (xs : List α) (f : α → Expr) (s : List Bool) (a : ℕ → ℕ) :
    (listSum xs f).eval s a≠0 ↔ ∃ x ∈ xs, (f x).eval s a≠0 := by
  rw [listSum_eval]
  simp only [ne_eq,List.sum_eq_zero_iff,List.mem_map,forall_exists_index,and_imp]
  push Not
  simp

end
open scoped Classical BigOperators
noncomputable section

def pick {α : Type} [Fintype α] (f : α → ℕ) (pred : α → Expr) : Expr :=
  listSum (List.finRange (Fintype.card α)) fun i =>
    .mul (positive (pred ((Fintype.equivFin α).symm i))) (.const (f ((Fintype.equivFin α).symm i)))

lemma pick_eval {α : Type} [Fintype α] (f : α → ℕ) (pred : α → Expr)
    (s : List Bool) (a : ℕ → ℕ) (v : α)
    (hv : ∀ x, (pred x).eval s a ≠ 0 ↔ x=v) :
    (pick f pred).eval s a=f v := by
  have hp : ∀ x, (positive (pred x)).eval s a=if x=v then 1 else 0 := by
    intro x
    rw [positive_eval]
    by_cases h : x=v
    · simp [h,(hv v).mpr rfl]
    · have hz : (pred x).eval s a=0 := by by_contra hh; exact h ((hv x).mp hh)
      simp [h,hz]
  simp only [pick,listSum_eval,eval,hp,ite_mul,one_mul,zero_mul]
  rw [← List.ofFn_eq_map,List.sum_ofFn]
  have he : ∀ i : Fin (Fintype.card α), (Fintype.equivFin α).symm i=v ↔ i=Fintype.equivFin α v := by
    intro i
    exact Equiv.symm_apply_eq (Fintype.equivFin α)
  simp only [he]
  simp

end
end IndependentSetsCut.CounterMachine.Expr

end OAI
