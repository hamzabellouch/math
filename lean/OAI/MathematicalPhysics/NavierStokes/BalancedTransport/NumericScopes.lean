import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericEvaluation

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp

def Scoped (o : NumericOp) (n : ℕ) : Prop :=
  let a := o.left
  let b := o.right
  match o.tag with
  | 0 => True
  | 1 => True
  | 2 => a < n ∧ b < n
  | 3 => a < n ∧ b < n
  | 4 => a < n
  | 5 => a < n
  | 6 => b < n
  | 7 => a < n
  | 8 => True

lemma real_append (d : ℕ) [NeZero d] (o : NumericOp) (x : Fin d → ℝ)
    (s q : List ℝ) (hs : o.Scoped s.length) : o.real d x (s ++ q) = o.real d x s := by
  have he (i : ℕ) (hi : i < s.length) : (s ++ q).getD i 0 = s.getD i 0 := by
    simp [List.getD, List.getElem?_append_left hi]
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> simp only [Scoped, real, tag, rat, left, right] at hs ⊢
  all_goals first | rfl | exact he _ hs | simp only [he _ hs] | simp only [he _ hs.1, he _ hs.2]

lemma valid_append (o : NumericOp) (s q : List ℝ) (hs : o.Scoped s.length) :
    o.Valid (s ++ q) ↔ o.Valid s := by
  by_cases ht : o.tag = 5
  · have hh : o.left < s.length := by unfold Scoped at hs; rw [ht] at hs; exact hs
    simp only [Valid, ht, forall_const]
    simp only [List.getD, List.getElem?_append_left hh]
  · simp [Valid, ht]

end BalancedTransport.Effectivity.NumericOp
end

noncomputable section
namespace BalancedTransport.Effectivity.NumericProgram
variable {d : ℕ} [NeZero d]

def ScopedFrom : NumericProgram → ℕ → Prop
  | [], _ => True
  | o::p, n => o.Scoped n ∧ ScopedFrom p (n+1)

def Closed (p : NumericProgram) : Prop := p.ScopedFrom 0

lemma realFrom_length (p : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (realFrom p x s).length = p.length + s.length := by
  induction p generalizing s with
  | nil => simp [realFrom]
  | cons o p ih => simpa [realFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (o.real d x s :: s)

lemma realFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : realFrom p x (s ++ q) = realFrom p x s ++ q := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change realFrom p x (o.real d x (s ++ q) :: (s ++ q)) =
      realFrom p x (o.real d x s :: s) ++ q
    rw [o.real_append d x s q hs.1]
    exact ih (o.real d x s :: s) hs.2

lemma validFrom_append (p : NumericProgram) (x : Fin d → ℝ) (s q : List ℝ)
    (hs : p.ScopedFrom s.length) : ValidFrom x p (s ++ q) ↔ ValidFrom x p s := by
  induction p generalizing s with
  | nil => rfl
  | cons o p ih =>
    change o.Valid (s ++ q) ∧ ValidFrom x p (o.real d x (s ++ q) :: (s ++ q)) ↔
      o.Valid s ∧ ValidFrom x p (o.real d x s :: s)
    rw [o.valid_append s q hs.1, o.real_append d x s q hs.1]
    exact and_congr_right (fun _ => ih (o.real d x s :: s) hs.2)

lemma realFrom_empty_append (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    realFrom p x s = realFrom p x [] ++ s :=
  realFrom_append p x [] s hp

lemma validFrom_of_closed (p : NumericProgram) (hp : p.Closed) (x : Fin d → ℝ) (s : List ℝ) :
    ValidFrom x p s ↔ p.Valid x := p.validFrom_append x [] s hp

lemma realFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).realFrom x s = q.realFrom x (realFrom p x s) := List.foldl_append

lemma validFrom_concat (p q : NumericProgram) (x : Fin d → ℝ) (s : List ℝ) :
    (p ++ q).ValidFrom x s ↔ ValidFrom x p s ∧ q.ValidFrom x (realFrom p x s) := by
  induction p generalizing s with
  | nil => simp [ValidFrom, realFrom]
  | cons o p ih => simpa only [List.cons_append, ValidFrom, realFrom,
      List.foldl_cons, and_assoc] using and_congr_right (fun _ => ih _)

lemma scopedFrom_mono (p : NumericProgram) {n m : ℕ} (hnm : n ≤ m) :
    p.ScopedFrom n → p.ScopedFrom m := by
  intro h
  induction p generalizing n m with
  | nil => trivial
  | cons o p ih =>
    refine ⟨?_, ih (Nat.add_le_add_right hnm 1) h.2⟩
    rcases o with ⟨j,r,a,b⟩
    have ho := h.1
    fin_cases j <;> dsimp only [NumericOp.Scoped, NumericOp.tag, NumericOp.rat,
      NumericOp.left, NumericOp.right] at ho ⊢
    all_goals first | trivial | exact ho.trans_le hnm | exact ⟨ho.1.trans_le hnm,ho.2.trans_le hnm⟩

lemma scopedFrom_concat (p q : NumericProgram) (n : ℕ) :
    (p ++ q).ScopedFrom n ↔ p.ScopedFrom n ∧ q.ScopedFrom (n+p.length) := by
  induction p generalizing n with
  | nil => simp [ScopedFrom]
  | cons o p ih =>
    simp only [List.cons_append, ScopedFrom, List.length_cons]
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1, and_assoc]

end BalancedTransport.Effectivity.NumericProgram
end

end OAI
