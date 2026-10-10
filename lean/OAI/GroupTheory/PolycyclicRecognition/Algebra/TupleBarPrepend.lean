import OAI.GroupTheory.PolycyclicRecognition.Algebra.ListBarCoordinates
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-! # Head insertion and contraction in finite-tuple bar coordinates -/

noncomputable section
namespace PolycyclicRecognition
variable {A : Type}

theorem contractNth_cons_zero (op : A → A → A) (a : A) {n : ℕ} (v : Fin (n + 1) → A) :
    Fin.contractNth 0 op (Fin.cons a v) = Fin.cons (op a (v 0)) (fun i => v i.succ) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [Fin.contractNth]
  · simp [Fin.contractNth]

theorem contractNth_cons_succ (op : A → A → A) (a : A) {n : ℕ}
    (v : Fin (n + 1) → A) (j : Fin (n + 1)) :
    Fin.contractNth j.succ op (Fin.cons a v) = Fin.cons a (Fin.contractNth j op v) := by
  funext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [Fin.contractNth]
  · simp [Fin.contractNth]

def tupleBarPrepend (n : ℕ) (a : A) :
    ((Fin n → A) →₀ ℤ) →ₗ[ℤ] ((Fin (n + 1) → A) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun v : Fin n → A => Fin.cons a v)

@[simp] theorem tupleBarPrepend_single (n : ℕ) (a : A) (v : Fin n → A) (z : ℤ) :
    tupleBarPrepend n a (Finsupp.single v z) = Finsupp.single (Fin.cons a v) z := by
  simp [tupleBarPrepend]

theorem tupleBarToList_prepend (n : ℕ) (a : A) (z : (Fin n → A) →₀ ℤ) :
    tupleBarToList (n + 1) (tupleBarPrepend n a z) = listBarPrepend a (tupleBarToList n z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v c => simp

end PolycyclicRecognition

end

end OAI
