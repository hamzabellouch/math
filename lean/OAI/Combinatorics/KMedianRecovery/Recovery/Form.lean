import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Row

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

structure Form (V : Type*) where
  constant : ℚ
  coeff : V → ℚ

namespace Form
variable {V I : Type*} [Fintype V]

def eval (f : Form V) (x : V → ℚ) : ℚ := f.constant+∑ v, f.coeff v*x v
noncomputable def realEval (f : Form V) (x : V → ℝ) : ℝ :=
  (f.constant:ℝ)+∑ v, (f.coeff v:ℝ)*x v

def const (c : ℚ) : Form V := ⟨c,fun _ => 0⟩
def coord [DecidableEq V] (v : V) : Form V := ⟨0,fun u => if u=v then 1 else 0⟩
def add (f g : Form V) : Form V := ⟨f.constant+g.constant,fun v => f.coeff v+g.coeff v⟩
def sub (f g : Form V) : Form V := ⟨f.constant-g.constant,fun v => f.coeff v-g.coeff v⟩
def sum [Fintype I] (f : I → Form V) : Form V := ⟨∑ i, (f i).constant,fun v => ∑ i, (f i).coeff v⟩

@[simp] lemma eval_const (c : ℚ) (x : V → ℚ) : (const c).eval x = c := by simp [eval,const]
@[simp] lemma realEval_const (c : ℚ) (x : V → ℝ) : (const c).realEval x = (c:ℝ) := by simp [realEval,const]
@[simp] lemma eval_coord [DecidableEq V] (v : V) (x : V → ℚ) : (coord v).eval x = x v := by simp [eval,coord]
@[simp] lemma realEval_coord [DecidableEq V] (v : V) (x : V → ℝ) : (coord v).realEval x = x v := by simp [realEval,coord,apply_ite]
@[simp] lemma eval_add (f g : Form V) (x : V → ℚ) : (f.add g).eval x = f.eval x+g.eval x := by
  simp only [eval,add,add_mul,Finset.sum_add_distrib]
  ring
@[simp] lemma realEval_add (f g : Form V) (x : V → ℝ) : (f.add g).realEval x = f.realEval x+g.realEval x := by
  simp only [realEval,add,Rat.cast_add,add_mul,Finset.sum_add_distrib]
  ring
@[simp] lemma eval_sub (f g : Form V) (x : V → ℚ) : (f.sub g).eval x = f.eval x-g.eval x := by
  simp only [eval,sub,sub_mul,Finset.sum_sub_distrib]
  ring
@[simp] lemma realEval_sub (f g : Form V) (x : V → ℝ) : (f.sub g).realEval x = f.realEval x-g.realEval x := by
  simp only [realEval,sub,Rat.cast_sub,sub_mul,Finset.sum_sub_distrib]
  ring
@[simp] lemma eval_sum [Fintype I] (f : I → Form V) (x : V → ℚ) :
    (sum f).eval x = ∑ i, (f i).eval x := by
  simp only [eval,sum,Finset.sum_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
@[simp] lemma realEval_sum [Fintype I] (f : I → Form V) (x : V → ℝ) :
    (sum f).realEval x = ∑ i, (f i).realEval x := by
  simp only [realEval,sum,Rat.cast_sum,Finset.sum_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]

lemma realEval_cast (f : Form V) (x : V → ℚ) : f.realEval (fun v => (x v:ℝ)) = (f.eval x:ℝ) := by
  simp [realEval,eval]

noncomputable def toRow (f : Form V) : Row (Fintype.card V) :=
  ⟨fun i => f.coeff ((Fintype.equivFin V).symm i),-f.constant⟩

lemma toRow_realHolds (f : Form V) (x : V → ℝ) :
    f.toRow.RealHolds (fun i => x ((Fintype.equivFin V).symm i)) ↔ f.realEval x ≤ 0 := by
  unfold Row.RealHolds Row.realValue toRow realEval
  rw [(Fintype.equivFin V).symm.sum_comp (fun v => (f.coeff v:ℝ)*x v),Rat.cast_neg]
  constructor <;> intro h <;> linarith

lemma toRow_holds (f : Form V) (x : Fin (Fintype.card V) → ℚ) :
    f.toRow.Holds x ↔ f.eval (fun v => x (Fintype.equivFin V v)) ≤ 0 := by
  unfold Row.Holds Row.value toRow eval
  have he := (Fintype.equivFin V).sum_comp (fun i => f.coeff ((Fintype.equivFin V).symm i)*x i)
  simp only [Equiv.symm_apply_apply] at he
  rw [he]
  constructor <;> intro h <;> linarith

end Form

theorem affine_rational_witness {V I : Type*} [Fintype V] [Fintype I] (f : I → Form V) :
    (∃ x : V → ℝ, ∀ i, (f i).realEval x ≤ 0) ↔
    (∃ x : V → ℚ, ∀ i, (f i).eval x ≤ 0) := by
  classical
  constructor
  · rintro ⟨x,hx⟩
    let rows : List (Row (Fintype.card V)) :=
      List.ofFn (fun i : Fin (Fintype.card I) => (f ((Fintype.equivFin I).symm i)).toRow)
    have hr : ∀ r ∈ rows, r.RealHolds (fun i => x ((Fintype.equivFin V).symm i)) := by
      intro r hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      exact ((f ((Fintype.equivFin I).symm i)).toRow_realHolds x).mpr (hx _)
    obtain ⟨y,hy⟩ := (rational_witness (Fintype.card V) rows).mp ⟨_,hr⟩
    refine ⟨fun v => y (Fintype.equivFin V v),?_⟩
    intro i
    apply ((f i).toRow_holds y).mp
    apply hy
    apply List.mem_ofFn.mpr
    exact ⟨Fintype.equivFin I i,by simp⟩
  · rintro ⟨x,hx⟩
    refine ⟨fun v => (x v:ℝ),?_⟩
    intro i
    rw [Form.realEval_cast]
    exact_mod_cast hx i

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
