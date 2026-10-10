import Mathlib
import OAI.GroupTheory.BooneHigman.PartialAffine
import OAI.GroupTheory.BooneHigman.Steinberg
import OAI.GroupTheory.FiniteType.HomotopyFunctor
import OAI.GroupTheory.SimpleOvergroups.TruncatedAlgebra

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding.WordCalculus
noncomputable section
open scoped Classical

variable {M : Type*} [Monoid M] {m : ℕ} (C : WordCalculus M m)
variable (k : Type*) [CommRing k]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev MatrixBall (b : ℕ) (A : Matrix ι ι (MonoidAlgebra k M)) :=
  ∀ i j, A i j ∈ C.ball k b
abbrev ColumnBall (b : ℕ) (x : ι → MonoidAlgebra k M) := ∀ i, x i ∈ C.ball k b

def matrixCollect (A : Matrix ι ι (MonoidAlgebra k M)) : Matrix ι ι (MonoidAlgebra k M) :=
  A.map (C.collect k)
def columnCollect (x : ι → MonoidAlgebra k M) : ι → MonoidAlgebra k M :=
  fun i => C.collect k (x i)

@[simp] theorem matrixCollect_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MonoidAlgebra k M)) (i j : ι) :
    C.matrixCollect k A i j = C.collect k (A i j) := rfl
@[simp] theorem columnCollect_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → MonoidAlgebra k M) (i : ι) :
    C.columnCollect k x i = C.collect k (x i) := rfl

@[simp] theorem matrixCollect_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    C.matrixCollect k (1 : Matrix ι ι (MonoidAlgebra k M)) = 1 :=
  Matrix.map_one _ (map_zero _) (C.collect_one k)
@[simp] theorem matrixCollect_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    C.matrixCollect k (0 : Matrix ι ι (MonoidAlgebra k M)) = 0 :=
  Matrix.map_zero _ (map_zero _)
@[simp] theorem columnCollect_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    C.columnCollect k (0 : ι → MonoidAlgebra k M) = 0 := by
  funext i; exact (C.collect k).map_zero

@[simp] theorem matrixBall_one {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ℕ) :
    C.MatrixBall k b (1 : Matrix ι ι (MonoidAlgebra k M)) := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, C.one_mem_ball]
@[simp] theorem matrixBall_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ℕ) :
    C.MatrixBall k b (0 : Matrix ι ι (MonoidAlgebra k M)) := by
  intro i j; exact (C.ball k b).zero_mem
@[simp] theorem columnBall_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ℕ) :
    C.ColumnBall k b (0 : ι → MonoidAlgebra k M) := by
  intro i; exact (C.ball k b).zero_mem

theorem matrixBall_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k b B) : C.MatrixBall k b (A+B) := by
  intro i j; exact (C.ball k b).add_mem (hA i j) (hB i j)
theorem matrixBall_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k b B) : C.MatrixBall k b (A-B) := by
  intro i j; exact (C.ball k b).sub_mem (hA i j) (hB i j)

theorem matrixBall_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : MonoidAlgebra k M} {b : ℕ}
    (hp : p ∈ C.ball k b) (i j : ι) : C.MatrixBall k b (Matrix.single i j p) := by
  intro u v
  by_cases hi : i = u <;> by_cases hj : j = v <;> simp [hi, hj, hp]

theorem matrixBall_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) : C.MatrixBall k (b+c) (A*B) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (C.ball k (b+c)).sum_mem (fun l _ => C.mul_mem_ball k (hA i l) (hB l j))

theorem columnBall_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)} {x : ι → MonoidAlgebra k M}
    {b c : ℕ} (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) :
    C.ColumnBall k (b+c) (A.mulVec x) := by
  intro i
  exact (C.ball k (b+c)).sum_mem (fun l _ => C.mul_mem_ball k (hA i l) (hx l))

theorem matrixCollect_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)} {b : ℕ}
    (hA : C.MatrixBall k b A) (hb : b ≤ m) : C.MatrixBall k b (C.matrixCollect k A) := by
  intro i j; exact C.collect_mem_ball k (hA i j) hb

theorem columnCollect_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : ι → MonoidAlgebra k M} {b : ℕ}
    (hx : C.ColumnBall k b x) (hb : b ≤ m) : C.ColumnBall k b (C.columnCollect k x) := by
  intro i; exact C.collect_mem_ball k (hx i) hb

theorem matrixCollect_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)} {b : ℕ}
    (hA : C.MatrixBall k b A) (hb : b ≤ m) :
    C.matrixCollect k (C.matrixCollect k A) = C.matrixCollect k A := by
  funext i j; exact C.collect_idempotent k (hA i j) hb

theorem columnCollect_idempotent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : ι → MonoidAlgebra k M} {b : ℕ}
    (hx : C.ColumnBall k b x) (hb : b ≤ m) :
    C.columnCollect k (C.columnCollect k x) = C.columnCollect k x := by
  funext i; exact C.collect_idempotent k (hx i) hb

theorem matrixCollect_mul_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) (hbc : b+c ≤ m) :
    C.matrixCollect k (C.matrixCollect k A * B) = C.matrixCollect k (A*B) := by
  funext i j
  simp only [matrixCollect_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_left k (hA i l) (hB l j) hbc

theorem matrixCollect_mul_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) (hbc : b+c ≤ m) :
    C.matrixCollect k (A * C.matrixCollect k B) = C.matrixCollect k (A*B) := by
  funext i j
  simp only [matrixCollect_apply, Matrix.mul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_right k (hA i l) (hB l j) hbc

theorem matrixCollect_context {P Q X Y : Matrix ι ι (MonoidAlgebra k M)} {a b c d : ℕ}
    (hp : C.MatrixBall k b P) (hq : C.MatrixBall k c Q)
    (hx : C.MatrixBall k a X) (hy : C.MatrixBall k d Y)
    (hpb : a+b+d ≤ m) (hqb : a+c+d ≤ m)
    (he : C.matrixCollect k P = C.matrixCollect k Q) :
    C.matrixCollect k (X*P*Y) = C.matrixCollect k (X*Q*Y) := by
  have hxp : C.matrixCollect k (X*P) = C.matrixCollect k (X*Q) := by
    rw [← C.matrixCollect_mul_right k hx hp (by omega),
      ← C.matrixCollect_mul_right k hx hq (by omega), he]
  rw [← C.matrixCollect_mul_left k (C.matrixBall_mul k hx hp) hy hpb,
    ← C.matrixCollect_mul_left k (C.matrixBall_mul k hx hq) hy hqb, hxp]

theorem columnCollect_mulVec_left {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)}
    {x : ι → MonoidAlgebra k M} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) (hbc : b+c ≤ m) :
    C.columnCollect k ((C.matrixCollect k A).mulVec x) = C.columnCollect k (A.mulVec x) := by
  funext i
  simp only [columnCollect_apply, Matrix.mulVec, dotProduct, matrixCollect_apply, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_left k (hA i l) (hx l) hbc

theorem columnCollect_mulVec_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι (MonoidAlgebra k M)}
    {x : ι → MonoidAlgebra k M} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) (hbc : b+c ≤ m) :
    C.columnCollect k (A.mulVec (C.columnCollect k x)) = C.columnCollect k (A.mulVec x) := by
  funext i
  simp only [columnCollect_apply, Matrix.mulVec, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact C.collect_mul_right k (hA i l) (hx l) hbc

theorem columnCollect_context {A : Matrix ι ι (MonoidAlgebra k M)}
    {x y : ι → MonoidAlgebra k M} {a b c : ℕ}
    (hA : C.MatrixBall k a A) (hx : C.ColumnBall k b x) (hy : C.ColumnBall k c y)
    (hb : a+b ≤ m) (hc : a+c ≤ m) (he : C.columnCollect k x = C.columnCollect k y) :
    C.columnCollect k (A.mulVec x) = C.columnCollect k (A.mulVec y) := by
  rw [← C.columnCollect_mulVec_right k hA hx hb,
    ← C.columnCollect_mulVec_right k hA hy hc, he]

def matrixPair (u : (Matrix ι ι (MonoidAlgebra k M))ˣ) :=
  (C.matrixCollect k u.val, C.matrixCollect k u.inv)

def UnitBall (b : ℕ) (u : (Matrix ι ι (MonoidAlgebra k M))ˣ) : Prop :=
  C.MatrixBall k b u.val ∧ C.MatrixBall k b u.inv

@[simp] theorem unitBall_one (b : ℕ) :
    C.UnitBall k b (1 : (Matrix ι ι (MonoidAlgebra k M))ˣ) :=
  ⟨C.matrixBall_one k b, C.matrixBall_one k b⟩

theorem unitBall_inv {u : (Matrix ι ι (MonoidAlgebra k M))ˣ} {b : ℕ}
    (hu : C.UnitBall k b u) : C.UnitBall k b u⁻¹ := ⟨hu.2, hu.1⟩

theorem unitBall_mul {u v : (Matrix ι ι (MonoidAlgebra k M))ˣ} {b c : ℕ}
    (hu : C.UnitBall k b u) (hv : C.UnitBall k c v) : C.UnitBall k (b+c) (u*v) := by
  refine ⟨C.matrixBall_mul k hu.1 hv.1, ?_⟩
  change C.MatrixBall k (b+c) (v.inv * u.inv)
  simpa only [Nat.add_comm] using C.matrixBall_mul k hv.2 hu.2

theorem unitBall_elementary {p : MonoidAlgebra k M} {b : ℕ}
    (hp : p ∈ C.ball k b) (i j : ι) (hij : i ≠ j) :
    C.UnitBall k b (FiniteAlgebraicEnvelopes.Steinberg.elementary i j hij p) :=
  ⟨C.matrixBall_add k (C.matrixBall_one k b) (C.matrixBall_single k hp i j),
    C.matrixBall_sub k (C.matrixBall_one k b) (C.matrixBall_single k hp i j)⟩

theorem matrixPair_context {p q x y : (Matrix ι ι (MonoidAlgebra k M))ˣ} {a b c d : ℕ}
    (hp : C.UnitBall k b p) (hq : C.UnitBall k c q)
    (hx : C.UnitBall k a x) (hy : C.UnitBall k d y)
    (hb : a+b+d ≤ m) (hc : a+c+d ≤ m)
    (he : C.matrixPair k p = C.matrixPair k q) :
    C.matrixPair k (x*p*y) = C.matrixPair k (x*q*y) := by
  apply Prod.ext
  · exact C.matrixCollect_context k hp.1 hq.1 hx.1 hy.1 hb hc (congrArg Prod.fst he)
  · change C.matrixCollect k (y.inv * (p.inv * x.inv)) =
      C.matrixCollect k (y.inv * (q.inv * x.inv))
    rw [← mul_assoc, ← mul_assoc]
    exact C.matrixCollect_context k hp.2 hq.2 hy.2 hx.2 (by omega) (by omega)
      (congrArg Prod.snd he)

theorem matrixPair_inv {u v : (Matrix ι ι (MonoidAlgebra k M))ˣ}
    (he : C.matrixPair k u = C.matrixPair k v) : C.matrixPair k u⁻¹ = C.matrixPair k v⁻¹ :=
  Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)

theorem matrixPair_action {u v : (Matrix ι ι (MonoidAlgebra k M))ˣ}
    {x : ι → MonoidAlgebra k M} {b c d : ℕ}
    (hu : C.UnitBall k b u) (hv : C.UnitBall k c v) (hx : C.ColumnBall k d x)
    (hb : b+d ≤ m) (hc : c+d ≤ m) (he : C.matrixPair k u = C.matrixPair k v) :
    C.columnCollect k (u.val.mulVec x) = C.columnCollect k (v.val.mulVec x) := by
  have hh : C.matrixCollect k u.val = C.matrixCollect k v.val := congrArg Prod.fst he
  rw [← C.columnCollect_mulVec_left k hu.1 hx hb,
    ← C.columnCollect_mulVec_left k hv.1 hx hc, hh]

theorem inverse_action_iff {u : (Matrix ι ι (MonoidAlgebra k M))ˣ}
    {y z : ι → MonoidAlgebra k M} {b c e : ℕ}
    (hu : C.UnitBall k b u) (hy : C.ColumnBall k c y) (hz : C.ColumnBall k e z)
    (hyb : b+c ≤ m) (hzb : b+e ≤ m) (hybb : 2*b+c ≤ m) (hzbb : 2*b+e ≤ m) :
    C.columnCollect k y = C.columnCollect k (u.val.mulVec z) ↔
    C.columnCollect k (u.inv.mulVec y) = C.columnCollect k z := by
  constructor
  · intro heq
    have hh := C.columnCollect_context k hu.2 hy (C.columnBall_mulVec k hu.1 hz)
      hyb (by omega) heq
    simpa only [Matrix.mulVec_mulVec, u.inv_val, Matrix.one_mulVec] using hh
  · intro heq
    have hh := C.columnCollect_context k hu.1 (C.columnBall_mulVec k hu.2 hy) hz
      (by omega) hzb heq
    simpa only [Matrix.mulVec_mulVec, u.val_inv, Matrix.one_mulVec] using hh

theorem inverse_action_iff_of_total {u : (Matrix ι ι (MonoidAlgebra k M))ˣ}
    {y z : ι → MonoidAlgebra k M} {b c e d : ℕ}
    (hu : C.UnitBall k b u) (hy : C.ColumnBall k c y) (hz : C.ColumnBall k e z)
    (htotal : b+c+e ≤ d) (hm : 3*d ≤ m) :
    C.columnCollect k y = C.columnCollect k (u.val.mulVec z) ↔
    C.columnCollect k (u.inv.mulVec y) = C.columnCollect k z :=
  C.inverse_action_iff k hu hy hz (by omega) (by omega) (by omega) (by omega)

end
end SimpleFInftyOvergroups.BoundedEncoding.WordCalculus

end OAI
