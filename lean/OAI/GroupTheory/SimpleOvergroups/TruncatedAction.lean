import Mathlib
import OAI.GroupTheory.SimpleOvergroups.TruncatedMatrix

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

structure KeyBall (X K : Type*) where
  ball : ℕ → Set X
  mono : Monotone ball
  key : X → K

namespace KeyBall
variable {X K : Type*} (C : KeyBall X K) (m : ℕ)

def Represented (k : K) : Prop := ∃ b, b ≤ m ∧ ∃ x ∈ C.ball b, C.key x = k

def leastCost (k : K) : ℕ :=
  if h : C.Represented m k then Nat.find h else 0

theorem leastCost_spec {k : K} (h : C.Represented m k) :
    C.leastCost m k ≤ m ∧ ∃ x ∈ C.ball (C.leastCost m k), C.key x = k := by
  rw [leastCost, dite_eq_left h]
  exact Nat.find_spec h

theorem represented_key {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.Represented m (C.key x) := ⟨b, hb, x, hx, rfl⟩

theorem leastCost_le {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.leastCost m (C.key x) ≤ b := by
  rw [leastCost, dite_eq_left (C.represented_key m hx hb)]
  exact Nat.find_min' _ ⟨hb, x, hx, rfl⟩

variable [Nonempty X]

def representative (k : K) : X :=
  if h : ∃ x ∈ C.ball (C.leastCost m k), C.key x = k then Classical.choose h
  else Classical.choice ‹Nonempty X›

theorem representative_spec {k : K} (h : C.Represented m k) :
    C.representative m k ∈ C.ball (C.leastCost m k) ∧
      C.key (C.representative m k) = k := by
  have he := (C.leastCost_spec m h).2
  rw [representative, dite_eq_left he]
  exact Classical.choose_spec he

def canonical (x : X) : X := C.representative m (C.key x)

theorem canonical_congr {x y : X} (h : C.key x = C.key y) :
    C.canonical m x = C.canonical m y := congrArg (C.representative m) h

theorem canonical_mem {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.canonical m x ∈ C.ball b :=
  C.mono (C.leastCost_le m hx hb)
    (C.representative_spec m (C.represented_key m hx hb)).1

theorem key_canonical {x : X} {b : ℕ} (hx : x ∈ C.ball b) (hb : b ≤ m) :
    C.key (C.canonical m x) = C.key x :=
  (C.representative_spec m (C.represented_key m hx hb)).2

end KeyBall

structure ActionCalculus (V X K L : Type*) [Group V] [MulAction V X] (m : ℕ) where
  group : KeyBall V K
  point : KeyBall X L
  one_mem : ∀ b, (1 : V) ∈ group.ball b
  inv_mem : ∀ {b v}, v ∈ group.ball b → v⁻¹ ∈ group.ball b
  mul_mem : ∀ {b c u v}, u ∈ group.ball b → v ∈ group.ball c → u*v ∈ group.ball (b+c)
  smul_mem : ∀ {b c v x}, v ∈ group.ball b → x ∈ point.ball c → v • x ∈ point.ball (b+c)
  inv_congr : ∀ {u v}, group.key u = group.key v → group.key u⁻¹ = group.key v⁻¹
  mul_congr : ∀ {b c b' c' u v u' v'},
    u ∈ group.ball b → v ∈ group.ball c →
    u' ∈ group.ball b' → v' ∈ group.ball c' →
    b+c ≤ m → b'+c' ≤ m → group.key u = group.key u' → group.key v = group.key v' →
    group.key (u*v) = group.key (u'*v')
  smul_congr : ∀ {b c b' c' v x v' x'},
    v ∈ group.ball b → x ∈ point.ball c →
    v' ∈ group.ball b' → x' ∈ point.ball c' →
    b+c ≤ m → b'+c' ≤ m → group.key v = group.key v' → point.key x = point.key x' →
    point.key (v • x) = point.key (v' • x')

namespace ActionCalculus
variable {V X K L : Type*} [Group V] [MulAction V X] {m : ℕ}
  (C : ActionCalculus V X K L m)

theorem inverse_action_iff {v : V} {y z : X} {b c e : ℕ}
    (hv : v ∈ C.group.ball b) (hy : y ∈ C.point.ball c) (hz : z ∈ C.point.ball e)
    (hyb : b+c ≤ m) (hzb : b+e ≤ m) (hybb : 2*b+c ≤ m) (hzbb : 2*b+e ≤ m) :
    C.point.key y = C.point.key (v • z) ↔ C.point.key (v⁻¹ • y) = C.point.key z := by
  constructor
  · intro he
    simpa only [inv_smul_smul] using C.smul_congr (C.inv_mem hv) hy
      (C.inv_mem hv) (C.smul_mem hv hz) hyb (by omega) rfl he
  · intro he
    simpa only [smul_inv_smul] using C.smul_congr hv
      (C.smul_mem (C.inv_mem hv) hy) hv hz (by omega) hzb rfl he

theorem inverse_action_iff_of_total {v : V} {y z : X} {b c e d : ℕ}
    (hv : v ∈ C.group.ball b) (hy : y ∈ C.point.ball c) (hz : z ∈ C.point.ball e)
    (h : b+c+e ≤ d) (hm : 3*d ≤ m) :
    C.point.key y = C.point.key (v • z) ↔ C.point.key (v⁻¹ • y) = C.point.key z :=
  C.inverse_action_iff hv hy hz (by omega) (by omega) (by omega) (by omega)

theorem group_context {u v a z : V} {b c e f : ℕ}
    (hu : u ∈ C.group.ball b) (hv : v ∈ C.group.ball c)
    (ha : a ∈ C.group.ball e) (hz : z ∈ C.group.ball f)
    (hb : e+b+f ≤ m) (hc : e+c+f ≤ m) (he : C.group.key u = C.group.key v) :
    C.group.key (a*u*z) = C.group.key (a*v*z) :=
  C.mul_congr (C.mul_mem ha hu) hz (C.mul_mem ha hv) hz hb hc
    (C.mul_congr ha hu ha hv (by omega) (by omega) rfl he) rfl

end ActionCalculus

namespace WordCalculus
variable {M : Type*} [Monoid M] {m : ℕ} (C : WordCalculus M m)
variable (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[instance_reducible] def rawMatrixAction : MulAction (Matrix ι ι (MonoidAlgebra k M))ˣ (ι → MonoidAlgebra k M) where
  smul u x := u.val.mulVec x
  one_smul x := Matrix.one_mulVec x
  mul_smul u v x := (Matrix.mulVec_mulVec x u.val v.val).symm

attribute [local instance] rawMatrixAction

theorem matrixCollect_product {A B : Matrix ι ι (MonoidAlgebra k M)} {b c : ℕ}
    (hA : C.MatrixBall k b A) (hB : C.MatrixBall k c B) (hbc : b+c ≤ m) :
    C.matrixCollect k (C.matrixCollect k A * C.matrixCollect k B) = C.matrixCollect k (A*B) := by
  rw [C.matrixCollect_mul_left k hA (C.matrixCollect_mem k hB (by omega)) hbc,
    C.matrixCollect_mul_right k hA hB hbc]

theorem columnCollect_product {A : Matrix ι ι (MonoidAlgebra k M)} {x : ι → MonoidAlgebra k M}
    {b c : ℕ} (hA : C.MatrixBall k b A) (hx : C.ColumnBall k c x) (hbc : b+c ≤ m) :
    C.columnCollect k ((C.matrixCollect k A).mulVec (C.columnCollect k x)) =
      C.columnCollect k (A.mulVec x) := by
  rw [C.columnCollect_mulVec_left k hA (C.columnCollect_mem k hx (by omega)) hbc,
    C.columnCollect_mulVec_right k hA hx hbc]

def matrixActionCalculus (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ActionCalculus (Matrix ι ι (MonoidAlgebra k M))ˣ (ι → MonoidAlgebra k M)
      (Matrix ι ι (MonoidAlgebra k M) × Matrix ι ι (MonoidAlgebra k M))
      (ι → MonoidAlgebra k M) m where
  group :=
    { ball := C.UnitBall k
      mono := by
        intro b c hbc u hu
        exact ⟨fun i j => C.ball_mono k hbc (hu.1 i j),
          fun i j => C.ball_mono k hbc (hu.2 i j)⟩
      key := C.matrixPair k }
  point :=
    { ball := C.ColumnBall k
      mono := by
        intro b c hbc x hx i
        exact C.ball_mono k hbc (hx i)
      key := C.columnCollect k }
  one_mem := C.unitBall_one k
  inv_mem := C.unitBall_inv k
  mul_mem := C.unitBall_mul k
  smul_mem := fun hu hx => C.columnBall_mulVec k hu.1 hx
  inv_congr := C.matrixPair_inv k
  mul_congr := by
    intro b c b' c' u v u' v' hu hv hu' hv' hb hb' heu hev
    apply Prod.ext
    · change C.matrixCollect k (u.val*v.val) = C.matrixCollect k (u'.val*v'.val)
      rw [← C.matrixCollect_product k hu.1 hv.1 hb,
        ← C.matrixCollect_product k hu'.1 hv'.1 hb']
      rw [show C.matrixCollect k u.val = C.matrixCollect k u'.val from congrArg Prod.fst heu,
        show C.matrixCollect k v.val = C.matrixCollect k v'.val from congrArg Prod.fst hev]
    · change C.matrixCollect k (v.inv*u.inv) = C.matrixCollect k (v'.inv*u'.inv)
      rw [← C.matrixCollect_product k hv.2 hu.2 (by omega),
        ← C.matrixCollect_product k hv'.2 hu'.2 (by omega)]
      rw [show C.matrixCollect k u.inv = C.matrixCollect k u'.inv from congrArg Prod.snd heu,
        show C.matrixCollect k v.inv = C.matrixCollect k v'.inv from congrArg Prod.snd hev]
  smul_congr := by
    intro b c b' c' u x u' x' hu hx hu' hx' hb hb' heu hex
    change C.columnCollect k (u.val.mulVec x) = C.columnCollect k (u'.val.mulVec x')
    rw [← C.columnCollect_product k hu.1 hx hb, ← C.columnCollect_product k hu'.1 hx' hb']
    rw [show C.matrixCollect k u.val = C.matrixCollect k u'.val from congrArg Prod.fst heu,
      show C.columnCollect k x = C.columnCollect k x' from hex]

end WordCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
