import Mathlib
import OAI.Computability.FiniteCompiler.Control
import OAI.Computability.FiniteCompiler.Normalization
import OAI.Computability.FiniteCompiler.Simulator
import OAI.Computability.FiniteCompiler.Transition
import OAI.GroupTheory.FiniteType.TwistedBrin

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

structure WordCalculus (M : Type*) [Monoid M] (m : ℕ) where
  grade : M → ℕ
  grade_one : grade 1 = 0
  grade_mul : ∀ a b, grade (a * b) = grade a + grade b
  omega : M
  grade_omega : grade omega = 0
  omega_ne_one : omega ≠ 1
  normal : M → M
  normal_one : normal 1 = 1
  normal_omega : normal omega = omega
  nonincreasing : ∀ w, grade w ≤ m → grade (normal w) ≤ grade w
  idempotent : ∀ w, grade w ≤ m → normal (normal w) = normal w
  context : ∀ {u v}, normal u = normal v → ∀ a b,
    grade (a * u * b) ≤ m → grade (a * v * b) ≤ m →
    normal (a * u * b) = normal (a * v * b)
  absorbs : ∀ a b, normal (a * omega * b) = omega

namespace WordCalculus
variable {M : Type*} [Monoid M] {m : ℕ} (C : WordCalculus M m)
variable (k : Type*) [CommSemiring k]

def ball (b : ℕ) : Submodule k (MonoidAlgebra k M) :=
  MonoidAlgebra.supported k k {w | C.grade w ≤ b}

theorem mem_ball_iff {b : ℕ} {p : MonoidAlgebra k M} :
    p ∈ C.ball k b ↔ ∀ w ∈ p.coeff.support, C.grade w ≤ b := Iff.rfl

theorem ball_mono {b c : ℕ} (hbc : b ≤ c) : C.ball k b ≤ C.ball k c := by
  intro p hp w hw
  exact (hp hw).trans hbc

theorem single_mem_ball {w : M} {b : ℕ} (hw : C.grade w ≤ b) (a : k) :
    MonoidAlgebra.single w a ∈ C.ball k b := by
  change ∀ ⦃v⦄, v ∈ (MonoidAlgebra.single w a).coeff.support → C.grade v ≤ b
  intro v hv
  have hvw : v = w := ((Finsupp.mem_support_single v w a).mp hv).1
  simpa only [hvw] using hw

theorem ball_induction {b : ℕ} {P : MonoidAlgebra k M → Prop}
    (hp : ∀ w, C.grade w ≤ b → P (MonoidAlgebra.single w 1))
    (hz : P 0) (ha : ∀ p q, P p → P q → P (p+q))
    (hs : ∀ (a : k) p, P p → P (a • p)) {p : MonoidAlgebra k M}
    (h : p ∈ C.ball k b) : P p := by
  rw [ball, MonoidAlgebra.supported_eq_span_single] at h
  induction h using Submodule.span_induction with
  | mem p h => obtain ⟨w, hw, rfl⟩ := h; exact hp w hw
  | zero => exact hz
  | add p q _ _ hp hq => exact ha p q hp hq
  | smul a p _ hp => exact hs a p hp

@[simp] theorem one_mem_ball (b : ℕ) : (1 : MonoidAlgebra k M) ∈ C.ball k b := by
  rw [MonoidAlgebra.one_def]
  exact C.single_mem_ball k (by rw [C.grade_one]; exact Nat.zero_le _) 1

theorem mul_mem_ball {p q : MonoidAlgebra k M} {b c : ℕ}
    (hp : p ∈ C.ball k b) (hq : q ∈ C.ball k c) : p*q ∈ C.ball k (b+c) := by
  apply C.ball_induction k (P := fun p => p*q ∈ C.ball k (b+c)) ?_ ?_ ?_ ?_ hp
  · intro u hu
    apply C.ball_induction k (P := fun q => MonoidAlgebra.single u 1*q ∈ C.ball k (b+c))
      ?_ ?_ ?_ ?_ hq
    · intro v hv
      rw [MonoidAlgebra.single_mul_single]
      exact C.single_mem_ball k (by rw [C.grade_mul]; omega) _
    · simp
    · intro x y hx hy
      rw [mul_add]
      exact (C.ball k (b+c)).add_mem hx hy
    · intro a x hx
      rw [mul_smul_comm]
      exact (C.ball k (b+c)).smul_mem a hx
  · simp
  · intro x y hx hy
    rw [add_mul]
    exact (C.ball k (b+c)).add_mem hx hy
  · intro a x hx
    rw [smul_mul_assoc]
    exact (C.ball k (b+c)).smul_mem a hx

def collect : MonoidAlgebra k M →ₗ[k] MonoidAlgebra k M :=
  (Finsupp.linearCombination k (fun w =>
    if C.normal w = C.omega then 0 else MonoidAlgebra.single (C.normal w) (1 : k))).comp
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem collect_single (w : M) (a : k) :
    C.collect k (MonoidAlgebra.single w a) =
      if C.normal w = C.omega then 0 else MonoidAlgebra.single (C.normal w) a := by
  classical
  simp only [collect, LinearMap.comp_apply]
  split <;> rename_i h <;> simp [h, MonoidAlgebra.smul_single]

@[simp] theorem collect_one : C.collect k 1 = 1 := by
  rw [MonoidAlgebra.one_def, C.collect_single, C.normal_one,
    ite_eq_right (Ne.symm C.omega_ne_one)]

@[simp] theorem collect_omega (a : k) :
    C.collect k (MonoidAlgebra.single C.omega a) = 0 := by
  simp [C.normal_omega]

theorem collect_mem_ball {p : MonoidAlgebra k M} {b : ℕ}
    (hp : p ∈ C.ball k b) (hb : b ≤ m) : C.collect k p ∈ C.ball k b := by
  classical
  apply C.ball_induction k (P := fun p => C.collect k p ∈ C.ball k b) ?_ ?_ ?_ ?_ hp
  · intro w hw
    rw [C.collect_single]
    split
    · exact (C.ball k b).zero_mem
    · exact C.single_mem_ball k ((C.nonincreasing w (hw.trans hb)).trans hw) 1
  · simp
  · intro x y hx hy
    rw [map_add]
    exact (C.ball k b).add_mem hx hy
  · intro a x hx
    rw [map_smul]
    exact (C.ball k b).smul_mem a hx

theorem collect_idempotent {p : MonoidAlgebra k M} {b : ℕ}
    (hp : p ∈ C.ball k b) (hb : b ≤ m) : C.collect k (C.collect k p) = C.collect k p := by
  classical
  apply C.ball_induction k (P := fun p => C.collect k (C.collect k p) = C.collect k p)
    ?_ ?_ ?_ ?_ hp
  · intro w hw
    rw [C.collect_single]
    split
    · exact map_zero _
    next h => simp [C.idempotent w (hw.trans hb), h]
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    simp only [map_smul, hx]

theorem collect_mul_right {p q : MonoidAlgebra k M} {b c : ℕ}
    (hp : p ∈ C.ball k b) (hq : q ∈ C.ball k c) (hbc : b+c ≤ m) :
    C.collect k (p * C.collect k q) = C.collect k (p*q) := by
  classical
  apply C.ball_induction k
    (P := fun p => C.collect k (p*C.collect k q) = C.collect k (p*q)) ?_ ?_ ?_ ?_ hp
  · intro u hu
    apply C.ball_induction k
      (P := fun q => C.collect k (MonoidAlgebra.single u 1*C.collect k q) =
        C.collect k (MonoidAlgebra.single u 1*q)) ?_ ?_ ?_ ?_ hq
    · intro v hv
      have hvn := C.nonincreasing v (by omega)
      have he := C.context (C.idempotent v (by omega)) u 1
        (by simp only [mul_one, C.grade_mul]; omega)
        (by simp only [mul_one, C.grade_mul]; omega)
      simp only [mul_one] at he
      rw [C.collect_single]
      by_cases hz : C.normal v = C.omega
      · rw [ite_eq_left hz, mul_zero, map_zero, MonoidAlgebra.single_mul_single, C.collect_single]
        have ha : C.normal (u*v) = C.omega := by
          rw [hz] at he
          exact he.symm.trans (by simpa using C.absorbs u 1)
        simp [ha]
      · rw [ite_eq_right hz, MonoidAlgebra.single_mul_single,
          MonoidAlgebra.single_mul_single, C.collect_single, C.collect_single, he]
    · simp
    · intro x y hx hy
      simp only [map_add, mul_add, hx, hy]
    · intro a x hx
      simp only [map_smul, mul_smul_comm, hx]
  · simp
  · intro x y hx hy
    simp only [add_mul, map_add, hx, hy]
  · intro a x hx
    simp only [smul_mul_assoc, map_smul, hx]

theorem collect_mul_left {p q : MonoidAlgebra k M} {b c : ℕ}
    (hp : p ∈ C.ball k b) (hq : q ∈ C.ball k c) (hbc : b+c ≤ m) :
    C.collect k (C.collect k p * q) = C.collect k (p*q) := by
  classical
  apply C.ball_induction k
    (P := fun p => C.collect k (C.collect k p*q) = C.collect k (p*q)) ?_ ?_ ?_ ?_ hp
  · intro u hu
    apply C.ball_induction k
      (P := fun q => C.collect k (C.collect k (MonoidAlgebra.single u 1)*q) =
        C.collect k (MonoidAlgebra.single u 1*q)) ?_ ?_ ?_ ?_ hq
    · intro v hv
      have hun := C.nonincreasing u (by omega)
      have he := C.context (C.idempotent u (by omega)) 1 v
        (by simp only [one_mul, C.grade_mul]; omega)
        (by simp only [one_mul, C.grade_mul]; omega)
      simp only [one_mul] at he
      rw [C.collect_single]
      by_cases hz : C.normal u = C.omega
      · rw [ite_eq_left hz, zero_mul, map_zero, MonoidAlgebra.single_mul_single, C.collect_single]
        have ha : C.normal (u*v) = C.omega := by
          rw [hz] at he
          exact he.symm.trans (by simpa using C.absorbs 1 v)
        simp [ha]
      · rw [ite_eq_right hz, MonoidAlgebra.single_mul_single,
          MonoidAlgebra.single_mul_single, C.collect_single, C.collect_single, he]
    · simp
    · intro x y hx hy
      simp only [mul_add, map_add, hx, hy]
    · intro a x hx
      simp only [mul_smul_comm, map_smul, hx]
  · simp
  · intro x y hx hy
    simp only [map_add, add_mul, hx, hy]
  · intro a x hx
    simp only [map_smul, smul_mul_assoc, hx]

theorem collect_context {p q x y : MonoidAlgebra k M} {a b c d : ℕ}
    (hp : p ∈ C.ball k b) (hq : q ∈ C.ball k c)
    (hx : x ∈ C.ball k a) (hy : y ∈ C.ball k d)
    (hpb : a+b+d ≤ m) (hqb : a+c+d ≤ m)
    (he : C.collect k p = C.collect k q) :
    C.collect k (x*p*y) = C.collect k (x*q*y) := by
  have hxp : C.collect k (x*p) = C.collect k (x*q) := by
    rw [← C.collect_mul_right k hx hp (by omega),
      ← C.collect_mul_right k hx hq (by omega), he]
  rw [← C.collect_mul_left k (C.mul_mem_ball k hx hp) hy hpb,
    ← C.collect_mul_left k (C.mul_mem_ball k hx hq) hy hqb, hxp]

theorem collect_context_zero {p x y : MonoidAlgebra k M} {a b d : ℕ}
    (hp : p ∈ C.ball k b) (hx : x ∈ C.ball k a) (hy : y ∈ C.ball k d)
    (hbd : a+b+d ≤ m) (he : C.collect k p = 0) : C.collect k (x*p*y) = 0 := by
  have hh := C.collect_context k hp (C.ball k 0).zero_mem hx hy hbd (by omega)
    (he.trans (map_zero _).symm)
  simpa using hh

end WordCalculus

namespace CompilerCalculus
open FiniteAlgebraicEnvelopes.Compiler
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

def calculus
    (decode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → Part (List S)} {m : ℕ} (budget : PartialBudget f m)
    (realizes : Word.Realizes A M f) :
    WordCalculus (FreeMonoid (Word.Letter S Γ Q)) m where
  grade w := Word.grade w.toList
  grade_one := rfl
  grade_mul a b := Word.grade_append a.toList b.toList
  omega := FreeMonoid.ofList [.zero]
  grade_omega := rfl
  omega_ne_one := by simp
  normal w := FreeMonoid.ofList (Word.normal A M (fun w => partValue (f w)) w.toList)
  normal_one := by simp
  normal_omega := by simp
  nonincreasing w hw := Word.normal_grade A M budget.totalize _ hw
  idempotent w hw := congrArg FreeMonoid.ofList
    (Word.normal_idempotent A M decode budget.totalize (realizes.computesAt A M budget) _ hw)
  context h a b hu hv := congrArg FreeMonoid.ofList
    (Word.normal_context A M decode budget.totalize (realizes.computesAt A M budget)
      (congrArg FreeMonoid.toList h) a.toList b.toList hu hv)
  absorbs a b := by
    apply congrArg FreeMonoid.ofList
    simpa using Word.normal_contains_omega A M (fun w => partValue (f w)) a.toList b.toList

theorem support_calls_terminate
    (decode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → Part (List S)} {m b : ℕ} (budget : PartialBudget f m)
    (realizes : Word.Realizes A M f)
    {p : MonoidAlgebra (ZMod 2) (FreeMonoid (Word.Letter S Γ Q))}
    (hp : p ∈ (calculus A M decode budget realizes).ball (ZMod 2) b) (hb : b ≤ m) :
    ∀ w ∈ p.coeff.support, (Word.partialNormal A M f w.toList).Dom := by
  intro w hw
  have hwb : Word.grade w.toList ≤ b := hp hw
  exact Word.partialNormal_terminates A M budget _ (hwb.trans hb)

end CompilerCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
