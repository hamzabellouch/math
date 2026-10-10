import Mathlib
import OAI.Combinatorics.KMedian.PCP.Quadratic

namespace OAI

section Inline_PCPQuadraticEncoding

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Algebra
variable {I T : Type} [Fintype I] [Fintype T]

theorem bit_mul_self (b : Bit) : b*b = b := by
  rcases bit_cases b with rfl | rfl <;> simp

@[simp] theorem dot_sum (a : BitVector I) (x : T → BitVector I) :
    dot a (∑ t, x t) = ∑ t, dot a (x t) := map_sum (dotHom a) _ _

@[simp] theorem dot_smul (a x : BitVector I) (c : Bit) :
    dot a (c • x) = c * dot a x := ZMod.map_smul (dotHom a) c x

def unitForm [DecidableEq I] (i j : I) : BitVector (I × I) := Pi.single (i,j) 1

@[simp] theorem dot_unitForm [DecidableEq I] (a : BitVector (I × I)) (i j : I) :
    dot a (unitForm i j) = a (i,j) := by
  simp [unitForm, dot, Pi.single_apply, mul_ite]

@[simp] theorem quadratic_diagonal [DecidableEq I] (a : BitVector I) (i : I) :
    dot (tensor a a) (unitForm i i) = a i := by
  simp [tensor, bit_mul_self]
end Algebra

namespace RelationEncoding
variable {I A : Type} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

abbrev Variable (I A : Type) := I ⊕ A
abbrev Equation (I A : Type) := Unit ⊕ ((A × A) ⊕ I)

def system (label : A → BitVector I) : QuadraticSystem (Variable I A) (Equation I A) where
  form q := match q with
    | .inl _ => ∑ a : A, unitForm (Sum.inr a) (Sum.inr a)
    | .inr (.inl (a,b)) => if a = b then 0 else unitForm (Sum.inr a) (Sum.inr b)
    | .inr (.inr i) => unitForm (Sum.inl i) (Sum.inl i) +
        ∑ a : A, label a i • unitForm (Sum.inr a) (Sum.inr a)
  rhs q := match q with | .inl _ => 1 | .inr _ => 0

theorem satisfies_iff (label : A → BitVector I) (z : BitVector (Variable I A)) :
    (system label).Satisfies z ↔
      (∑ a : A, z (.inr a)) = 1 ∧
      (∀ a b : A, a ≠ b → z (.inr a) * z (.inr b) = 0) ∧
      (∀ i : I, z (.inl i) + ∑ a : A, label a i * z (.inr a) = 0) := by
  constructor
  · intro hz
    refine ⟨?_, ?_, ?_⟩
    · simpa [system, tensor, bit_mul_self] using hz (.inl ())
    · intro a b hab
      simpa [system, hab, tensor] using hz (.inr (.inl (a,b)))
    · intro i
      simpa [system, tensor, bit_mul_self] using hz (.inr (.inr i))
  · rintro ⟨hs,hp,hi⟩ q
    rcases q with u | ab | i
    · simpa [system, tensor, bit_mul_self] using hs
    · obtain ⟨a,b⟩ := ab
      by_cases hab : a = b
      · simp [system, hab]
      · simpa [system, hab, tensor] using hp a b hab
    · simpa [system, tensor, bit_mul_self] using hi i

def witness (label : A → BitVector I) (a : A) : BitVector (Variable I A) :=
  Sum.elim (label a) (Pi.single a 1)

omit [Fintype I] [Fintype A] [DecidableEq I] in
@[simp] theorem witness_left (label : A → BitVector I) (a : A) (i : I) :
    witness label a (.inl i) = label a i := rfl

omit [Fintype I] [Fintype A] [DecidableEq I] in
@[simp] theorem witness_right (label : A → BitVector I) (a b : A) :
    witness label a (.inr b) = if b = a then 1 else 0 := by
  simp [witness, Pi.single_apply]

theorem complete (label : A → BitVector I) (a : A) :
    (system label).Satisfies (witness label a) := by
  rw [satisfies_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro b c hbc
    by_cases hb : b = a <;> by_cases hc : c = a <;>
      simp [hb, hc] at hbc ⊢
  · intro i
    simp [mul_ite, CharTwo.add_self_eq_zero]

theorem sound (label : A → BitVector I) (z : BitVector (Variable I A))
    (hz : (system label).Satisfies z) : ∃ a, ∀ i, z (.inl i) = label a i := by
  obtain ⟨hs,hp,hi⟩ := (satisfies_iff label z).mp hz
  have hex : ∃ a, z (.inr a) = 1 := by
    by_contra! ha
    have hzero : ∀ a, z (.inr a) = 0 := fun a => (bit_cases _).resolve_right (ha a)
    simp only [hzero, sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨a,ha⟩ := hex
  have hsel : ∀ b, z (.inr b) = if b = a then 1 else 0 := by
    intro b
    by_cases hb : b = a
    · simp [hb, ha]
    · have he := hp a b (Ne.symm hb)
      rw [ha, one_mul] at he
      simpa only [ite_eq_right hb] using he
  refine ⟨a,?_⟩
  intro i
  have he := hi i
  simp only [hsel, mul_ite, mul_one, mul_zero] at he
  simp only [sum_ite_eq', mem_univ, ite_true] at he
  calc
    z (.inl i) = (z (.inl i) + label a i) + label a i := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = label a i := by rw [he, zero_add]

theorem exact (label : A → BitVector I) (x : BitVector I) :
    (∃ z : BitVector (Variable I A), (system label).Satisfies z ∧
      (∀ i, z (.inl i) = x i)) ↔ ∃ a, label a = x := by
  constructor
  · rintro ⟨z,hz,hx⟩
    obtain ⟨a,ha⟩ := sound label z hz
    exact ⟨a, funext (fun i => (ha i).symm.trans (hx i))⟩
  · rintro ⟨a,rfl⟩
    exact ⟨witness label a, complete label a, fun _ => rfl⟩

end RelationEncoding
end MetricKMedian.PCP

end Inline_PCPQuadraticEncoding

end OAI
