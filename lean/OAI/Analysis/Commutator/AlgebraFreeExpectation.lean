import Mathlib
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.AlgebraFreeExpectation

open FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S τ)

lemma centered_mem {i : ι} {a : A} (ha : a ∈ S i) :
    a - τ a • (1 : A) ∈ S i :=
  sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S i)))

omit [StarRing A] [StarModule ℂ A] in
include hτ1 in
lemma centered_zero (a : A) : τ (a - τ a • (1 : A)) = 0 := by
  simp [map_sub, map_smul, hτ1]

include hfree in
lemma free_two {i j : ι} (hij : i ≠ j) {a b : A} (ha : a ∈ S i) (hb : b ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0) :
    τ (a*b) = 0 := by
  let x : Letter S τ := ⟨i, a, ha, ha0⟩
  let y : Letter S τ := ⟨j, b, hb, hb0⟩
  have h := hfree [x, y] (by simpa [Reduced, List.isChain_cons_cons, x, y]) (by simp)
  simpa [word, x, y] using h

include hfree in
lemma free_three {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) :
    τ (a*b*c) = 0 := by
  let x : Letter S τ := ⟨i, a, ha, ha0⟩
  let y : Letter S τ := ⟨j, b, hb, hb0⟩
  let z : Letter S τ := ⟨i, c, hc, hc0⟩
  have h := hfree [x, y, z]
    (by simp [Reduced, List.isChain_cons_cons, x, y, z, hij, hij.symm]) (by simp)
  simpa [word, x, y, z, mul_assoc] using h

include hfree in
lemma free_four {i j : ι} (hij : i ≠ j) {a b c d : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i) (hd : d ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0)
    (hc0 : τ c = 0) (hd0 : τ d = 0) :
    τ (a*b*c*d) = 0 := by
  let x : Letter S τ := ⟨i, a, ha, ha0⟩
  let y : Letter S τ := ⟨j, b, hb, hb0⟩
  let z : Letter S τ := ⟨i, c, hc, hc0⟩
  let w : Letter S τ := ⟨j, d, hd, hd0⟩
  have h := hfree [x, y, z, w]
    (by simp [Reduced, List.isChain_cons_cons, x, y, z, w, hij, hij.symm]) (by simp)
  simpa [word, x, y, z, w, mul_assoc] using h

include hτ1 hfree in
lemma centered_mul_zero {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (ha0 : τ a = 0) :
    τ (a*b) = 0 := by
  have h := free_two τ S hfree hij ha (centered_mem τ S hb) ha0 (centered_zero τ hτ1 b)
  simpa [mul_sub, mul_smul_comm, map_sub, map_smul, ha0] using h

include hτ1 hfree in
lemma mul_centered_zero {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hb0 : τ b = 0) :
    τ (a*b) = 0 := by
  have h := free_two τ S hfree hij (centered_mem τ S ha) hb (centered_zero τ hτ1 a) hb0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hb0] using h

include hτ1 hfree in
lemma centered_middle_pairing {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0) :
    τ (c*a*b) = 0 := by
  have h := free_three τ S hfree hij.symm (centered_mem τ S hc) ha hb
    (centered_zero τ hτ1 c) ha0 hb0
  have hab := free_two τ S hfree hij ha hb ha0 hb0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hab, mul_assoc] using h

include hτ1 hfree in
lemma centered_sandwich_pairing {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0) :
    τ (c*a*b*a) = 0 := by
  have h := free_four τ S hfree hij.symm (centered_mem τ S hc) ha hb ha
    (centered_zero τ hτ1 c) ha0 hb0 ha0
  have hab := free_three τ S hfree hij ha hb ha ha0 hb0 ha0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hab] using h

include hτ1 hfree in
theorem free_compression_pairing {i j : ι} (hij : i ≠ j) {e b c : A}
    (he : e ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j) (hb0 : τ b = 0) :
    τ (c * (e*b*e)) = (τ e)^2 * τ (c*b) := by
  let a := e - τ e • (1 : A)
  have ha : a ∈ S i := centered_mem τ S he
  have ha0 : τ a = 0 := centered_zero τ hτ1 e
  have h1 := centered_sandwich_pairing τ hτ1 S hfree hij ha hb hc ha0 hb0
  have h2 := centered_middle_pairing τ hτ1 S hfree hij ha hb hc ha0 hb0
  have h3 := mul_centered_zero τ hτ1 S hfree hij.symm (mul_mem hc hb) ha ha0
  have hid : c * (e*b*e) = c*a*b*a + τ e • (c*a*b) +
      τ e • (c*b*a) + ((τ e)^2) • (c*b) := by
    dsimp [a]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one,
      smul_sub, smul_smul, pow_two]
    noncomm_ring
  rw [hid]
  simp only [map_add, map_smul, h1, h2, h3, smul_eq_mul, mul_zero, zero_add]

end Kadison.AlgebraFreeExpectation

end

end
end

end OAI
