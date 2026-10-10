import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicSchreierKernel

namespace OAI

/-! # Growth drops in the kernel of a surjection to the integers

Distinct integer heights give disjoint translates of a kernel word ball.
The count supplies the degree drop required by the Gromov induction.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G : Type*} [Group G] [DecidableEq G]

theorem cyclic_kernel_wordBall_count (q : G →* Multiplicative ℤ) (t : G)
    (ht : q t = Multiplicative.ofAdd 1) (S : Finset G) (T : Finset q.ker)
    (m : ℕ) (htlen : t ∈ wordBall S m)
    (hT : ∀ x ∈ T, (x : G) ∈ wordBall S m) (n : ℕ) :
    (n + 1) * (wordBall T n).card ≤ (wordBall S (2 * m * n)).card := by
  let f : (Fin (n + 1) × ↥(wordBall T n)) → ↥(wordBall S (2 * m * n)) := fun a =>
    ⟨(a.2.val : G) * t ^ (a.1.val : ℤ), by
      have hx := wordBall_hom_mem_scaled q.ker.subtype S T m hT n a.2.property
      have hy := pow_mem_wordBall htlen a.1.val
      have hidx : a.1.val ≤ n := Nat.lt_succ_iff.mp a.1.isLt
      have hy' : t ^ (a.1.val : ℤ) ∈ wordBall S (m * n) :=
        wordBall_mono S (Nat.mul_le_mul_left m hidx) (by simpa using hy)
      have hh := mul_mem_wordBall hx hy'
      simpa only [Subgroup.subtype_apply, show m * n + m * n = 2 * m * n by ring] using hh⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he : (a.2.val : G) * t ^ (a.1.val : ℤ) =
        (b.2.val : G) * t ^ (b.1.val : ℤ) := congrArg Subtype.val hab
    have hh := congrArg q he
    rw [map_mul, map_mul, a.2.val.property, b.2.val.property, one_mul, one_mul,
      cyclicHeight_zpow q t ht, cyclicHeight_zpow q t ht] at hh
    have hi : a.1 = b.1 := by
      apply Fin.ext
      have hz := congrArg Multiplicative.toAdd hh
      change (a.1.val : ℤ) = (b.1.val : ℤ) at hz
      exact_mod_cast hz
    apply Prod.ext hi
    apply Subtype.ext
    apply Subtype.ext
    rw [hi] at he
    exact mul_right_cancel he
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

theorem cyclic_kernel_word_growth_degree_drop
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (S : Finset G) (T : Finset q.ker) (m : ℕ) (htlen : t ∈ wordBall S m)
    (hT : ∀ x ∈ T, (x : G) ∈ wordBall S m) (C d : ℕ)
    (hvol : ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ (d + 1)) :
    ∀ n, (wordBall T n).card ≤ (C * (1 + 2 * m) ^ (d + 1)) * (1 + n) ^ d := by
  intro n
  have hcount := (cyclic_kernel_wordBall_count q t ht S T m htlen hT n).trans (hvol (2 * m * n))
  have hbase : 1 + 2 * m * n ≤ (1 + 2 * m) * (1 + n) := by nlinarith
  have hbound : (n + 1) * (wordBall T n).card ≤
      (n + 1) * ((C * (1 + 2 * m) ^ (d + 1)) * (1 + n) ^ d) := by
    calc
      _ ≤ C * (1 + 2 * m * n) ^ (d + 1) := hcount
      _ ≤ C * ((1 + 2 * m) * (1 + n)) ^ (d + 1) := by gcongr
      _ = _ := by rw [mul_pow, pow_succ (1 + n) d]; ring
  exact (mul_le_mul_iff_right₀ (by omega : 0 < n + 1)).mp hbound

end PolycyclicRecognition

end

end OAI
