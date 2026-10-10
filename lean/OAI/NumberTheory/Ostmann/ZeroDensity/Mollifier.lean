import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Convolution

namespace OAI

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta LSeries.notation

namespace Ostmann.ZeroDensity

def truncate (N : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≤ N then f n else 0, by simp⟩

@[simp] theorem truncate_apply (N : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    truncate N f n = if n ≤ N then f n else 0 := rfl

def mollifierCoefficient (X N : ℕ) : ArithmeticFunction ℂ :=
  truncate X (μ : ArithmeticFunction ℂ) * truncate N (ζ : ArithmeticFunction ℂ)

theorem mollifierCoefficient_initial {X N n : ℕ} (hnX : n ≤ X) (hnN : n ≤ N) :
    mollifierCoefficient X N n = (1 : ArithmeticFunction ℂ) n := by
  calc
    mollifierCoefficient X N n =
        ((μ : ArithmeticFunction ℂ) * (ζ : ArithmeticFunction ℂ)) n := by
      rw [mollifierCoefficient, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro p hp
      have hp1 := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
      have hp2 := Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
      simp [hp1.trans hnX, hp2.trans hnN]
    _ = _ := by rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]

@[simp] theorem mollifierCoefficient_one {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) :
    mollifierCoefficient X N 1 = 1 := by
  simpa using mollifierCoefficient_initial hX hN

theorem mollifierCoefficient_vanish {X N n : ℕ} (hX : X ≤ N)
    (hn : 2 ≤ n) (hnX : n ≤ X) : mollifierCoefficient X N n = 0 := by
  rw [mollifierCoefficient_initial hnX (hnX.trans hX)]
  exact ArithmeticFunction.one_apply_ne (by omega)

theorem mollifierCoefficient_support {X N n : ℕ} (hn : X * N < n) :
    mollifierCoefficient X N n = 0 := by
  rw [mollifierCoefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases hx : p.1 ≤ X
  · have hn' : ¬p.2 ≤ N := by
      intro hN
      have := Nat.mul_le_mul hx hN
      omega
    simp [hx, hn']
  · simp [hx]

theorem norm_mollifierCoefficient_le (X N n : ℕ) :
    ‖mollifierCoefficient X N n‖ ≤ (n.divisors.card : ℝ) := by
  rw [mollifierCoefficient, ArithmeticFunction.mul_apply]
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal,
      truncate X (μ : ArithmeticFunction ℂ) p.1 *
        truncate N (ζ : ArithmeticFunction ℂ) p.2‖ ≤
        ∑ p ∈ n.divisorsAntidiagonal,
          ‖truncate X (μ : ArithmeticFunction ℂ) p.1 *
            truncate N (ζ : ArithmeticFunction ℂ) p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp2 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
      by_cases hx : p.1 ≤ X <;> by_cases hn : p.2 ≤ N
      · rcases ArithmeticFunction.moebius_eq_or p.1 with hm | hm | hm <;>
          simp [hx, hn, ArithmeticFunction.natCoe_apply,
            ArithmeticFunction.intCoe_apply, ArithmeticFunction.zeta_apply_ne hp2, hm]
      · simp [hn]
      · simp [hx]
      · simp [hx]
    _ = (n.divisors.card : ℝ) := by
      rw [← Nat.map_div_right_divisors]
      simp

def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => f n * χ n, by simp⟩

@[simp] theorem characterTwist_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f : ArithmeticFunction ℂ) (n : ℕ) : characterTwist χ f n = f n * χ n := rfl

theorem characterTwist_mul {q : ℕ} (χ : DirichletCharacter ℂ q)
    (f g : ArithmeticFunction ℂ) :
    characterTwist χ (f * g) = characterTwist χ f * characterTwist χ g := by
  ext n
  simp only [characterTwist_apply, ArithmeticFunction.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [← hprod, Nat.cast_mul, map_mul]
  ring

theorem truncated_twist_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (N : ℕ) (f : ArithmeticFunction ℂ) (s : ℂ) :
    LSeriesSummable (characterTwist χ (truncate N f)) s := by
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  have hnN : ¬n ≤ N := by simpa using hn
  simp [LSeries.term, hnN]

theorem mollifier_product {q : ℕ} (χ : DirichletCharacter ℂ q)
    (X N : ℕ) (s : ℂ) :
    LSeries (characterTwist χ (mollifierCoefficient X N)) s =
      LSeries (characterTwist χ (truncate X (μ : ArithmeticFunction ℂ))) s *
      LSeries (characterTwist χ (truncate N (ζ : ArithmeticFunction ℂ))) s := by
  rw [mollifierCoefficient, characterTwist_mul]
  exact ArithmeticFunction.LSeries_mul' (truncated_twist_summable χ X _ s)
    (truncated_twist_summable χ N _ s)

end Ostmann.ZeroDensity

end

end OAI
