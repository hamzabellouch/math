import Mathlib

namespace OAI

namespace Erdos970

section

namespace ErdosCoprimeResidueInterval
open scoped ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable

theorem moebius_divisor_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

theorem coprime_indicator (H : ℕ) (hH : 0 < H) (m : ℤ) :
    (∑ d ∈ H.divisors, if (d : ℤ) ∣ m then (μ d : ℝ) else 0) =
      if H.Coprime m.natAbs then 1 else 0 := by
  have hg : 0 < H.gcd m.natAbs := Nat.gcd_pos_of_pos_left m.natAbs hH
  have hf : H.divisors.filter (fun d : ℕ => (d : ℤ) ∣ m) = (H.gcd m.natAbs).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Int.natCast_dvd,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdH,_⟩,hdm⟩
      exact ⟨⟨hdH,hdm⟩,hg.ne'⟩
    · rintro ⟨⟨hdH,hdm⟩,_⟩
      exact ⟨⟨hdH,hH.ne'⟩,hdm⟩
  rw [← Finset.sum_filter,hf,moebius_divisor_sum]

theorem moebius_abs_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)

theorem moebius_density (H : ℕ) (hH : 0 < H) :
    (∑ d ∈ H.divisors, (μ d : ℝ)/(d : ℝ)) = (H.totient : ℝ)/(H : ℝ) := by
  have ht : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, (d.totient : ℝ)) = (n : ℝ) := by
    intro n _
    exact_mod_cast Nat.sum_totient n
  have hi := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp ht H hH
  rw [Nat.sum_divisorsAntidiagonal (fun d k => (μ d : ℝ)*(k : ℝ))] at hi
  apply (eq_div_iff (show (H : ℝ) ≠ 0 by exact_mod_cast hH.ne')).mpr
  rw [Finset.sum_mul]
  calc
    _ = ∑ d ∈ H.divisors, (μ d : ℝ)*((H/d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
        (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')]
      ring
    _ = _ := hi

theorem coprime_count_expansion (H : ℕ) (hH : 0 < H) (C : Finset ℤ) (F : ℤ → Prop) :
    ((C.filter (fun m => H.Coprime m.natAbs ∧ F m)).card : ℝ) =
      ∑ d ∈ H.divisors, (μ d : ℝ)*((C.filter (fun m => (d : ℤ) ∣ m ∧ F m)).card : ℝ) := by
  classical
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hF : F m
  · simpa only [hF,and_true,mul_ite,mul_one,mul_zero] using (coprime_indicator H hH m).symm
  · simp [hF]

end ErdosCoprimeResidueInterval

end

end Erdos970

end OAI
