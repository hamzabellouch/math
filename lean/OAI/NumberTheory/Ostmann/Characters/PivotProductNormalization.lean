import OAI.NumberTheory.Ostmann.Characters.PivotProductFibers
import OAI.NumberTheory.Ostmann.Conclusion.BadFraction

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.PivotProductNormalization
open Construction Preliminaries PivotProductFibers

theorem normalization_pos {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) : 0 < normalization E :=
  Finset.prod_pos (fun i _ => inv_pos.mpr (hE i))

theorem normalization_le_exp {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (D : Fin n → ℝ) (hZ : ∀i,Real.exp (-D i) ≤ primeShellMass (E i)) :
    normalization E ≤ Real.exp (∑i,D i) := by
  calc
    _ ≤ ∏i,Real.exp (D i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact inv_nonneg.mpr ((Real.exp_pos _).trans_le (hZ i)).le
      · intro i hi
        have h := inv_anti₀ (Real.exp_pos (-D i)) (hZ i)
        simpa only [Real.exp_neg,inv_inv] using h
    _ = _ := (Real.exp_sum Finset.univ D).symm

theorem factor_le_exp {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (D : Fin n → ℝ) (hZ : ∀i,Real.exp (-D i) ≤ primeShellMass (E i)) :
    (n.factorial:ℝ)*normalization E ≤
      Real.exp (Real.log (n.factorial:ℝ)+∑i,D i) := by
  rw [Real.exp_add,Real.exp_log (by positivity : (0:ℝ)<n.factorial)]
  exact mul_le_mul_of_nonneg_left (normalization_le_exp E D hZ) (Nat.cast_nonneg _)

theorem log_factor_le {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (D : Fin n → ℝ) (hZ : ∀i,Real.exp (-D i) ≤ primeShellMass (E i)) :
    Real.log ((n.factorial:ℝ)*normalization E) ≤ Real.log (n.factorial:ℝ)+∑i,D i := by
  have hp : 0 < (n.factorial:ℝ)*normalization E :=
    mul_pos (by positivity) (normalization_pos E (fun i => (Real.exp_pos _).trans_le (hZ i)))
  have h := Real.log_le_log hp (factor_le_exp E D hZ)
  simpa only [Real.log_exp] using h

theorem log_factorial_upper_all (n : ℕ) :
    Real.log (n.factorial:ℝ) ≤ (n:ℝ)*Real.log (max (n:ℝ) 1) := by
  by_cases hn : n=0
  · simp [hn]
  · have hp : 0<n := Nat.pos_of_ne_zero hn
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast hp
    rw [max_eq_left h1]
    exact Conclusion.log_factorial_upper hp

theorem log_factor_le_count {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (D : Fin n → ℝ) (hZ : ∀i,Real.exp (-D i) ≤ primeShellMass (E i)) :
    Real.log ((n.factorial:ℝ)*normalization E) ≤
      (n:ℝ)*Real.log (max (n:ℝ) 1)+∑i,D i :=
  (log_factor_le E D hZ).trans (add_le_add (log_factorial_upper_all n) le_rfl)

theorem factor_le_exp_count {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (D : Fin n → ℝ) (hZ : ∀i,Real.exp (-D i) ≤ primeShellMass (E i)) :
    (n.factorial:ℝ)*normalization E ≤
      Real.exp ((n:ℝ)*Real.log (max (n:ℝ) 1)+∑i,D i) :=
  (factor_le_exp E D hZ).trans (Real.exp_le_exp.mpr
    (add_le_add (log_factorial_upper_all n) le_rfl))

theorem factor_le_exp_uniform {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (C L : ℝ) (hZ : ∀i,Real.exp (-(C*L)) ≤ primeShellMass (E i)) :
    (n.factorial:ℝ)*normalization E ≤ Real.exp (C*(n:ℝ)*L+Real.log (n.factorial:ℝ)) := by
  have h := factor_le_exp E (fun _ => C*L) hZ
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    add_comm,mul_left_comm,mul_assoc] using h

theorem factor_le_exp_of_count_bound {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hZ : ∀i,Real.exp (-(C*L)) ≤ primeShellMass (E i)) (N : ℕ) (hn : n ≤ N) :
    (n.factorial:ℝ)*normalization E ≤ Real.exp (C*(N:ℝ)*L+Real.log (N.factorial:ℝ)) := by
  apply (factor_le_exp_uniform E C L hZ).trans
  apply Real.exp_le_exp.mpr
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hC) hL
  · exact Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.factorial_le hn)

end Ostmann.Characters.PivotProductNormalization

end

end OAI
