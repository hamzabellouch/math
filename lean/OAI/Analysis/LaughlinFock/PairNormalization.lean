import Mathlib
import OAI.Analysis.LaughlinFock.Model

namespace OAI

/-! Pair Normalization. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
private def euler (P : ℝ[X]) : ℝ[X] := X * derivative P
private def variance (P : ℝ[X]) : ℝ[X] := euler (euler P) * P - (euler P)^2
private theorem coeff_euler (P : ℝ[X]) (n : ℕ) :
    (euler P).coeff n = (n : ℝ) * P.coeff n := by
  cases n with
  | zero => simp [euler]
  | succ n => simp [euler, coeff_derivative, mul_comm]
private theorem euler_mul (P R : ℝ[X]) :
    euler (P * R) = euler P * R + P * euler R := by
  simp only [euler, derivative_mul]
  ring
private theorem euler_add (P R : ℝ[X]) : euler (P + R) = euler P + euler R := by
  simp [euler, mul_add]
private theorem variance_mul (P R : ℝ[X]) :
    variance (P * R) = P^2 * variance R + R^2 * variance P := by
  simp only [variance, euler_mul, euler_add]
  ring
private theorem variance_X_add_one : variance (X + 1) = X := by
  simp [variance, euler]
  ring
private theorem variance_X_add_one_pow (n : ℕ) :
    variance ((X + 1)^(n+1)) = C ((n+1 : ℕ) : ℝ) * X * ((X+1)^n)^2 := by
  induction n with
  | zero => simp [variance_X_add_one]
  | succ n ih =>
    rw [pow_succ (X + 1) (n + 1), variance_mul, variance_X_add_one, ih]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

private theorem weighted_antidiagonal (P : ℝ[X]) (n : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((ij.1 : ℝ) - (ij.2 : ℝ))^2 * P.coeff ij.1 * P.coeff ij.2) =
      2 * (variance P).coeff n := by
  have hswap : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      (ij.2 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 := by
    rw [← Finset.Nat.sum_antidiagonal_swap (f := fun ij =>
      (ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2)]
    apply Finset.sum_congr rfl
    intro ij _
    dsimp only [Prod.swap]
    ring
  calc
    _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 +
       (ij.2 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 -
       2 * ((ij.1 : ℝ) * P.coeff ij.1 * ((ij.2 : ℝ) * P.coeff ij.2))) := by
      apply Finset.sum_congr rfl
      intro ij _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        variance, coeff_sub, pow_two, coeff_mul, coeff_euler]
      simp only [pow_two] at hswap
      rw [hswap]
      have hh : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (ij.1 : ℝ) * ((ij.1 : ℝ) * P.coeff ij.1) * P.coeff ij.2) =
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (ij.1 : ℝ)^2 * P.coeff ij.1 * P.coeff ij.2 := by
        apply Finset.sum_congr rfl
        intro ij _
        ring
      simp only [pow_two] at hh
      rw [hh]
      ring

 
theorem pair_binomial_identity (Q p : ℕ) (hQ : 1 ≤ Q) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p+1),
      ((ij.1 : ℝ) - (ij.2 : ℝ))^2 * (Q.choose ij.1 : ℝ) * (Q.choose ij.2 : ℝ)) =
      2 * (Q : ℝ) * ((2*Q-2).choose p : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, Q = n+1 := ⟨Q-1, by omega⟩
  have h := weighted_antidiagonal ((X+1)^(n+1)) (p+1)
  rw [variance_X_add_one_pow] at h
  simp only [coeff_X_add_one_pow, mul_assoc, coeff_C_mul, coeff_X_mul] at h
  rw [← pow_mul, coeff_X_add_one_pow] at h
  have he : 2*(n+1)-2 = n*2 := by omega
  rw [he]
  simpa only [mul_assoc] using h

 
theorem pairCoefficient_sq (Q p : ℕ) (i j : Orbital Q)
    (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    pairCoefficient Q p i j ^ 2 =
      if i.val + j.val = p+1 then
        ((i.val : ℝ) - (j.val : ℝ))^2 * (Q.choose i.val : ℝ) *
          (Q.choose j.val : ℝ) / ((Q : ℝ) * ((2*Q-2).choose p : ℝ))
      else 0 := by
  rw [pairCoefficient_eq]
  split_ifs
  · rw [mul_pow, Real.sq_sqrt (by positivity)]
    simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    have hp' : ((2*Q-2).choose p : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
    have hi : (i.val.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    have hj : (j.val.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
    have hf : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
    field_simp
  · simp

private theorem orbital_sum_eq_antidiagonal (Q p : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ i j, Q < i ∨ Q < j → f i j = 0) :
    (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i.val + j.val = p+1 then f i.val j.val else 0) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (p+1), f ij.1 ij.2 := by
  classical
  have hi (i : Orbital Q) : (∑ j : Orbital Q,
      if i.val + j.val = p+1 then f i.val j.val else 0) =
      ∑ j ∈ Finset.range (Q+1), if i.val+j=p+1 then f i.val j else 0 :=
    Fin.sum_univ_eq_sum_range (fun j => if i.val+j=p+1 then f i.val j else 0) _
  simp_rw [hi]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => ∑ j ∈ Finset.range (Q+1), if i+j=p+1 then f i j else 0) (Q+1)]
  rw [← Finset.sum_product (Finset.range (Q+1)) (Finset.range (Q+1))
    (fun ij : ℕ × ℕ => if ij.1+ij.2=p+1 then f ij.1 ij.2 else 0),
    ← Finset.sum_filter (fun ij : ℕ × ℕ => ij.1+ij.2=p+1) (fun ij => f ij.1 ij.2)]
  have hs : ((Finset.range (Q+1) ×ˢ Finset.range (Q+1)).filter
      (fun ij : ℕ × ℕ => ij.1 + ij.2 = p+1)) =
      (Finset.HasAntidiagonal.antidiagonal (p+1)).filter
        (fun ij : ℕ × ℕ => ij.1 ≤ Q ∧ ij.2 ≤ Q) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.HasAntidiagonal.mem_antidiagonal, Nat.lt_succ_iff]
    tauto
  rw [hs]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ij hij hn
  have hn' : ¬ (ij.1 ≤ Q ∧ ij.2 ≤ Q) := by
    simpa only [Finset.mem_filter, hij, true_and] using hn
  exact hf _ _ (by omega)

 
theorem pairCoefficient_ordered_norm (Q p : ℕ) (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) :
    (∑ i : Orbital Q, ∑ j : Orbital Q, pairCoefficient Q p i j ^ 2) = 2 := by
  have hsum := orbital_sum_eq_antidiagonal Q p
    (fun i j => ((i : ℝ) - (j : ℝ))^2 * (Q.choose i : ℝ) * (Q.choose j : ℝ))
    (by
      intro i j hij
      rcases hij with hi | hj
      · simp [Nat.choose_eq_zero_of_lt hi]
      · simp [Nat.choose_eq_zero_of_lt hj])
  rw [pair_binomial_identity Q p hQ] at hsum
  have hq : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hc : ((2*Q-2).choose p : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hp))
  calc
    _ = (∑ i : Orbital Q, ∑ j : Orbital Q,
        if i.val+j.val = p+1 then
          ((i.val : ℝ) - (j.val : ℝ))^2 * (Q.choose i.val : ℝ) * (Q.choose j.val : ℝ)
        else 0) / ((Q : ℝ) * ((2*Q-2).choose p : ℝ)) := by
      simp only [Finset.sum_div, ite_div, zero_div, pairCoefficient_sq Q p _ _ hQ hp]
    _ = _ := by rw [hsum]; field_simp

private theorem sum_eq_twice_upper {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hsymm : ∀ i j, f j i = f i j) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * ∑ i, ∑ j, if i < j then f i j else 0 := by
  have hterm : ∀ i j, f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, not_lt.mpr hij.le]
    · subst j; simp [hdiag]
    · simp [hij, not_lt.mpr hij.le, hsymm]
  calc
    _ = ∑ i, ∑ j,
        ((if i < j then f i j else 0) + (if j < i then f j i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hterm i j
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        ∑ i, ∑ j, if j < i then f j i else 0 := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
      ring

 

theorem pairCoefficient_norm (Q p : ℕ) (hQ : 1 ≤ Q) (hp : p ≤ 2*Q-2) :
    (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i < j then pairCoefficient Q p i j ^ 2 else 0) = 1 := by
  have hs := sum_eq_twice_upper (fun i j : Orbital Q => pairCoefficient Q p i j^2)
    (by
      intro i j
      rw [pairCoefficient_sq Q p j i hQ hp, pairCoefficient_sq Q p i j hQ hp]
      by_cases h : i.val+j.val = p+1
      · have h' : j.val+i.val=p+1 := by omega
        simp only [h, h', ite_true]
        ring
      · have h' : j.val+i.val≠p+1 := by omega
        simp only [h, h', ite_false])
    (by intro i; simp [pairCoefficient_eq])
  rw [pairCoefficient_ordered_norm Q p hQ hp] at hs
  linarith

 

theorem pairCoefficient_orthogonal (Q p r : ℕ) (hpr : p ≠ r) :
    (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i < j then pairCoefficient Q p i j * pairCoefficient Q r i j else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  split_ifs
  · rw [pairCoefficient_eq, pairCoefficient_eq]
    split_ifs <;> first | omega | simp
  · rfl
end LaughlinFock
end

end OAI
