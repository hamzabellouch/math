import Mathlib.Data.Nat.GCD.BigOperators
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourier

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

/-- A bounded density product with its proved local-mean-zero consequence. -/
structure DensityCRTData (q : ℕ) [NeZero q] where
  value : ZMod q → ℂ
  norm_le_one : ∀ x, ‖value x‖ ≤ 1
  fourier_nonunit : ∀ x, ¬IsUnit x → densityFourier value x = 0

namespace DensityCRTData

noncomputable def one : DensityCRTData 1 where
  value := fun _ => 1
  norm_le_one := by intro x; simp
  fourier_nonunit := by
    intro x hx
    exact (hx (by have h : x = 1 := Subsingleton.elim _ _; rw [h]; exact isUnit_one)).elim

noncomputable def prime (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) : DensityCRTData p where
  value := fun x => (centeredDensity S x : ℂ)
  norm_le_one := by
    intro x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using centeredDensity_abs_le S x
  fourier_nonunit := densityFourier_centered_prime_nonunit S

noncomputable def mul {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (A : DensityCRTData m) (B : DensityCRTData n) : DensityCRTData (m * n) where
  value := fun x => A.value ((ZMod.chineseRemainder h) x).1 * B.value ((ZMod.chineseRemainder h) x).2
  norm_le_one := by
    intro x
    rw [norm_mul]
    exact (mul_le_mul (A.norm_le_one _) (B.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  fourier_nonunit := densityFourier_crt_nonunit h A.value B.value A.fourier_nonunit B.fourier_nonunit

end DensityCRTData

theorem prime_list_prod_pos (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime) : 0 < ps.prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.prod_cons]
    exact Nat.mul_pos (hp p (List.mem_cons_self)).pos (ih (fun q hq => hp q (List.mem_cons_of_mem p hq)))

/-- This is the actual product of the centered functions, formed by CRT
along the list of distinct prime factors. -/
noncomputable def densityCRTList (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) :
    @DensityCRTData ps.prod ⟨(prime_list_prod_pos ps hp).ne'⟩ := by
  cases ps with
  | nil => exact DensityCRTData.one
  | cons p ps =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : Fact p.Prime := ⟨hp p List.mem_cons_self⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    change DensityCRTData (p * ps.prod)
    exact DensityCRTData.mul (m := p) (n := ps.prod) (Nat.coprime_list_prod_right_iff.mpr hcp.1)
      (DensityCRTData.prime p (S p)) (densityCRTList ps hp' hcp.2 S)

theorem densityCRTList_intCast (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) (n : ℤ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (densityCRTList ps hp hc S).value (n : ZMod ps.prod) =
      (ps.map fun p => (centeredDensity (S p) (n : ZMod p) : ℂ)).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp' : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hcp := List.pairwise_cons.mp hc
    let : Fact p.Prime := ⟨hp p List.mem_cons_self⟩
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp').ne'⟩
    change (centeredDensity (S p)
      ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) (n : ZMod (p * ps.prod))).1 : ℂ) *
      (densityCRTList ps hp' hcp.2 S).value
        ((ZMod.chineseRemainder (Nat.coprime_list_prod_right_iff.mpr hcp.1)) (n : ZMod (p * ps.prod))).2 = _
    rw [map_intCast]
    change (centeredDensity (S p) (n : ZMod p) : ℂ) *
      (densityCRTList ps hp' hcp.2 S).value (n : ZMod ps.prod) = _
    rw [ih hp' hcp.2]
    rfl

/-- The hypotheses of the small-kernel bound hold for the original finite
product of centered density functions. -/
theorem densityCRTList_energy (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    (∑ a : ZMod ps.prod, ‖densityFourier (densityCRTList ps hp hc S).value a‖ ^ 2) ≤ ps.prod := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  exact densityFourier_energy_le _ (densityCRTList ps hp hc S).norm_le_one

/-- The manuscript's small-kernel bound with all density Fourier
hypotheses supplied by the original centered factors. -/
theorem densityCRT_small_quadratic_sum (ps : List ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (hc : ps.Pairwise Nat.Coprime) (S : ∀ p : ℕ, Finset (ZMod p))
    (W : ℕ) (a : ZMod ps.prod) (weight : ℕ → ℂ) (B C N : ℝ)
    (hB : 0 ≤ B) (hN : 0 < N) (hq : (ps.prod : ℝ) ≤ N)
    (hW : (W : ℝ) ≤ C * N) (hw : ∀ w ∈ Finset.Ioc 0 W, ‖weight w‖ ≤ B) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ‖(N : ℂ)⁻¹ * ∑ w ∈ Finset.Ioc 0 W,
      densityFourier (densityCRTList ps hp hc S).value (a * (w : ZMod ps.prod) ^ 2) * weight w‖ ≤
      B * (C + 1) * Real.sqrt ((2 : ℝ) ^ (ps.prod.primeFactors.card + 1)) := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  exact small_kernel_quadratic_sum_bound ps.prod W
    (densityFourier (densityCRTList ps hp hc S).value)
    (densityCRTList ps hp hc S).fourier_nonunit (densityCRTList_energy ps hp hc S)
    a weight B C N hB hN hq hW hw

end Ostmann

end OAI
