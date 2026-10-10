import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-! # The algebraic Laplacian on twelve-dimensional polynomials

The radius-multiplication identity is the algebraic ingredient for reducing
sphere polynomial moments to homogeneous harmonic moments.
-/

open MvPolynomial

namespace DefocusingNLS

abbrev PhysicalRealPolynomial := MvPolynomial (Fin 12) ℝ

noncomputable def physicalPolynomialLaplacian :
    PhysicalRealPolynomial →ₗ[ℝ] PhysicalRealPolynomial :=
  ∑ i : Fin 12, (pderiv i).toLinearMap.comp (pderiv i).toLinearMap

noncomputable def physicalRadiusPolynomial : PhysicalRealPolynomial :=
  ∑ i : Fin 12, (X i) ^ 2

theorem physicalPolynomialLaplacian_apply (p : PhysicalRealPolynomial) :
    physicalPolynomialLaplacian p = ∑ i : Fin 12, pderiv i (pderiv i p) := by
  simp [physicalPolynomialLaplacian]

theorem pderiv_physicalRadiusPolynomial (i : Fin 12) :
    pderiv i physicalRadiusPolynomial = 2 * X i := by
  classical
  simp [physicalRadiusPolynomial, map_sum, pderiv_X, Pi.single_apply]

theorem physicalPolynomialLaplacian_radius :
    physicalPolynomialLaplacian physicalRadiusPolynomial = 24 := by
  have htwo (i : Fin 12) : pderiv i (2 : PhysicalRealPolynomial) = 0 := by
    simpa only [map_ofNat] using (pderiv_C (i := i) (a := (2 : ℝ)))
  rw [physicalPolynomialLaplacian_apply]
  simp [pderiv_physicalRadiusPolynomial, htwo]
  norm_num

theorem physicalRadiusPolynomial_homogeneous : physicalRadiusPolynomial.IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_X_pow i 2

theorem physicalPolynomialLaplacian_mul (p q : PhysicalRealPolynomial) :
    physicalPolynomialLaplacian (p * q) =
      physicalPolynomialLaplacian p * q + p * physicalPolynomialLaplacian q +
        2 * ∑ i : Fin 12, pderiv i p * pderiv i q := by
  simp only [physicalPolynomialLaplacian_apply]
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pderiv_mul, map_add]
  ring

theorem physicalPolynomialLaplacian_radius_mul (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) :
    physicalPolynomialLaplacian (physicalRadiusPolynomial * p) =
      physicalRadiusPolynomial * physicalPolynomialLaplacian p + (4 * n + 24) • p := by
  rw [physicalPolynomialLaplacian_mul, physicalPolynomialLaplacian_radius]
  have hcross : (∑ i : Fin 12, pderiv i physicalRadiusPolynomial * pderiv i p) =
      2 * (n • p) := by
    simp only [pderiv_physicalRadiusPolynomial, mul_assoc, ← Finset.mul_sum,
      hp.sum_X_mul_pderiv]
  rw [hcross]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem physicalPolynomialLaplacian_homogeneous (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) :
    (physicalPolynomialLaplacian p).IsHomogeneous (n - 2) := by
  rw [physicalPolynomialLaplacian_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  simpa only [Nat.sub_sub] using hp.pderiv.pderiv (i := i)

theorem physicalPolynomialLaplacian_radius_pow_mul (p : PhysicalRealPolynomial)
    (n j : ℕ) (hp : p.IsHomogeneous n) :
    physicalPolynomialLaplacian (physicalRadiusPolynomial ^ (j + 1) * p) =
      physicalRadiusPolynomial ^ (j + 1) * physicalPolynomialLaplacian p +
        (4 * (j + 1) * (n + j + 6)) • (physicalRadiusPolynomial ^ j * p) := by
  induction j with
  | zero =>
    simpa only [zero_add, add_zero, pow_one, pow_zero, one_mul,
      show 4 * 1 * (n + 0 + 6) = 4 * n + 24 by omega] using
      physicalPolynomialLaplacian_radius_mul p n hp
  | succ j ih =>
    have hp' : (physicalRadiusPolynomial ^ (j + 1) * p).IsHomogeneous
        (2 * (j + 1) + n) :=
      (physicalRadiusPolynomial_homogeneous.pow (j + 1)).mul hp
    calc
      _ = physicalPolynomialLaplacian
          (physicalRadiusPolynomial * (physicalRadiusPolynomial ^ (j + 1) * p)) := by
        rw [pow_succ']
        congr 1
        ring
      _ = physicalRadiusPolynomial *
          physicalPolynomialLaplacian (physicalRadiusPolynomial ^ (j + 1) * p) +
          (4 * (2 * (j + 1) + n) + 24) • (physicalRadiusPolynomial ^ (j + 1) * p) :=
        physicalPolynomialLaplacian_radius_mul _ _ hp'
      _ = _ := by
        rw [ih]
        simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        rw [pow_succ' physicalRadiusPolynomial j, pow_succ' physicalRadiusPolynomial (j + 1)]
        ring

theorem physicalPolynomialLaplacian_constant (p : PhysicalRealPolynomial)
    (hp : p.IsHomogeneous 0) : physicalPolynomialLaplacian p = 0 := by
  have he : p = C (p.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 12)).mpr hp)
  rw [he, physicalPolynomialLaplacian_apply]
  simp

theorem physicalPolynomialLaplacian_low_degree (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) (hn : n ≤ 1) :
    physicalPolynomialLaplacian p = 0 := by
  rw [physicalPolynomialLaplacian_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hd : (pderiv i p).IsHomogeneous 0 := by
    simpa only [Nat.sub_eq_zero_of_le hn] using hp.pderiv (i := i)
  have he : pderiv i p = C ((pderiv i p).coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 12)).mpr hd)
  rw [he, pderiv_C]

theorem physicalPolynomialLaplacian_iterate_homogeneous
    (p : PhysicalRealPolynomial) (n j : ℕ) (hp : p.IsHomogeneous n) :
    ((physicalPolynomialLaplacian^[j]) p).IsHomogeneous (n - 2 * j) := by
  induction j with
  | zero => simpa only [Function.iterate_zero_apply, Nat.mul_zero, Nat.sub_zero] using hp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h := physicalPolynomialLaplacian_homogeneous _ _ ih
    convert h using 1

theorem physicalPolynomialLaplacian_iterate_zero
    (p : PhysicalRealPolynomial) (n j : ℕ) (hp : p.IsHomogeneous n) (hj : n < 2 * j) :
    (physicalPolynomialLaplacian^[j]) p = 0 := by
  induction n using Nat.strong_induction_on generalizing p j with
  | h n ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [Function.iterate_succ_apply]
      by_cases hn : n ≤ 1
      · rw [physicalPolynomialLaplacian_low_degree p n hp hn]
        exact Function.iterate_fixed (map_zero physicalPolynomialLaplacian) j
      · exact ih (n - 2) (by omega) (physicalPolynomialLaplacian p) j
          (physicalPolynomialLaplacian_homogeneous p n hp) (by omega)

end DefocusingNLS

end OAI
