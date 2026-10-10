import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoefficientContinuity

namespace OAI

/-! # Uniform polynomial growth over compact coefficient families -/

noncomputable section
namespace PolycyclicRecognition

open MvPolynomial Set
open scoped BigOperators

theorem finite_bounded_exponents (m D : ℕ) :
    {s : Fin m →₀ ℕ | ∀ i, s i ≤ D}.Finite :=
  ((Set.Finite.pi' (fun _ : Fin m => Set.finite_le_nat D)).preimage
    DFunLike.coe_injective.injOn)

theorem norm_monomial_value_le {m D : ℕ} (s : Fin m →₀ ℕ)
    (hs : ∀ i, s i ≤ D) (x : Fin m → ℝ) :
    |∏ i, x i ^ s i| ≤ (1 + ‖x‖) ^ (m * D) := by
  rw [Finset.abs_prod]
  calc
    ∏ i, |x i ^ s i| ≤ ∏ _i : Fin m, (1 + ‖x‖) ^ D := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i _
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) ((norm_le_pi_norm x i).trans
        (by linarith [norm_nonneg x])) _).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg x]) (hs i))
    _ = (1 + ‖x‖) ^ (m * D) := by simp [← pow_mul, Nat.mul_comm]

theorem polynomial_support_subset_bounded_exponents {m D : ℕ}
    (p : MvPolynomial (Fin m) ℝ) (hp : p.totalDegree ≤ D) :
    p.support ⊆ (finite_bounded_exponents m D).toFinset := by
  intro s hs
  simp only [Finite.mem_toFinset]
  intro i
  exact ((le_degreeOf_of_mem_support i hs).trans (degreeOf_le_totalDegree _ i)).trans hp

theorem continuous_polynomial_evaluation_of_coefficients
    {P : Type*} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (hc : ∀ s, Continuous (fun a => (p a).coeff s)) (x : Fin m → ℝ) :
    Continuous (fun a => eval x (p a)) := by
  classical
  let T := (finite_bounded_exponents m D).toFinset
  have he (a : P) : eval x (p a) = ∑ s ∈ T, (p a).coeff s * ∏ i, x i ^ s i := by
    rw [eval_eq']
    apply Finset.sum_subset (polynomial_support_subset_bounded_exponents (p a) (hD a))
    intro s _ hs
    have hz : (p a).coeff s = 0 := notMem_support_iff.mp hs
    rw [hz, zero_mul]
  simp_rw [he]
  exact continuous_finsetSum _ (fun s _ => (hc s).mul continuous_const)

theorem exists_uniform_polynomial_growth
    {P : Type*} [TopologicalSpace P] {m : ℕ}
    (p : P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ a, (p a).totalDegree ≤ D)
    (heval : ∀ x : Fin m → ℝ, Continuous (fun a => eval x (p a)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ S, ∀ x : Fin m → ℝ,
      |eval x (p a)| ≤ C * (1 + ‖x‖) ^ (m * D) := by
  classical
  let T := (finite_bounded_exponents m D).toFinset
  have hb (s : Fin m →₀ ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ S, |(p a).coeff s| ≤ B := by
    obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
      (continuous_polynomial_coefficients p D hD heval s).continuousOn
    exact ⟨max B 0, le_max_right _ _, fun a ha => (hB a ha).trans (le_max_left _ _)⟩
  choose B hB hbound using hb
  let C := max 1 (∑ s ∈ T, B s)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a ha x
  have hsub : (p a).support ⊆ T :=
    polynomial_support_subset_bounded_exponents (p a) (hD a)
  rw [eval_eq']
  calc
    |∑ s ∈ (p a).support, (p a).coeff s * ∏ i, x i ^ s i| ≤
        ∑ s ∈ (p a).support, |(p a).coeff s * ∏ i, x i ^ s i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (p a).support, B s * (1 + ‖x‖) ^ (m * D) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul]
      apply mul_le_mul (hbound s a ha) (norm_monomial_value_le s ?_ x) (abs_nonneg _) (hB s)
      intro i
      exact ((le_degreeOf_of_mem_support i hs).trans (degreeOf_le_totalDegree _ i)).trans (hD a)
    _ ≤ ∑ s ∈ T, B s * (1 + ‖x‖) ^ (m * D) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ =>
        mul_nonneg (hB s) (pow_nonneg (by linarith [norm_nonneg x]) _))
    _ = (∑ s ∈ T, B s) * (1 + ‖x‖) ^ (m * D) := by rw [Finset.sum_mul]
    _ ≤ C * (1 + ‖x‖) ^ (m * D) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith [norm_nonneg x]) _)

theorem exists_uniform_finite_polynomial_growth
    {P J : Type*} [TopologicalSpace P] [Fintype J] {m : ℕ}
    (p : J → P → MvPolynomial (Fin m) ℝ) (D : ℕ)
    (hD : ∀ j a, (p j a).totalDegree ≤ D)
    (heval : ∀ j (x : Fin m → ℝ), Continuous (fun a => eval x (p j a)))
    (S : Set P) (hS : IsCompact S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j a, a ∈ S → ∀ x : Fin m → ℝ,
      |eval x (p j a)| ≤ C * (1 + ‖x‖) ^ (m * D) := by
  choose C hC hb using (fun j => exists_uniform_polynomial_growth (p j) D (hD j) (heval j) S hS)
  have hC0 : ∀ i, 0 ≤ C i := fun i => (hC i).trans' zero_le_one
  refine ⟨1 + ∑ j, C j, le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hC0 i)), ?_⟩
  intro j a ha x
  apply (hb j a ha x).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith [norm_nonneg x]) _)
  have hj := Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ j)
  linarith

end PolycyclicRecognition

end

end OAI
