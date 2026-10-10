import OAI.NumberTheory.JointDickman.Probability.ArithmeticKernelMass

namespace OAI

/-! # Finite sets of actual lag correlations are controlled by their mass -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def arithmeticKernelMass (B L : ℕ) (τ C : ℝ) (T N : ℕ) (j : ℤ) : ℝ :=
  (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
    rawArithmeticGraphKernel B L τ C T N j n)/((B : ℝ)*T*N)

noncomputable def kernelLagCorrelation (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (j : ℤ) (F : ℕ → ℂ) : ℝ :=
  (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
    rawArithmeticGraphKernel B L τ C T N j n * (star (F n)*F ((n : ℤ)+j).toNat).re) /
      ((B : ℝ)*T*N)

theorem kernelLagCorrelation_abs (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (j : ℤ) (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 2) :
    |kernelLagCorrelation B L τ C T N j F| ≤ 4*arithmeticKernelMass B L τ C T N j := by
  have hpair (n : ℕ) : |(star (F n)*F ((n : ℤ)+j).toNat).re| ≤ 4 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul, norm_star]
    have h := mul_le_mul (hF n) (hF ((n : ℤ)+j).toNat) (norm_nonneg _) (by norm_num)
    norm_num at h
    exact h
  have hs : |∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
      rawArithmeticGraphKernel B L τ C T N j n * (star (F n)*F ((n : ℤ)+j).toNat).re| ≤
      4*∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N), rawArithmeticGraphKernel B L τ C T N j n := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [abs_mul, abs_of_nonneg (rawArithmeticGraphKernel_nonneg B L τ C T N j n)]
    exact (mul_le_mul_of_nonneg_left (hpair n)
      (rawArithmeticGraphKernel_nonneg B L τ C T N j n)).trans_eq (mul_comm _ _)
  unfold kernelLagCorrelation arithmeticKernelMass
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (B : ℝ)*T*N)]
  convert div_le_div_of_nonneg_right hs (by positivity : 0 ≤ (B : ℝ)*T*N) using 1; ring

theorem finite_kernelLagCorrelation_absolute_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ J : Finset ℤ, (∀ j ∈ J, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
        (∑ j ∈ J, |kernelLagCorrelation B L τ C T N j F|) ≤
          (4*K/(T : ℝ))*(∑ j ∈ J, singularFactor 24 j.natAbs)+ε := by
  classical
  obtain ⟨K,hK,hbound⟩ := arithmeticKernelMass_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs J hJ ε hε
  let δ : ℝ := ε/(4*((J.card : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hall : ∀ᶠ N : ℕ in atTop, ∀ j ∈ J, ∀ L : ℕ, ∀ τ C : ℝ,
      arithmeticKernelMass B L τ C T N j ≤ K*singularFactor 24 j.natAbs/(T : ℝ)+δ := by
    apply (eventually_all_finset J).mpr
    intro j hj
    exact hB T j hT hTs (hJ j hj).1 (hJ j hj).2 δ hδ
  filter_upwards [hall] with N hN
  intro L τ C F hF
  have herr : 4*(J.card : ℝ)*δ ≤ ε := by
    have hc : (J.card : ℝ) ≤ (J.card : ℝ)+1 := by linarith
    calc
      _ ≤ 4*((J.card : ℝ)+1)*δ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (by norm_num)) hδ.le
      _ = ε := by dsimp [δ]; field_simp
  calc
    _ ≤ ∑ j ∈ J, 4*(K*singularFactor 24 j.natAbs/(T : ℝ)+δ) := by
      apply sum_le_sum
      intro j hj
      exact (kernelLagCorrelation_abs B L τ C T N j F hF).trans
        (mul_le_mul_of_nonneg_left (hN j hj L τ C) (by norm_num))
    _ = (4*K/(T : ℝ))*(∑ j ∈ J, singularFactor 24 j.natAbs)+4*(J.card : ℝ)*δ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul]
      rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro j _
        ring
      · ring
    _ ≤ _ := by linarith only [herr]

theorem finite_kernelLagCorrelation_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ J : Finset ℤ, (∀ j ∈ J, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
        |∑ j ∈ J, kernelLagCorrelation B L τ C T N j F| ≤
          (4*K/(T : ℝ))*(∑ j ∈ J, singularFactor 24 j.natAbs)+ε := by
  obtain ⟨K,hK,hbound⟩ := finite_kernelLagCorrelation_absolute_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs J hJ ε hε
  filter_upwards [hB T hT hTs J hJ ε hε] with N hN
  intro L τ C F hF
  exact (abs_sum_le_sum_abs _ _).trans (hN L τ C F hF)

end JointDickman

end OAI
