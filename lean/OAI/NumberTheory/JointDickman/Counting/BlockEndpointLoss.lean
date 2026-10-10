import OAI.NumberTheory.JointDickman.Counting.ShortLagRemoval

namespace OAI

/-! # The endpoint cost of averaging the actual graph over finite blocks -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem kernelLagCorrelation_zero (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (F : ℕ → ℂ) : kernelLagCorrelation B L τ C T N 0 F = 0 := by
  simp [kernelLagCorrelation, rawArithmeticGraphKernel_zero_lag]

theorem graph_without_short_nonzero (B L : ℕ) (τ C : ℝ)
    (T N H : ℕ) (F : ℕ → ℂ) :
    graphEnergyWithoutShortLags B L τ C T N H F =
      ∑ j ∈ nonzeroShortLags T \ nonzeroShortLags H,
        kernelLagCorrelation B L τ C T N j F := by
  classical
  unfold graphEnergyWithoutShortLags nonzeroShortLags
  have he : (Icc (-(T : ℤ)) T \ (Icc (-(H : ℤ)) H).erase 0).erase 0 =
      (Icc (-(T : ℤ)) T).erase 0 \ (Icc (-(H : ℤ)) H).erase 0 := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_sdiff]
    tauto
  rw [← he, sum_erase_eq_sub]
  · simp [kernelLagCorrelation_zero]
  · simp

/-- The coefficient is precisely the fraction of origins retaining both endpoints. -/
noncomputable def blockWeightedGraphEnergy (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) : ℝ :=
  ∑ j ∈ nonzeroShortLags T \ nonzeroShortLags H,
    (1-(j.natAbs : ℝ)/M)*kernelLagCorrelation B L τ C T N j F

theorem block_endpoint_loss_le (B L : ℕ) (τ C : ℝ)
    (T N H M : ℕ) (F : ℕ → ℂ) :
    |graphEnergyWithoutShortLags B L τ C T N H F -
      blockWeightedGraphEnergy B L τ C T N H M F| ≤
        ((T : ℝ)/M)*(∑ j ∈ nonzeroShortLags T,
          |kernelLagCorrelation B L τ C T N j F|) := by
  rw [graph_without_short_nonzero]
  unfold blockWeightedGraphEnergy
  rw [← sum_sub_distrib]
  have he (j : ℤ) : kernelLagCorrelation B L τ C T N j F -
      (1-(j.natAbs : ℝ)/M)*kernelLagCorrelation B L τ C T N j F =
      ((j.natAbs : ℝ)/M)*kernelLagCorrelation B L τ C T N j F := by ring
  simp_rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ nonzeroShortLags T \ nonzeroShortLags H,
        ((T : ℝ)/M)*|kernelLagCorrelation B L τ C T N j F| := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j.natAbs : ℝ)/M)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
      exact_mod_cast (mem_nonzeroShortLags.mp (mem_sdiff.mp hj).1).2
    _ ≤ ∑ j ∈ nonzeroShortLags T,
        ((T : ℝ)/M)*|kernelLagCorrelation B L τ C T N j F| := by
      apply sum_le_sum_of_subset_of_nonneg sdiff_subset
      intro j _ _
      positivity
    _ = _ := (mul_sum ..).symm

theorem arithmetic_block_endpoint_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      T ≤ auxiliaryCutoff B → ∀ M : ℕ, T ≤ M →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ H L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 2) →
      |graphEnergyWithoutShortLags B L τ C T N H F -
        blockWeightedGraphEnergy B L τ C T N H M F| ≤ K*T/M+ε := by
  obtain ⟨K,hK,hbound⟩ := finite_kernelLagCorrelation_absolute_bound hFord hMertens
  refine ⟨8*K*Real.exp 24, by positivity, ?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs hTc M hTM ε hε
  have hJ : ∀ j ∈ nonzeroShortLags T, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B := by
    intro j hj
    have h := mem_nonzeroShortLags.mp hj
    exact ⟨h.1,h.2.trans hTc⟩
  filter_upwards [hB T hT hTs (nonzeroShortLags T) hJ ε hε] with N hN
  intro H L τ C F hF
  have hmass := hN L τ C F hF
  have hs := mul_le_mul_of_nonneg_left (shortLag_singular_sum T)
    (show 0 ≤ 4*K/(T : ℝ) by positivity)
  have he : (4*K/(T : ℝ))*((2*Real.exp 24)*(T : ℝ)) = 8*K*Real.exp 24 := by
    field_simp
    ring
  rw [he] at hs
  have hmass' : (∑ j ∈ nonzeroShortLags T,
      |kernelLagCorrelation B L τ C T N j F|) ≤ 8*K*Real.exp 24+ε := by
    linarith only [hmass,hs]
  have hratio : (T : ℝ)/M ≤ 1 := by
    apply (div_le_one (by exact_mod_cast hT.trans_le hTM : (0 : ℝ) < M)).mpr
    exact_mod_cast hTM
  calc
    _ ≤ ((T : ℝ)/M)*(∑ j ∈ nonzeroShortLags T,
        |kernelLagCorrelation B L τ C T N j F|) := block_endpoint_loss_le ..
    _ ≤ ((T : ℝ)/M)*(8*K*Real.exp 24+ε) :=
      mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ ≤ (8*K*Real.exp 24)*T/M+ε := by
      have hh := mul_le_mul_of_nonneg_right hratio hε.le
      calc
        _ = (8*K*Real.exp 24)*T/M+((T : ℝ)/M)*ε := by ring
        _ ≤ _ := by linarith only [hh]

end JointDickman

end OAI
