import OAI.NumberTheory.JointDickman.Probability.CandidateKernelMass

namespace OAI

/-! # A polynomial bound on the actual candidate fluctuation test -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem kernelCutNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ι → ℝ) :
    0 ≤ kernelCutNorm K := div_nonneg (kernelCutMaximum_nonneg K) (Nat.cast_nonneg _)

theorem kernel_difference_absolute_mass {ι : Type*} [Fintype ι] (K L : ι → ι → ℝ) :
    (∑ i, ∑ j, |K i j-L i j|) ≤ (∑ i, ∑ j, |K i j|)+(∑ i, ∑ j, |L i j|) := by
  simp only [← sum_add_distrib]
  exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => abs_sub (K i j) (L i j)))

theorem candidate_root_error_cap {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ), 0 < M → M ≤ B^2 →
      ∀ (S : Fin M → Finset ℕ) (χ : BlockCandidateIndex M → ℝ),
      (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) → ∀ R,
      |kernelCutNorm (fun i k => independentCandidateKernel B L T H M τ C S χ R i k-
        latentCandidateKernel B L T H M τ C S χ i k)| ≤ (B : ℝ)^10 := by
  filter_upwards [candidate_kernels_polynomial_mass hL hτ hτsmall,eventually_ge_atTop 2]
    with B hmass hB
  intro C T H M hM0 hM S χ hχ R
  obtain ⟨hlat,hind⟩ := hmass C T H M S χ hχ
  let K := fun i k => independentCandidateKernel B L T H M τ C S χ R i k-
    latentCandidateKernel B L T H M τ C S χ i k
  have habs : (∑ i, ∑ k, |K i k|) ≤ 4*(M : ℝ)^2*(B : ℝ)^2 :=
    (kernel_difference_absolute_mass _ _).trans (by linarith [hind R,hlat])
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM0
  have hm2 : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  have hb2 : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hb1 : (1 : ℝ) ≤ B := by linarith
  have hb4 : (4 : ℝ) ≤ (B : ℝ)^4 := by
    have hsq : (4 : ℝ) ≤ (B : ℝ)^2 := by nlinarith
    exact hsq.trans (pow_le_pow_right₀ hb1 (by norm_num : 2 ≤ 4))
  rw [abs_of_nonneg (kernelCutNorm_nonneg _)]
  calc
    kernelCutNorm K ≤ kernelAbsoluteMass K := kernelCutNorm_le_absolute_mass K
    _ ≤ (4*(M : ℝ)^2*(B : ℝ)^2)/(M : ℝ) := by
      simpa only [kernelAbsoluteMass,Fintype.card_fin] using
        div_le_div_of_nonneg_right habs (Nat.cast_nonneg M)
    _ ≤ 4*(M : ℝ)^2*(B : ℝ)^2 := div_le_self (by positivity) hm1
    _ ≤ 4*((B : ℝ)^2)^2*(B : ℝ)^2 := by gcongr
    _ = 4*(B : ℝ)^6 := by ring
    _ ≤ (B : ℝ)^4*(B : ℝ)^6 := mul_le_mul_of_nonneg_right hb4 (by positivity)
    _ = (B : ℝ)^10 := by ring

end JointDickman

end OAI
