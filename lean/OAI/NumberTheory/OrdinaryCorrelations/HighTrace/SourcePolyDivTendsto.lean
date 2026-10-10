import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceSystem

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open Finset Classical Filter

lemma source_poly_div_tendsto (n : ℕ) :
    Tendsto (fun B : ℝ => B^n / sourceMinPrime B) atTop (nhds 0) := by
  have hr : 0 < (1-epsilon) := by norm_num [epsilon]
  have hrne : (1-epsilon) ≠ 0 := hr.ne'
  have hlim := ((isLittleO_rpow_exp_atTop ((n : ℝ)/(1-epsilon))).tendsto_div_nhds_zero).comp
    (tendsto_rpow_atTop hr)
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
  change (B^(1-epsilon))^((n : ℝ)/(1-epsilon)) / Real.exp (B^(1-epsilon)) = _
  rw [← Real.rpow_mul hB]
  have he : (1-epsilon)*((n : ℝ)/(1-epsilon)) = (n : ℝ) := by field_simp
  rw [he, Real.rpow_natCast]
  rfl

lemma sourceMinPrime_tendsto : Tendsto sourceMinPrime atTop atTop :=
  Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num [epsilon]))

theorem source_eventually_large (h : ℕ) :
    ∀ᶠ B : ℝ in atTop, 1 ≤ B ∧ ∀ p : (sourceSystem B).Index,
      2 * (sourceLength B + 1) ≤ (p : ℕ) ∧ h < (p : ℕ) := by
  have hratio : ∀ᶠ B : ℝ in atTop, B / sourceMinPrime B < (1/6 : ℝ) := by
    simpa only [pow_one] using
      (source_poly_div_tendsto 1).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/6))
  filter_upwards [eventually_ge_atTop (1 : ℝ), hratio,
    sourceMinPrime_tendsto.eventually (eventually_ge_atTop ((h : ℝ)+1))] with B hB hratio hh
  refine ⟨hB, fun p => ?_⟩
  have hp := source_prime_lower B hB p
  have hP := (div_lt_iff₀ (Real.exp_pos _)).mp hratio
  change B < 1/6 * sourceMinPrime B at hP
  have hℓ := sourceLength_le B (by linarith)
  constructor
  · have : (2 : ℝ) * ((sourceLength B : ℝ)+1) ≤ (p : ℝ) := by linarith
    exact_mod_cast this
  · have : (h : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast this

theorem source_assigned_kernel_uniform (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ)
    (hτ : 0 ≤ τ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
    ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (w : ClosedLine h (sourceLength B)),
    (∀ i, w.label i ∈ D.members) →
    ∀ {T : ℝ} (cut : (sourceSystem B).Cutoffs T)
      (𝔏 : List (AttachedSpec w D (pathLength B))),
    𝔏.length < listCutoff B →
    ∀ (E : (sourceSystem B).Index → Finset (Fin (sourceLength B))),
    (∀ p, E p ⊆ treeOccurrences w p) →
    ∀ (group : (sourceSystem B).FixedResidues w → Prop),
    (∀ a, group a → ∀ p : (sourceSystem B).FixedIndex w,
      litEdges w p.val (a p) = E p.val) →
    assignedKernelIntegral w cut 𝔏 group ≤
      chargeConstant (S := sourceSystem B) w T (recordU w E) *
      Real.exp (-(sourceSystem B).harmonicCore * bandDefect w betaC -
        (sourceSystem B).harmonicCenter * bandDefect w betaZ +
        (sourceSystem B).harmonicCore * betaC * (Real.exp kappa - 1) * (recordU w E).card +
        sourceErrorBound h τ C₀ B) *
      ∏ p : (sourceSystem B).Index, tokenPrimeFactor w 𝔏 E p := by
  filter_upwards [source_eventually_large h] with B hB
  intro D w hlabels T cut 𝔏 ht E hE group hgroup
  have he := restorationError_source_bound w 𝔏 hlabels hB.1 hC₀ hτ
    (sourceLength_le B (by linarith [hB.1])) (pathLength_le B hB.1)
    ((by exact_mod_cast ht.le : (𝔏.length : ℝ) ≤ (listCutoff B : ℝ)).trans (listCutoff_le B hB.1))
    (fun p => (source_prime_lower B hB.1 p).le)
  apply (assignedKernelIntegral_restored w hh cut 𝔏 E hE group hgroup (fun p => (hB.2 p).1)).trans
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg (fun p _ => tokenPrimeFactor_nonneg w 𝔏 E p))
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  linarith only [he]

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
