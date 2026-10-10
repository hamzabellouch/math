import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceCoreEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Shape

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter

lemma centerMass_tendsto : Tendsto SourcePrimeBands.centerMass atTop atTop := by
  have h := SourcePrimeBands.source_prime_bands.2.pos_mul_atTop
    (by norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon]) Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with B hB
  exact div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hB))

lemma source_center_eventually_one : ∀ᶠ B : ℝ in atTop, 1 ≤ (sourceSystem B).harmonicCenter := by
  simpa only [source_harmonicCenter] using centerMass_tendsto.eventually (eventually_ge_atTop (1 : ℝ))

lemma source_band_nonempty : ∀ᶠ B : ℝ in atTop,
    (∃ p : (sourceSystem B).Index, (sourceSystem B).IsCore p) ∧
    (∃ p : (sourceSystem B).Index, ¬(sourceSystem B).IsCore p) := by
  filter_upwards [source_core_eventually_one,source_center_eventually_one] with B hc hz
  have hcp : 0 < ∑ p : (sourceSystem B).CoreIndex, (p.val.val : ℝ)⁻¹ := lt_of_lt_of_le zero_lt_one hc
  have hzp : 0 < ∑ p : (sourceSystem B).CenterIndex, (p.val.val : ℝ)⁻¹ := lt_of_lt_of_le zero_lt_one hz
  have hc' := (sum_pos_iff_of_nonneg (s := univ)
    (fun (p : (sourceSystem B).CoreIndex) _ => inv_nonneg.mpr (Nat.cast_nonneg p.val.val))).mp hcp
  have hz' := (sum_pos_iff_of_nonneg (s := univ)
    (fun (p : (sourceSystem B).CenterIndex) _ => inv_nonneg.mpr (Nat.cast_nonneg p.val.val))).mp hzp
  obtain ⟨p,hp,hpv⟩ := hc'
  obtain ⟨q,hq,hqv⟩ := hz'
  exact ⟨⟨p.val,p.property⟩,⟨q.val,q.property⟩⟩

theorem source_untagged_exponential :
    ∀ᶠ B : ℝ in atTop, ∃ pC pZ : (sourceSystem B).Index,
      (sourceSystem B).IsCore pC ∧ ¬(sourceSystem B).IsCore pZ ∧
      ∀ (h ℓ : ℕ) (w : ClosedLine h ℓ), 0 < h → ∀ (N : TokenType w → ℕ),
        Real.exp (-(sourceSystem B).harmonicCore*bandDefect w betaC-
          (sourceSystem B).harmonicCenter*bandDefect w betaZ) *
          (∑ j : ∀ t : TokenType w, Fin (N t),
            ∏ t : TokenType w,
              (tokenMass w (sourceSystem B).harmonicCore (sourceSystem B).harmonicCenter t *
                tokenWeight w pC pZ t)^(j t).val / (j t).val.factorial) ≤
        B^(-(epsilon/10)*((goodEdges w).card : ℝ) + epsilon*(badEdges w).card) := by
  filter_upwards [source_band_nonempty,source_core_eventually_one,source_center_eventually_one,
    source_center_exponential] with B hne hc hz he
  obtain ⟨⟨pC,hpC⟩,⟨pZ,hpZ⟩⟩ := hne
  refine ⟨pC,pZ,hpC,hpZ,?_⟩
  intro h ℓ w hh N
  exact (untagged_exponential_bound w hh pC pZ hpC hpZ _ _
    (zero_le_one.trans hc) (zero_le_one.trans hz) N).trans (he _ _)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
