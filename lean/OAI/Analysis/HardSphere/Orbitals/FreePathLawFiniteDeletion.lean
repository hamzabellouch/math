import Mathlib
import OAI.Analysis.HardSphere.Geometry.SliceNormSq

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

instance freePathLaw_finite_deletion (N : ℕ) (L : Length) (t : ℝ) :
    IsFiniteMeasure (freePathLaw N L t) := by unfold freePathLaw; infer_instance
instance killedPathLaw_finite_deletion (N : ℕ) (L : Length) (a t : ℝ) :
    IsFiniteMeasure (killedPathLaw N L a t) := by unfold killedPathLaw; infer_instance

@[simp] lemma joinConfigurationPath_apply (m n : ℕ) (L : Length)
    (p : ConfigurationPath m L × ConfigurationPath n L) (t : Time) :
    joinConfigurationPath m n L p t=joinConfiguration m n L (p.1 t,p.2 t) := rfl

lemma selected_reversal_integral {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h)
    (hrev : ∀ ω, h (reverseConfigurationPath m L ω)=h ω) :
    (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 1)) ∂freePathLaw m L t)=
      ∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t := by
  have hmeas : Measurable (fun ω : ConfigurationPath m L ↦ h ω*ENNReal.ofReal (sliceNormSq u (ω 0))) :=
    hh.mul (((sliceNormSq_measurable u).comp (continuous_eval_const (0:Time)).measurable).ennreal_ofReal)
  simpa only [reverseConfigurationPath_apply,reverseTime_zero,hrev] using
    (reverse_freePath_preserving m L t).lintegral_comp hmeas

lemma deleted_path_integral_le {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (a t : ℝ)
    {h : ConfigurationPath m L → ℝ≥0∞} (hh : Measurable h)
    (hrev : ∀ ω, h (reverseConfigurationPath m L ω)=h ω) :
    (∫⁻ ω : ConfigurationPath (m+n) L,
      h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u (ω 0)‖*‖u (ω 1)‖)
      ∂killedPathLaw (m+n) L a t) ≤
      ENNReal.ofReal ‖killedTransition n L a t‖*
        ∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t := by
  let F : ConfigurationPath (m+n) L → ℝ≥0∞ := fun ω ↦
    h (splitConfigurationPath m n L ω).1*ENNReal.ofReal (‖u (ω 0)‖*‖u (ω 1)‖)
  let G : ConfigurationPath m L × ConfigurationPath n L → ℝ≥0∞ := fun p ↦
    h p.1*ENNReal.ofReal (‖u (joinConfiguration m n L (p.1 0,p.2 0))‖*
      ‖u (joinConfiguration m n L (p.1 1,p.2 1))‖)
  have hu := (Lp.stronglyMeasurable u).measurable
  have hF : Measurable F := by
    exact (hh.comp ((splitConfigurationPath_continuous m n L).measurable.fst)).mul
      (((hu.comp (continuous_eval_const (0:Time)).measurable).norm.mul
        (hu.comp (continuous_eval_const (1:Time)).measurable).norm).ennreal_ofReal)
  have hG : Measurable G := by
    simpa only [F,G,Function.comp_def,split_joinConfigurationPath,joinConfigurationPath_apply]
      using hF.comp (joinConfigurationPath_continuous m n L).measurable
  have hS0 : Measurable (fun ω : ConfigurationPath m L ↦ h ω*ENNReal.ofReal (sliceNormSq u (ω 0))) :=
    hh.mul (((sliceNormSq_measurable u).comp (continuous_eval_const (0:Time)).measurable).ennreal_ofReal)
  have hS1 : Measurable (fun ω : ConfigurationPath m L ↦ h ω*ENNReal.ofReal (sliceNormSq u (ω 1))) :=
    hh.mul (((sliceNormSq_measurable u).comp (continuous_eval_const (1:Time)).measurable).ennreal_ofReal)
  have hj := (joinConfigurationPath_preserving m n L t).restrict_preimage
    (staysAllowed_open (m+n) L a).measurableSet
  have hd : ((freePathLaw m L t).prod (freePathLaw n L t)).restrict
      (joinConfigurationPath m n L ⁻¹' staysAllowed (m+n) L a) ≤
      (freePathLaw m L t).prod (killedPathLaw n L a t) := by
    calc
      _ ≤ ((freePathLaw m L t).prod (freePathLaw n L t)).restrict
          (Set.univ ×ˢ staysAllowed n L a) :=
        Measure.restrict_mono_set _ fun p hp ↦
          ⟨mem_univ _,staysAllowed_join_subset_bath m n L a hp⟩
      _ = _ := by rw [← Measure.prod_restrict,Measure.restrict_univ]; rfl
  have hq := bath_slice_quadratic_ae u a t
  calc
    _ = ∫⁻ p, G p ∂((freePathLaw m L t).prod (freePathLaw n L t)).restrict
        (joinConfigurationPath m n L ⁻¹' staysAllowed (m+n) L a) := by
      symm
      simpa only [F,G,killedPathLaw,split_joinConfigurationPath,joinConfigurationPath_apply] using
        hj.lintegral_comp hF
    _ ≤ ∫⁻ p, G p ∂((freePathLaw m L t).prod (killedPathLaw n L a t)) :=
      lintegral_mono' hd le_rfl
    _ = ∫⁻ ω : ConfigurationPath m L, h ω*(∫⁻ η : ConfigurationPath n L,
        ENNReal.ofReal (‖u (joinConfiguration m n L (ω 0,η 0))‖*
          ‖u (joinConfiguration m n L (ω 1,η 1))‖) ∂killedPathLaw n L a t) ∂freePathLaw m L t := by
      rw [lintegral_prod _ hG.aemeasurable]
      apply lintegral_congr
      intro ω
      dsimp only [G]
      exact lintegral_const_mul _ (by
        apply Measurable.ennreal_ofReal
        apply Measurable.mul
        all_goals
          apply Measurable.norm
          apply hu.comp
          exact (joinConfiguration_continuous m n L).measurable.comp
            (measurable_const.prodMk (continuous_eval_const _).measurable))
    _ ≤ ∫⁻ ω : ConfigurationPath m L, h ω*(ENNReal.ofReal (‖killedTransition n L a t‖/2)*
        (ENNReal.ofReal (sliceNormSq u (ω 0))+ENNReal.ofReal (sliceNormSq u (ω 1)))) ∂freePathLaw m L t := by
      apply lintegral_mono_ae
      filter_upwards [hq] with ω hω
      exact mul_le_mul_right hω _
    _ = ENNReal.ofReal (‖killedTransition n L a t‖/2)*
        ((∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 0)) ∂freePathLaw m L t)+
         (∫⁻ ω : ConfigurationPath m L, h ω*ENNReal.ofReal (sliceNormSq u (ω 1)) ∂freePathLaw m L t)) := by
      calc
        _ = ∫⁻ ω : ConfigurationPath m L, ENNReal.ofReal (‖killedTransition n L a t‖/2)*
            (h ω*ENNReal.ofReal (sliceNormSq u (ω 0))+h ω*ENNReal.ofReal (sliceNormSq u (ω 1)))
            ∂freePathLaw m L t := by
          apply lintegral_congr
          intro ω
          rw [← mul_add,mul_left_comm]
        _ = _ := by
          calc
            _ = ENNReal.ofReal (‖killedTransition n L a t‖/2)*
                (∫⁻ ω : ConfigurationPath m L,
                  h ω*ENNReal.ofReal (sliceNormSq u (ω 0))+
                    h ω*ENNReal.ofReal (sliceNormSq u (ω 1)) ∂freePathLaw m L t) :=
              lintegral_const_mul _ (hS0.add hS1)
            _ = _ := by rw [lintegral_add_left hS0]
    _ = _ := by
      rw [selected_reversal_integral u t hh hrev,mul_add,← add_mul,
        ← ENNReal.ofReal_add (div_nonneg (norm_nonneg _) (by norm_num))
          (div_nonneg (norm_nonneg _) (by norm_num)),add_halves]
end
end HardSphere

end
end
end
end

end OAI
