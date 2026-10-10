import Mathlib
import OAI.Probability.Perceptron.Variational.VarianceProdMemLp
import OAI.Probability.Perceptron.Variational.EnrichedMoments
import OAI.Probability.Perceptron.Cascade.CascadeParameters
import OAI.Probability.Perceptron.Variational.GaussianLinearStability

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma enrichedTerminal_parameters_measurable (n M : ℕ) (f : ℝ →ᵇ ℝ)
    (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (htop : ℝ) :
    Measurable (fun a : (Fin M → Fin (n+1) → ℝ) × EnrichedMark (n+1) (n+1) p =>
      enrichedTerminal n M f a.1 p u htop a.2) := by
  let V := fun x : NormalizedSpin (n+1) => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)
  have hV : Continuous V := (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  have hW := normalizedPatternEnergy_continuous (n+1) M f
  have hm : Measurable (fun a : ((Fin M → Fin (n+1) → ℝ) × EnrichedMark (n+1) (n+1) p) × NormalizedSpin (n+1) =>
      Real.exp (normalizedPatternEnergy (n+1) M f a.1.1 a.2+V a.2 a.1.2)) :=
    ((hW.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).add
      ((hV.comp continuous_snd).clm_apply (continuous_snd.comp continuous_fst))).rexp.measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.log.sub_const _

lemma enrichedCascadeLog_parameters_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) :
    Measurable (fun a : (Fin M → Fin (n+1) → ℝ) ×
        (EnrichedMark (n+1) (n+1) p × DecoratedCascade (EnrichedMark (n+1) (n+1) p) k) =>
      enrichedCascadeLog n M k f a.1 p d u h a.2) := by
  have hh := gaussianLinearCascadeLog_parameter_measurable
    (P := Fin M → Fin (n+1) → ℝ) (E := EnrichedMark (n+1) (n+1) p)
    (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (H := fun g => enrichedTerminal n M f g p u (h (Fin.last k)))
    (enrichedTerminal_parameters_measurable n M f p u (h (Fin.last k))) k z
  simpa only [enrichedCascadeLog,gaussianLinearCascadeLog] using hh

def enrichedExpectedLog (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (g : Fin M → Fin (n+1) → ℝ) : ℝ :=
  ∫ a, enrichedCascadeLog n M k f g p d u h a ∂enrichedDisorderLaw n k p z

lemma enrichedExpectedLog_measurable (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ) :
    Measurable (enrichedExpectedLog n M k f p d u h z) :=
  (enrichedCascadeLog_parameters_measurable n M k f p d u h z).stronglyMeasurable.integral_prod_right'.measurable

lemma enrichedTerminal_pattern_change (n M M' : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (g' : Fin M' → Fin (n+1) → ℝ)
    (p : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (htop : ℝ) {C : ℝ}
    (hC : ∀ x, |normalizedPatternEnergy (n+1) M f g x-
      normalizedPatternEnergy (n+1) M' f g' x| ≤ C)
    (a : EnrichedMark (n+1) (n+1) p) :
    |enrichedTerminal n M f g p u htop a-enrichedTerminal n M' f g' p u htop a| ≤ C := by
  have hW (M : ℕ) (g : Fin M → Fin (n+1) → ℝ) :
      Continuous (normalizedPatternEnergy (n+1) M f g) :=
    (normalizedPatternEnergy_continuous (n+1) M f).comp (continuous_const.prodMk continuous_id)
  have hV : Continuous (fun x : NormalizedSpin (n+1) => innerSL ℝ (sourceEnrichedFeature (n+1) p u x)) :=
    (innerSL ℝ).continuous.comp (enrichedFeature_continuous _ _ _ _ _)
  simp only [enrichedTerminal,sub_sub_sub_cancel_right]
  exact vectorLogPartition_data_bound (unitSphereLaw (n+1)) (hW M g).measurable (hW M' g').measurable
    hV.measurable (normalizedPatternEnergy_bound _ _ _ _) (normalizedPatternEnergy_bound _ _ _ _)
    (C := enrichedFeatureBound (n+1) u)
    (fun x => by rw [innerSL_apply_norm,sourceEnrichedFeature_norm]) hC a

lemma enrichedExpectedLog_pattern_change (n M M' k : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin (n+1) → ℝ) (g' : Fin M' → Fin (n+1) → ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) {C : ℝ}
    (hC : ∀ x, |normalizedPatternEnergy (n+1) M f g x-
      normalizedPatternEnergy (n+1) M' f g' x| ≤ C) :
    |enrichedExpectedLog n M k f p d u h z g-enrichedExpectedLog n M' k f p d u h z g'| ≤ C :=
  gaussianLinearCascadeLog_mean_difference (enrichedIncrementMap p d h) (enrichedRootMap p d h)
    (enrichedTerminal_lipschitz n M f g p u _) (enrichedTerminal_lipschitz n M' f g' p u _)
    (enrichedTerminal_pattern_change n M M' f g g' p u _ hC) k z hz hz0 hz1

lemma normalizedPatternEnergy_update (N M : ℕ) (f : ℝ →ᵇ ℝ)
    (g : Fin M → Fin N → ℝ) (a : Fin M) (v : Fin N → ℝ) (x : NormalizedSpin N) :
    |normalizedPatternEnergy N M f (Function.update g a v) x-normalizedPatternEnergy N M f g x| ≤ 2*‖f‖ := by
  classical
  unfold normalizedPatternEnergy
  rw [← Finset.sum_sub_distrib]
  have he : (∑ b : Fin M, (f (∑ i, (Function.update g a v) b i*x.val i)-f (∑ i, g b i*x.val i)))=
      f (∑ i, v i*x.val i)-f (∑ i, g a i*x.val i) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Function.update_of_ne hb]
    · simp
  rw [he]
  exact (abs_sub _ _).trans (by
    have hb := f.norm_coe_le_norm (∑ i, v i*x.val i)
    have ha := f.norm_coe_le_norm (∑ i, g a i*x.val i)
    simp only [Real.norm_eq_abs] at hb ha
    linarith)

lemma enrichedExpectedLog_update (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (g : Fin M → Fin (n+1) → ℝ) (a : Fin M) (v : Fin (n+1) → ℝ) :
    |enrichedExpectedLog n M k f p d u h z (Function.update g a v)-
      enrichedExpectedLog n M k f p d u h z g| ≤ 2*‖f‖ :=
  enrichedExpectedLog_pattern_change n M M k f _ _ p d u h z hz hz0 hz1
    (normalizedPatternEnergy_update (n+1) M f g a v)

lemma enrichedExpectedLog_bounded (n M k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1) → ℕ) (u : Fin (n+1) → ℝ) (h : Fin (k+1) → ℝ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    ∃ C : ℝ, ∀ g, |enrichedExpectedLog n M k f p d u h z g| ≤ C := by
  refine ⟨|enrichedExpectedLog n M k f p d u h z 0|+2*(M:ℝ)*‖f‖,fun g => ?_⟩
  have hh := enrichedExpectedLog_pattern_change n M M k f g 0 p d u h z hz hz0 hz1
    (C := 2*(M:ℝ)*‖f‖) (fun x => (abs_sub _ _).trans (by
      have h1 := normalizedPatternEnergy_bound (n+1) M f g x
      have h0 := normalizedPatternEnergy_bound (n+1) M f 0 x
      linarith))
  have ht := abs_sub_le (enrichedExpectedLog n M k f p d u h z g)
    (enrichedExpectedLog n M k f p d u h z 0) 0
  simp only [sub_zero] at ht
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
