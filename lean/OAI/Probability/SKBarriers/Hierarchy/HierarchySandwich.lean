import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyExponentialMoment
import OAI.Probability.SKBarriers.Gaussian.GaussianStepSandwich

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem HasExpGrowth.integrable_hierarchyPathLaw (n : ℕ) (m : Fin n → ℝ)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : HasExpGrowth g)
    (hc : Continuous g) (x : ℝ) : Integrable g (hierarchyPathLaw n m f x) := by
  rw [hierarchyPathLaw_eq_tilted n m f hf x]
  exact hg.integrable_tilted_fiberGaussian n _ (hierarchyPathLogDensity_regular n m hf) hc x

theorem hierarchyAverage_mono_exp (n : ℕ) (m : Fin n → ℝ)
    {f g a : ParameterSpace n → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (ha : Continuous a) (hgE : HasExpGrowth g) (haE : HasExpGrowth a)
    (hle : ∀ z, g z≤a z) (x : ℝ) : hierarchyAverage n m f g x≤hierarchyAverage n m f a x := by
  rw [hierarchyAverage_eq_integral_exp n m f hf g hg hgE x,
    hierarchyAverage_eq_integral_exp n m f hf a ha haE x]
  exact integral_mono (hgE.integrable_hierarchyPathLaw n m hf hg x)
    (haE.integrable_hierarchyPathLaw n m hf ha x) hle

theorem hierarchyPressure_increment_sandwich (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (x : ℝ) :
    hierarchyAverage n m f (fun z => g z-f z) x ≤
      hierarchyPressure n m g x-hierarchyPressure n m f x ∧
    Real.exp (hierarchyPressure n m g x-hierarchyPressure n m f x) ≤
      hierarchyAverage n m f (fun z => Real.exp (g z-f z)) x := by
  induction n with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ n ih =>
    let p := m (Fin.last n)
    let F := gaussianStep p f
    let G := gaussianStep p g
    have hF : BoundedDerivs F := hf.gaussianStep p
    have hG : BoundedDerivs G := hg.gaussianStep p
    have hU : BoundedDerivs (fun z => g z-f z) := by
      simpa only [neg_one_mul,← sub_eq_add_neg] using hg.add (hf.const_mul (-1))
    have hV : BoundedDerivs (fun z => G z-F z) := by
      simpa only [neg_one_mul,← sub_eq_add_neg] using hG.add (hF.const_mul (-1))
    have hUE : HasExpGrowth (fun z => Real.exp (g z-f z)) := by
      simpa only [one_mul] using (hU.exp_growths 1).1
    have hVE : HasExpGrowth (fun z => Real.exp (G z-F z)) := by
      simpa only [one_mul] using (hV.exp_growths 1).1
    have hUC : Continuous (fun z => Real.exp (g z-f z)) := Real.continuous_exp.comp hU.1.continuous
    have hVC : Continuous (fun z => Real.exp (G z-F z)) := Real.continuous_exp.comp hV.1.continuous
    have H := ih (fun i => m i.castSucc) (fun i => hm i.castSucc) hF hG
    constructor
    · refine (hierarchyAverage_mono_exp n (fun i => m i.castSucc) hF
        (gaussianAverage_continuous_of_expGrowth hf p hU.hasExpGrowth hU.1.continuous)
        hV.1.continuous (gaussianAverage_expGrowth hf p hU.hasExpGrowth) hV.hasExpGrowth
        (fun z => (gaussianStep_increment_sandwich hf hg (hm (Fin.last n)) z).1) x).trans H.1
    · refine H.2.trans (hierarchyAverage_mono_exp n (fun i => m i.castSucc) hF
        hVC (gaussianAverage_continuous_of_expGrowth hf p hUE hUC)
        hVE (gaussianAverage_expGrowth hf p hUE)
        (fun z => (gaussianStep_increment_sandwich hf hg (hm (Fin.last n)) z).2) x)

theorem hierarchyPressure_increment_integral_sandwich (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) {f g : ParameterSpace n → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (x : ℝ) :
    (∫ z, g z-f z ∂hierarchyPathLaw n m f x) ≤
      hierarchyPressure n m g x-hierarchyPressure n m f x ∧
    hierarchyPressure n m g x-hierarchyPressure n m f x ≤
      Real.log (∫ z, Real.exp (g z-f z) ∂hierarchyPathLaw n m f x) := by
  have hU : BoundedDerivs (fun z => g z-f z) := by
    simpa only [neg_one_mul,← sub_eq_add_neg] using hg.add (hf.const_mul (-1))
  have hUE : HasExpGrowth (fun z => Real.exp (g z-f z)) := by
    simpa only [one_mul] using (hU.exp_growths 1).1
  have H := hierarchyPressure_increment_sandwich n m hm hf hg x
  rw [hierarchyAverage_eq_integral_exp n m f hf _ hU.1.continuous hU.hasExpGrowth x,
    hierarchyAverage_eq_integral_exp n m f hf (fun z => Real.exp (g z-f z)) (Real.continuous_exp.comp hU.1.continuous) hUE x] at H
  refine ⟨H.1,?_⟩
  have hi := hUE.integrable_hierarchyPathLaw n m hf (Real.continuous_exp.comp hU.1.continuous) x
  let := hierarchyPathLaw_probability n m f hf x
  have hp := integral_exp_pos hi
  exact (Real.le_log_iff_exp_le hp).mpr H.2

end SK.Analytic

end
end

end OAI
