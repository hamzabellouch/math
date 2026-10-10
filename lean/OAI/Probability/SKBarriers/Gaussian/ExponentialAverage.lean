import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyDensity
import OAI.Probability.SKBarriers.Scalar.GrowthOperations

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ExponentialAverage
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem HasExpGrowth.gaussian_integral {f : E × ℝ → F} (hf : HasExpGrowth f) :
    HasExpGrowth (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
  obtain ⟨C,M,hC,hM,hf⟩ := hf
  let B := ∫ y : ℝ, Real.exp (M*|y|) ∂gaussianReal 0 1
  have hB : 0 ≤ B := integral_nonneg (fun y => (Real.exp_pos _).le)
  refine ⟨C*B,M,mul_nonneg hC hB,hM,?_⟩
  intro x
  have hb : ∀ y, ‖f (x,y)‖ ≤ C*Real.exp (M*‖x‖)*Real.exp (M*|y|) := by
    intro y
    apply (hf (x,y)).trans
    rw [mul_assoc,← Real.exp_add,← mul_add]
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hM
    rw [Prod.norm_def,Real.norm_eq_abs]
    exact max_le_add_of_nonneg (norm_nonneg x) (abs_nonneg y)
  calc
    _ ≤ ∫ y, ‖f (x,y)‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C*Real.exp (M*‖x‖)*Real.exp (M*|y|) ∂gaussianReal 0 1 :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
        ((integrable_exp_mul_abs_gaussian M).const_mul _) (ae_of_all _ hb)
    _ = _ := by rw [integral_const_mul]; dsimp [B]; ring

theorem gaussianAverage_exp_representation {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (g : E × ℝ → F) (x : E) :
    gaussianAverage m f g x = Real.exp (-m*gaussianStep m f x) •
      ∫ y, Real.exp (m*f (x,y)) • g (x,y) ∂gaussianReal 0 1 := by
  rw [gaussianAverage,gaussianStepLaw_integral hf,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [smul_smul,← Real.exp_add]
  congr 2
  ring

theorem gaussianAverage_expGrowth {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} (hg : HasExpGrowth g) :
    HasExpGrowth (gaussianAverage m f g) := by
  have hn := (((hf.exp_growths m).1).smul hg).gaussian_integral
  have hi := ((hf.gaussianStep m).exp_growths (-m)).1
  rw [funext (gaussianAverage_exp_representation hf m g)]
  exact hi.smul hn

theorem gaussianAverage_continuous_of_expGrowth {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) {g : E × ℝ → F} (hg : HasExpGrowth g) (hc : Continuous g) :
    Continuous (gaussianAverage m f g) := by
  have he := (hf.exp_growths m).1
  have hce : Continuous (fun z => Real.exp (m*f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf.1.continuous)
  have hn := (he.smul hg).continuous_gaussian_integral (hce.smul hc)
  have hi : Continuous (fun x => Real.exp (-m*gaussianStep m f x)) :=
    Real.continuous_exp.comp (continuous_const.mul (hf.gaussianStep m).1.continuous)
  rw [funext (gaussianAverage_exp_representation hf m g)]
  exact hi.smul hn
end ExponentialAverage

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathWeight_expGrowth (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) :
    HasExpGrowth (hierarchyPathWeight n m f) := by
  have hh := hf.add ((hierarchyPenalty_boundedDerivs n m 1 f hf).const_mul (-1))
  have h := (hh.exp_growths 1).1
  rw [funext (hierarchyPathWeight_eq n m f 1)]
  simpa only [one_mul,neg_one_mul,← sub_eq_add_neg] using h

theorem hierarchyPath_exp_integrable (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace n → ℝ) (hg : Continuous g) (hb : HasExpGrowth g) :
    Integrable (fun z => hierarchyPathWeight n m f z*g z) (fiberGaussian n x) :=
  ((hierarchyPathWeight_expGrowth n m f hf).mul hb).integrable_fiberGaussian n
    ((hierarchyPathWeight_continuous n m f hf).mul hg) x
end SK.Analytic

end
end

end

end OAI
