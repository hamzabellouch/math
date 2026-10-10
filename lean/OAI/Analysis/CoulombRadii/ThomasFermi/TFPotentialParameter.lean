import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.TfExtendNonneg

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb
variable {Ω : Set Space} (hΩ : MeasurableSet Ω)
include hΩ

lemma tfPotential_eq_restrict [IsFiniteMeasure (volume.restrict Ω)]
    (f : TFLp (volume.restrict Ω)) (y : Space) :
    tfPotential f y=∫ z in Ω, coulombKernel (y-z)*f z := by
  rw [←integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z∈Ω <;> simp [tfExtend,hz]

variable [IsFiniteMeasure (volume.restrict Ω)]

lemma tfPotential_add (f g : TFLp (volume.restrict Ω)) (y : Space) :
    tfPotential (f+g) y=tfPotential f y+tfPotential g y := by
  have he : tfPotential (f+g) y=∫ z, coulombKernel (y-z)*tfExtend Ω f z+
      coulombKernel (y-z)*tfExtend Ω g z := by
    rw [tfPotential_eq_restrict hΩ,←integral_indicator hΩ]
    apply integral_congr_ae
    have H := ae_restrict_iff' hΩ |>.mp (Lp.coeFn_add f g)
    filter_upwards [H] with z hz
    by_cases hzi : z∈Ω
    · simp only [Set.indicator_of_mem hzi,tfExtend,hz hzi,Pi.add_apply,mul_add]
    · simp [hzi,tfExtend]
  rw [he,integral_add (tfPotential_integrand hΩ f y) (tfPotential_integrand hΩ g y)]
  rfl

lemma tfPotential_smul (c : ℝ) (f : TFLp (volume.restrict Ω)) (y : Space) :
    tfPotential (c • f) y=c*tfPotential f y := by
  rw [tfPotential_eq_restrict hΩ,tfPotential_eq_restrict hΩ,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with z hz
  rw [hz]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def tfPotentialEvaluation (y : Space) : TFLp (volume.restrict Ω) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => tfPotential f y
      map_add' := fun f g => tfPotential_add hΩ f g y
      map_smul' := fun c f => tfPotential_smul hΩ c f y }
    ((8*Real.pi)^(2/5:ℝ)+(volume.real Ω)^(2/5:ℝ))
    (fun f => tfPotential_bound hΩ f y)

lemma continuous_tfPotential_evaluation (y : Space) :
    Continuous (fun f : TFLp (volume.restrict Ω) => tfPotential f y) :=
  (tfPotentialEvaluation hΩ y).continuous

lemma aestronglyMeasurable_localTFPotential {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (W : A → TFLq (volume.restrict Ω)) (hW : AEStronglyMeasurable W μ) (y : Space) :
    AEStronglyMeasurable (fun x => tfPotential (localTFMinimizer hΩ (W x)) y) μ :=
  (continuous_tfPotential_evaluation hΩ y).comp_aestronglyMeasurable
    ((continuous_localTFMinimizer hΩ).comp_aestronglyMeasurable hW)

end Coulomb
end

end
end

end OAI
