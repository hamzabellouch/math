import OAI.Probability.IsingPerceptron.RetainedDisplacement
import OAI.Probability.IsingPerceptron.NamespaceSplit

namespace OAI

/-! Pushforward of an integrable terminal Gibbs tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped ENNReal
namespace InvariantIsing

lemma gibbsProbability_map_normalize {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Nonempty X] [Nonempty Y] (ν : Measure X) [IsProbabilityMeasure ν]
    {f : X → Y} (hf : Measurable f) {H : Y → ℝ} (hH : Measurable H)
    (hi : Integrable (fun x => Real.exp (H (f x))) ν) :
    (gibbsProbability ν (fun x => H (f x))).map f =
      normalizeMass ((ν.map f).withDensity (fun y => ENNReal.ofReal (Real.exp (H y)))) := by
  have hI : Integrable (fun y => Real.exp (H y)) (ν.map f) :=
    (integrable_map_measure hH.exp.aestronglyMeasurable hf.aemeasurable).mpr hi
  have hmass : ((ν.map f).withDensity (fun y => ENNReal.ofReal (Real.exp (H y)))) Set.univ =
      ENNReal.ofReal (∫ y, Real.exp (H y) ∂ν.map f) := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun y => (Real.exp_pos _).le)]
  rw [gibbsProbability_eq_tilted _ _ hi, ← normalizeMass_exp ν (fun x => H (f x)) (hH.comp hf) hi]
  apply normalizeMass_weight_map ν hf hH.exp.ennreal_ofReal
  rw [hmass]
  exact ⟨ENNReal.ofReal_pos.mpr (integral_exp_pos hI), ENNReal.ofReal_lt_top⟩

end InvariantIsing

end

end OAI
