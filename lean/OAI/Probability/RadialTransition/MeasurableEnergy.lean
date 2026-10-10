import OAI.Probability.RadialTransition.MeasurableProducts

namespace OAI

universe uX

noncomputable section


open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition
section MeasurableEnergy
variable {X : Type uX} [MeasurableSpace X]
lemma measurable_multisetPairing_right {v : X → X → ℝ}
    (hv : Measurable (Function.uncurry v)) (s : Multiset X)
    {ι : Type} [Fintype ι] : Measurable (fun x : ι → X => multisetPairing v s (configurationMultiset x)) := by
  induction s using Multiset.induction_on with
  | empty => simp only [multisetPairing_zero_left]; exact measurable_const
  | @cons a s ih =>
    simp only [multisetPairing, Multiset.map_cons, Multiset.sum_cons, sum_map_configuration] at *
    exact (Finset.measurable_sum _ (fun i _ => hv.comp (measurable_const.prodMk (measurable_pi_apply i)))).add ih

lemma measurable_multisetEnergy_configuration {v : X → X → ℝ}
    (hv : Measurable (Function.uncurry v)) {ι : Type} [Fintype ι] :
    Measurable (fun x : ι → X => multisetEnergy v (configurationMultiset x)) := by
  simp only [multisetEnergy, multisetPairing_configuration, multisetDiagonal_configuration]
  apply measurable_const.mul
  apply Measurable.sub
  · exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => hv.comp (show Measurable (fun x : ι → X => (x i, x j)) from (measurable_pi_apply i).prodMk (measurable_pi_apply j))))
  · exact Finset.measurable_sum _ (fun i _ => hv.comp (show Measurable (fun x : ι → X => (x i, x i)) from (measurable_pi_apply i).prodMk (measurable_pi_apply i)))

lemma measurableConfiguration_boltzmann {v : X → X → ℝ}
    (hv : Measurable (Function.uncurry v)) (hsym : ∀ x y, v x y = v y x) (β : ℝ) :
    MeasurableConfiguration (fun s => ENNReal.ofReal (Real.exp (-β * multisetEnergy v s))) := by
  intro s ι _
  simp only [multisetEnergy_add hsym]
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul ((measurable_const.add (measurable_multisetEnergy_configuration hv)).add
      (measurable_multisetPairing_right hv s))))

end MeasurableEnergy
end RadialTransition

end

end OAI
