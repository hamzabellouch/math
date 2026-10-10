import OAI.Probability.InvariantIsing.Cavity.CavitySelectedCappedAverage

namespace OAI

/-! Finite replica product measures may be separated into their leaf,
ordinary residual and spin coordinates before normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_replica_product_integral {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {r : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (F : (Fin r → X × Y) → ℝ) (hF : Measurable F) {M : ℝ}
    (hbound : ∀ ξ, ‖F ξ‖ ≤ M) :
    (∫ ξ, F ξ ∂Measure.pi (fun _ : Fin r => μ.prod ν)) =
      ∫ x, ∫ y, F (fun i => (x i, y i))
        ∂Measure.pi (fun _ : Fin r => ν) ∂Measure.pi (fun _ : Fin r => μ) := by
  let G : (Fin r → X) × (Fin r → Y) → ℝ := fun p => F (fun i => (p.1 i, p.2 i))
  have hG : Measurable G := hF.comp (Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  have hi : Integrable G ((Measure.pi (fun _ : Fin r => μ)).prod
      (Measure.pi (fun _ : Fin r => ν))) :=
    (integrable_const M).mono' hG.aestronglyMeasurable (ae_of_all _ fun p => hbound _)
  have he := (measurePreserving_arrowProdEquivProdArrow X Y (Fin r)
    (fun _ => μ) (fun _ => ν)).hasLaw.integral_comp hG.aestronglyMeasurable
  calc
    _ = ∫ p, G p ∂(Measure.pi (fun _ : Fin r => μ)).prod
        (Measure.pi (fun _ : Fin r => ν)) := by
      simpa [G, Function.comp_def, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.arrowProdEquivProdArrow] using he
    _ = _ := integral_prod G hi

end InvariantIsing

end

end OAI
