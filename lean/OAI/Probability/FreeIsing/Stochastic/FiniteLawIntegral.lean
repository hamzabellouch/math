import OAI.Probability.FreeIsing.Spins.Chain

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem integral_finiteLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    {mu : Measure Ω} [IsFiniteMeasure mu] {X : Ω → E} (hX : Measurable X)
    (weight : E → ℝ) (hweight : ∀ e, 0 ≤ weight e)
    (hlaw : ∀ e, mu {ω | X ω = e} = ENNReal.ofReal (weight e)) (f : E → ℝ) :
    ∫ ω, f (X ω) ∂mu = ∑ e : E, weight e * f e := by
  rw [← integral_map hX.aemeasurable (measurable_of_finite f).aestronglyMeasurable]
  rw [integral_fintype (Integrable.of_finite : Integrable f (Measure.map X mu))]
  apply Finset.sum_congr rfl
  intro e he
  rw [Measure.real, Measure.map_apply hX (measurableSet_singleton e)]
  change (mu {ω | X ω = e}).toReal * f e = weight e * f e
  rw [hlaw e, ENNReal.toReal_ofReal (hweight e)]

theorem integrable_finiteLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    {mu : Measure Ω} [IsFiniteMeasure mu] {X : Ω → E} (hX : Measurable X)
    (f : E → ℝ) : Integrable (fun ω => f (X ω)) mu := by
  exact (integrable_map_measure (measurable_of_finite f).aestronglyMeasurable
    hX.aemeasurable).mp Integrable.of_finite

local instance : MeasurableSingletonClass IsingSpin where
  measurableSet_singleton _ := by trivial

theorem integral_finiteSpinCoordinates {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : I → TreeVertex d) (weight : (I → IsingSpin) → ℝ)
    (hweight : ∀ eta, 0 ≤ weight eta)
    (hlaw : ∀ eta, mu {x | ∀ i, x (p i) = eta i} = ENNReal.ofReal (weight eta))
    (f : (I → IsingSpin) → ℝ) :
    ∫ x, f (fun i => x (p i)) ∂mu = ∑ eta : I → IsingSpin, weight eta * f eta := by
  refine integral_finiteLaw (X := fun x : TreeVertex d → IsingSpin => fun i => x (p i))
    (Measurable.of_eval (fun index => measurable_pi_apply (p index))) weight hweight ?_ f
  intro eta
  convert hlaw eta using 2
  ext x
  simp only [Set.mem_ofPred_eq, funext_iff]

theorem integral_spinPath_of_cylinderLaw {d n : ℕ} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {mu : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure mu]
    (p : Fin (n+1) → TreeVertex d)
    (hlaw : ∀ eta : Fin (n+1) → IsingSpin,
      mu {x | ∀ i, x (p i) = eta i} =
        ENNReal.ofReal ((1/2 : ℝ) * spinPathWeight theta n eta)) :
    ∫ x, spinSign (x (p 0)) * spinSign (x (p (Fin.last n))) ∂mu = theta ^ n := by
  calc
    _ = ∑ eta : Fin (n+1) → IsingSpin,
        ((1/2 : ℝ) * spinPathWeight theta n eta) *
          (spinSign (eta 0) * spinSign (eta (Fin.last n))) :=
      integral_finiteSpinCoordinates p _
        (fun eta => mul_nonneg (by norm_num) (spinPathWeight_nonneg hlo hhi n eta))
        hlaw _
    _ = theta ^ n := by
      simpa only [mul_assoc] using spinPathWeight_correlation theta n

end Problem367

end

end OAI
