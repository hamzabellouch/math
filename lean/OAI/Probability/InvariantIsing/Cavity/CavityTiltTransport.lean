import OAI.Probability.InvariantIsing.Cavity.CavityPrecisionTiltLaw

namespace OAI

/-! Normalized quadratic tilts commute with the Gaussian factor map. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_tilt_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (F : X → Y) (hF : Measurable F)
    (f : Y → ℝ) (hf : Measurable f) :
    (μ.tilted (f ∘ F)).map F = (μ.map F).tilted f := by
  ext s hs
  rw [Measure.map_apply hF hs, tilted_apply_eq_ofReal_integral' _ (hF hs),
    tilted_apply_eq_ofReal_integral' _ hs,
    integral_map hF.aemeasurable hf.exp.aestronglyMeasurable,
    setIntegral_map hs ((hf.exp.div_const _).aestronglyMeasurable) hF.aemeasurable]
  rfl

lemma cavity_tilt_add_const {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Integrable (fun z => Real.exp (f z)) μ) (c : ℝ) :
    μ.tilted (fun z => f z + c) = μ.tilted f := by
  have := isProbabilityMeasure_tilted hf
  have he : (f + fun _ : EuclideanSpace ℝ (Fin d) => c) = (fun z => f z + c) := by
    funext z
    rfl
  rw [← he]
  exact (tilted_tilted hf (fun _ : EuclideanSpace ℝ (Fin d) => c)).symm.trans
    (tilted_const (μ.tilted f) c)

end InvariantIsing

end

end OAI
