import OAI.Analysis.CircleDomains.Probability.AffinePhysicalTimeMeasure

namespace OAI

/-! The time measure of a restricted piece transported back to its original
parameter interval. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

theorem physicalTimeLength_piece (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (η γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a < b)
    (hmatch : ∀ s, η.val (affinePathTime a b s) = γ.val s) :
    (physicalTimeLength e y₀ η).restrict (Icc a b) =
      (physicalTimeLength e y₀ γ).map (affinePathTime a b) := by
  have heq : affineFinitePhysicalPath e hU y₀ η hab = γ := by
    apply Subtype.ext
    exact ContinuousMap.ext hmatch
  have hm : physicalTimeLength e y₀ γ =
      ((physicalTimeLength e y₀ η).restrict (Icc a b)).map (rescalePathTime a b) := by
    rw [← heq]
    exact physicalTimeLength_affine e hU y₀ η hab
  rw [hm, Measure.map_map (affinePathTime a b).continuous.measurable
    (rescalePathTime a b).continuous.measurable]
  have hid : (fun t => affinePathTime a b (rescalePathTime a b t)) =ᵐ[
      (physicalTimeLength e y₀ η).restrict (Icc a b)] id := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact affine_rescalePathTime hab ht
  simp only [Function.comp_def]
  rw [Measure.map_congr hid, Measure.map_id]

end CircleDomainRigidity

end

end OAI
