import OAI.Analysis.CircleDomains.Probability.PathOccupation
import Mathlib.Topology.EMetricSpace.BoundedVariation

namespace OAI

/-! A Lipschitz map multiplies actual path arclength by at most its
Lipschitz constant. The proof constructs the nonnegative Stieltjes difference. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem pathLengthMeasure_le_of_interval_bounds
    (α : RectifiablePath X) (β : RectifiablePath Y) (L : ℝ≥0)
    (hI : ∀a b : PathTime, a ≤ b → pathLengthMeasure β (Icc a b) ≤
      (L : ℝ≥0∞) * pathLengthMeasure α (Icc a b)) :
    pathLengthMeasure β ≤ L • pathLengthMeasure α := by
  have hdiff (γ : RectifiablePath X) (a b : PathTime) (hab : a ≤ b) :
      pathLengthMeasure γ (Icc a b) =
        ENNReal.ofReal (pathLengthFunction γ b - pathLengthFunction γ a) := by
    rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure γ)),
      pathLengthMeasure, StieltjesFunction.measure_Ioc]
  have hdiffβ (a b : PathTime) (hab : a ≤ b) :
      pathLengthMeasure β (Icc a b) =
        ENNReal.ofReal (pathLengthFunction β b - pathLengthFunction β a) := by
    rw [← measure_congr (Ioc_ae_eq_Icc (μ := pathLengthMeasure β)),
      pathLengthMeasure, StieltjesFunction.measure_Ioc]
  have hbound (a b : PathTime) (hab : a ≤ b) :
      pathLengthFunction β b - pathLengthFunction β a ≤
        L * (pathLengthFunction α b - pathLengthFunction α a) := by
    have h := hI a b hab
    rw [hdiff α a b hab, hdiffβ a b hab] at h
    have hnonneg : 0 ≤ (L : ℝ) * (pathLengthFunction α b - pathLengthFunction α a) :=
      mul_nonneg L.property (sub_nonneg.mpr ((pathLengthFunction α).mono hab))
    apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
    rw [ENNReal.ofReal_mul (p := (L : ℝ))
      (q := pathLengthFunction α b - pathLengthFunction α a) L.property,
      ENNReal.ofReal_coe_nnreal]
    exact h
  let F : StieltjesFunction PathTime := {
    toFun := fun t => L * pathLengthFunction α t - pathLengthFunction β t
    mono' := by
      intro a b hab
      have h := hbound a b hab
      dsimp
      linarith
    right_continuous' := fun t =>
      (((continuous_pathLengthFunction α).const_mul (L : ℝ)).sub
        (continuous_pathLengthFunction β)).continuousAt.continuousWithinAt }
  have he : F + pathLengthFunction β = L • pathLengthFunction α := by
    apply StieltjesFunction.ext
    intro t
    change (L : ℝ) * pathLengthFunction α t - pathLengthFunction β t +
      pathLengthFunction β t = (L : ℝ) * pathLengthFunction α t
    ring
  have hmeasure := congrArg (fun f : StieltjesFunction PathTime => f.measure) he
  rw [StieltjesFunction.measure_add, StieltjesFunction.measure_smul] at hmeasure
  change F.measure + pathLengthMeasure β = L • pathLengthMeasure α at hmeasure
  rw [← hmeasure]
  exact le_add_of_nonneg_left bot_le

def lipschitzMappedPath (α : RectifiablePath X) (f : X → Y) {S : Set X} {L : ℝ≥0}
    (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S) : RectifiablePath Y := by
  have hc : Continuous (f ∘ α.val) := by
    apply ContinuousOn.comp_continuous hL.continuousOn α.val.continuous hα
  refine ⟨⟨f ∘ α.val, hc⟩, ?_⟩
  exact hL.comp_boundedVariationOn (fun t _ => hα t) α.property

theorem lipschitzMappedPath_length_le (α : RectifiablePath X) (f : X → Y)
    {S : Set X} {L : ℝ≥0} (hL : LipschitzOnWith L f S) (hα : ∀t, α.val t ∈ S) :
    pathLengthMeasure (lipschitzMappedPath α f hL hα) ≤ L • pathLengthMeasure α := by
  apply pathLengthMeasure_le_of_interval_bounds
  intro a b hab
  rw [pathLengthMeasure_Icc _ hab, pathLengthMeasure_Icc _ hab]
  exact hL.comp_eVariationOn_le (fun t _ => hα t)

end CircleDomainRigidity

end

end OAI
