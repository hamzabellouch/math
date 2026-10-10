import OAI.Probability.SLE.Loewner.RawDiskRadiusLaw

namespace OAI

/-! The finite centered disk success probability is a measurable function
of its initial angle, so it can be tested against the actual angle law. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance angleTailMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance angleTailBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def RawCanonicalMass.angleDiskTail (R : RawCanonicalMass)
    (ν : Measure C(ℝ≥0,ℝ)) (κ b v θ : ℝ) : ℝ≥0∞ :=
  (ν.withDensity (fun p => canonicalFiniteDensity κ (v,Target.diskMapInv θ 0,p)))
    {p | b ≤ R.diskAtRadius κ θ v p}

lemma RawCanonicalMass.angleDiskTail_measurable (R : RawCanonicalMass)
    (ν : Measure C(ℝ≥0,ℝ)) [SFinite ν] (κ b v : ℝ) :
    Measurable (R.angleDiskTail ν κ b v) := by
  let E : Set (ℝ × C(ℝ≥0,ℝ)) := {q | b ≤ R.diskAtRadius κ q.1 v q.2}
  let D : ℝ × C(ℝ≥0,ℝ) → ℝ≥0∞ := fun q =>
    canonicalFiniteDensity κ (v,Target.diskMapInv q.1 0,q.2)
  have hE : MeasurableSet E := measurableSet_le measurable_const
    (R.diskAtRadius_measurable κ Prod.fst (fun _ => v) measurable_fst measurable_const
      Prod.snd measurable_snd)
  have hz : Measurable (fun θ => Target.diskMapInv θ 0) := by
    unfold Target.diskMapInv
    fun_prop
  have hD : Measurable D := (canonicalFiniteDensity_measurable κ).comp
    (measurable_const.prodMk ((hz.comp measurable_fst).prodMk measurable_snd))
  have hK := (hD.indicator hE).lintegral_prod_right' (ν := ν)
  have he (θ : ℝ) : (∫⁻ p, E.indicator D (θ,p) ∂ν)=R.angleDiskTail ν κ b v θ := by
    have hEθ : MeasurableSet {p | b ≤ R.diskAtRadius κ θ v p} :=
      measurableSet_le measurable_const
        (R.diskAtRadius_measurable κ (fun _ => θ) (fun _ => v)
          measurable_const measurable_const id measurable_id)
    change (∫⁻ p, {p | b ≤ R.diskAtRadius κ θ v p}.indicator
      (fun p => D (θ,p)) p ∂ν)=_
    rw [lintegral_indicator hEθ,← withDensity_apply _ hEθ]
    rfl
  simpa only [he] using hK

lemma RawCanonicalMass.angleDiskTail_average (R : RawCanonicalMass)
    (ν : Measure C(ℝ≥0,ℝ)) [SFinite ν] (κ : ℝ) (hκ : 0 < κ) (b v : ℝ) :
    (∫⁻ θ, R.angleDiskTail ν κ b v θ ∂Target.angleLaw κ)=
      rawCenteredDiskLaw ν κ v {q | b ≤ R.diskAtRadius κ q.1 v q.2} := by
  symm
  exact measure_joint_tail_of_lintegral (rawCenteredDiskLaw ν κ v) (Target.angleLaw κ)
    (fun θ => ν.withDensity (fun p => canonicalFiniteDensity κ (v,Target.diskMapInv θ 0,p)))
    (rawCenteredDiskLaw_lintegral ν κ hκ v) _
    (R.diskAtRadius_measurable κ Prod.fst (fun _ => v) measurable_fst measurable_const
      Prod.snd measurable_snd) b

end SLEExactGauge.Multipoint

end

end OAI
