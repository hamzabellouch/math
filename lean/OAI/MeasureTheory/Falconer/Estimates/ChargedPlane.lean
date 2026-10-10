import OAI.MeasureTheory.Falconer.Radial.ClassicalAffineDistance

namespace OAI

/-! # Positive affine-plane restrictions at the classical threshold -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem positive_distance_of_charged_affine_plane
    (hpublished : PublishedClassicalDistance)
    (μ : ProbabilityMeasure (Space d)) (hK : IsCompact (μ : Measure (Space d)).support)
    (V : Submodule ℝ (Space d)) (p : Space d)
    (hcharge : 0 < (μ : Measure (Space d)) {x | x-p ∈ V})
    {s C : ℝ} (hs : ((Module.finrank ℝ V : ℝ)+1)/2 < s) (hC : 0 < C)
    (hfrost : FrostmanBallBound (μ : Measure (Space d)) s C) :
    0 < volume (distanceSet (μ : Measure (Space d)).support) := by
  let A : Set (Space d) := {x | x-p ∈ V}
  have hA : IsClosed A :=
    V.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const)
  let ν := positiveRestriction μ A hcharge
  have hdom : (ν : Measure (Space d)) ≪ (μ : Measure (Space d)) :=
    positiveRestriction_absolutelyContinuous μ A hcharge
  have hsupp : (ν : Measure (Space d)).support ⊆ (μ : Measure (Space d)).support :=
    hdom.support_mono
  have hKν : IsCompact (ν : Measure (Space d)).support :=
    hK.of_isClosed_subset Measure.isClosed_support hsupp
  have hplane : (ν : Measure (Space d)) Aᶜ = 0 := by
    change (positiveRestriction μ A hcharge : Measure (Space d)) Aᶜ = 0
    rw [positiveRestriction_eq,Measure.smul_apply,Measure.restrict_apply hA.measurableSet.compl,
      compl_inter_self,measure_empty,smul_zero]
  have hCν : 0 < ((μ : Measure (Space d)) A).toReal⁻¹*C :=
    mul_pos (inv_pos.mpr (ENNReal.toReal_pos hcharge.ne' (measure_ne_top _ _))) hC
  have hfrostν : FrostmanBallBound (ν : Measure (Space d)) s
      (((μ : Measure (Space d)) A).toReal⁻¹*C) := by
    have hid := positiveRestriction_projected_frostman μ A hcharge
      (ContinuousLinearMap.id ℝ (Space d)) (by simpa using hfrost)
    simpa using hid
  have hdist := classical_distance_in_affine_plane hpublished ν hKν V rfl p
    hplane hs hCν hfrostν
  exact hdist.trans_le (measure_mono (distanceSet_mono hsupp))

end Falconer

end OAI
