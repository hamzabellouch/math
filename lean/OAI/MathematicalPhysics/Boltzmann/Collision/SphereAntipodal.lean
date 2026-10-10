import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests

namespace OAI

/-! # Antipodal invariance of the actual angular area measure -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness

theorem sphereArea_antipodal :
    MeasurePreserving (Neg.neg : Sphere → Sphere) sphereArea sphereArea := by
  refine ⟨measurable_neg,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_neg hs]
  change (volume : Measure Velocity).toSphere (Neg.neg ⁻¹' s) =
    (volume : Measure Velocity).toSphere s
  rw [Measure.toSphere_apply' _ (measurable_neg hs),Measure.toSphere_apply' _ hs]
  have he : Ioo (0 : ℝ) 1 • ((↑) '' (Neg.neg ⁻¹' s)) =
      (Neg.neg : Velocity → Velocity) ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    constructor
    · rintro ⟨r,hr,y,⟨n,hn,rfl⟩,rfl⟩
      change -(r • (n : Velocity)) ∈ Ioo (0 : ℝ) 1 • ((↑) '' s)
      exact ⟨r,hr,(-n : Velocity),⟨-n,hn,rfl⟩,by simp⟩
    · rintro ⟨r,hr,y,⟨n,hn,rfl⟩,hy⟩
      refine ⟨r,hr,(-n : Velocity),⟨-n,?_,rfl⟩,?_⟩
      · simpa using hn
      · simpa only [smul_neg,neg_neg] using congrArg Neg.neg hy
  rw [he,Measure.measure_preimage_neg]

end BoltzmannNonuniqueness

end

end OAI
