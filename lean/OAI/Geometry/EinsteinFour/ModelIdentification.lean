import OAI.Geometry.EinsteinFour.FrameOrientation

namespace OAI

/-! Derdzinski, Compositio Math. 49 (1983), Remark 7,
p.429 (citing Hitchin), identifies compact connected oriented Einstein
four-manifolds of positive scalar curvature with one vanishing Weyl block.
Positive sectional curvature supplies the required scalar sign. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ConnectedSpace M]

/-- The compact positive-curvature specialization of the published
half-conformally-flat identification. -/
def DerdzinskiHitchinInput (g : SmoothMetric M) (o : FrameOrientation g) : Prop :=
  T2Space M → SecondCountableTopology M → CompactSpace M → ConnectedSpace M →
    IsEinstein g → HasPositiveSectionalCurvature g →
    ((∀ c, plusWeyl g c (o.frame c) = 0) ∨
      (∀ c, minusWeyl g c (o.frame c) = 0)) →
    ∃ a : ℝ, 0 < a ∧
      (ScaledIsometricTo g a roundDistance ∨
        ScaledIsometricTo g a fubiniStudyDistance)

theorem classified_of_one_block_vanishes
    (g : SmoothMetric M) (o : FrameOrientation g)
    (hpublished : DerdzinskiHitchinInput g o)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g)
    (hzero : (∀ c, plusNorm o c = 0) ∨ ∀ c, minusNorm o c = 0) :
    Classified g := by
  have hblock : (∀ c, plusWeyl g c (o.frame c) = 0) ∨
      ∀ c, minusWeyl g c (o.frame c) = 0 := by
    rcases hzero with hzero | hzero
    · exact Or.inl (fun c => (plusNorm_eq_zero_iff o c).mp (hzero c))
    · exact Or.inr (fun c => (minusNorm_eq_zero_iff o c).mp (hzero c))
  obtain ⟨a, ha, hmodel⟩ := hpublished inferInstance inferInstance inferInstance
    inferInstance hEinstein hpositive hblock
  refine ⟨a, ha, ?_⟩
  rcases hmodel with hround | hprojective
  · exact Or.inl hround
  · exact Or.inr (Or.inl hprojective)

end

end PositiveEinsteinFour.Geometry

end OAI
