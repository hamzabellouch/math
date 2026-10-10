import OAI.Geometry.CylinderCovering.Beams.MainDefinitions

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace

namespace CylinderCovering.BeamStrip

theorem IsRectangle.isCompact {B : Set Space} (hB : IsRectangle B) : IsCompact B := by
  obtain ⟨c,u,v,_,_,_,rfl⟩ := hB
  have heq : {z | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1,
      z = c+s • u+t • v} =
      (fun p : ℝ × ℝ => c+p.1 • u+p.2 • v) '' (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := by
    ext z
    constructor
    · rintro ⟨s,hs,t,ht,rfl⟩
      exact ⟨(s,t),⟨hs,ht⟩,rfl⟩
    · rintro ⟨⟨s,t⟩,⟨hs,ht⟩,rfl⟩
      exact ⟨s,hs,t,ht,rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

theorem HasRectangularBase.isCompact {C : RuledApproximation.Cylinder}
    (hC : HasRectangularBase C) : IsCompact C.base :=
  Subtype.isCompact_iff.mpr (IsRectangle.isCompact hC)

end CylinderCovering.BeamStrip

namespace ShortenedBeam

theorem HasTriangularBase.isCompact {C : RuledApproximation.Cylinder}
    (hC : HasTriangularBase C) : IsCompact C.base := by
  obtain ⟨v,hv,hbase⟩ := hC
  rw [Subtype.isCompact_iff,hbase]
  exact (Set.finite_range v).isCompact_convexHull ℝ

theorem HasMixedBase.isCompact {C : RuledApproximation.Cylinder}
    (hC : HasMixedBase C) : IsCompact C.base := by
  rcases hC with hC | hC
  · exact hC.isCompact
  · exact hC.isCompact

end ShortenedBeam

end

end OAI
