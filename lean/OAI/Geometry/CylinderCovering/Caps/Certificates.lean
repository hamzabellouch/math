import OAI.Geometry.CylinderCovering.Caps.CertificatesDefinitions
import OAI.Geometry.CylinderCovering.Caps.FiniteShape
import OAI.Geometry.CylinderCovering.Caps.CompensationEstimates

namespace OAI

namespace CylinderCovering.HalfheightCertificates

theorem shape : ShapeStatement := by
  intro δ hδ R hR hR0 N i
  have hM : 0 ≤ HalfheightFinite.maxCap R N i :=
    RadialRiemann.capMax_nonneg (by norm_num) hR hR0 i
  obtain ⟨hU,hL,hiU,hiL⟩ := HalfheightFinite.Shape.projected_shape i hδ hM
  obtain ⟨hnU,hnL⟩ := HalfheightFinite.Shape.projected_nondegenerate i hδ hM
  obtain ⟨ha,hb,dU,dL,hdU,hdL,haU,hbU,haL,hbL⟩ :=
    HalfheightFinite.Shape.projected_parallel_sides i hδ hM
  exact ⟨⟨HalfheightFinite.Shape.firstVertices δ R N i,hU,hiU,hnU,
      dU,_,_,hdU,ha,hb,haU,hbU⟩,
    ⟨HalfheightFinite.Shape.secondVertices δ R N i,hL,hiL,hnL,
      dL,_,_,hdL,ha,hb,haL,hbL⟩⟩

open HalfHeightCaps.CompensationEstimates

theorem quantitative : QuantitativeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ X Y Z r s u v hδ hd hXb hYb hr hs hu hv hY hZ hX hZv
    have hrad := radial_excess_bounds hδ hd hXb hYb hr hs hu hv hY hZ hX hZv
    have hang := angular_errors hδ hd hXb hYb hr hs hu hv hY hZ hX hZv
    exact ⟨⟨(weight_bounds hδ hd hXb hr).2.2.1,
        (weight_bounds hδ hd hYb hs).2.2.2⟩,hrad,hang,
      weighted_comparison hδ hXb hYb hr hs hang.1 hang.2⟩
  · exact fun _ _ _ hδ hd hr hs => cubic_padding_lower hδ hd hr hs
  · exact fun _ _ _ _ _ _ _ _ hδ hd hXb hYb hr hs hY hZ hX hZv =>
      cubic_failures_incompatible hδ hd hXb hYb hr hs hY hZ hX hZv

theorem main : Statement := ⟨shape,quantitative⟩

end CylinderCovering.HalfheightCertificates

end OAI
