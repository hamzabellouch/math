import OAI.Geometry.SurfaceImmersion.Correction.CoordinateSurfaceModels
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingCoordinateMap
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleAtlas
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveVelocities

namespace OAI

/-! Constructed smooth models of the two actual sheets, using the same
parameter on their common curve. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure LocalDoubleSheetModel (f : M → ProjectionTarget 3) (x y : M) (t : ℝ) where
  left : OpenPartialHomeomorph M Base
  right : OpenPartialHomeomorph M Base
  F : Base → ProjectionTarget 3
  G : Base → ProjectionTarget 3
  left_mem : x ∈ left.source
  right_mem : y ∈ right.source
  left_center : left x = ![0,t]
  right_center : right y = ![0,t]
  left_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ left left.source
  right_smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ right right.source
  left_inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ left.symm left.target
  right_inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ right.symm right.target
  F_smooth : ContDiff ℝ ∞ F
  G_smooth : ContDiff ℝ ∞ G
  left_model : f =ᶠ[𝓝 x] F ∘ left
  right_model : f =ᶠ[𝓝 y] G ∘ right
  common_axis : (fun s => F ![0,s]) =ᶠ[𝓝 t] (fun s => G ![0,s])
  transverse : Function.Surjective (fun z : Base × Base =>
    fderiv ℝ F ![0,t] z.1-fderiv ℝ G ![0,t] z.2)

namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem adapted_sheet_models (c : SmoothDoubleChart f)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {t : ℝ}
    (ht : t ∈ c.coord.target)
    (hreg : Function.Surjective (surfacePairDerivative f (c.coord.symm t).val.1 (c.coord.symm t).val.2))
    (hAf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (c.coord.symm t).val.1))
    (hBf : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (c.coord.symm t).val.2)) :
    Nonempty (LocalDoubleSheetModel f (c.coord.symm t).val.1 (c.coord.symm t).val.2 t) := by
  let A : ℝ → M := fun s => (c.coord.symm s).val.1
  let B : ℝ → M := fun s => (c.coord.symm s).val.2
  have hAs := c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
  have hBs := c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
  have hEq : f ∘ A =ᶠ[𝓝 t] f ∘ B :=
    Filter.Eventually.of_forall fun s => (c.coord.symm s).property.2
  obtain ⟨hAI,hBI⟩ := regular_double_curve_velocities hf hAs hBs hEq (c.inverse_regular t ht) hAf hBf
  obtain ⟨a,U,hU,htU,hUT,has,hai,haxisA⟩ :=
    surface_curve_coordinates c.coord.open_target c.inverse_left_smooth ht hAI
  obtain ⟨b,V,hV,htV,hVT,hbs,hbi,haxisB⟩ :=
    surface_curve_coordinates c.coord.open_target c.inverse_right_smooth ht hBI
  have ha := (haxisA t htU).1
  have hb := (haxisB t htV).1
  have hac := (haxisA t htU).2
  have hbc := (haxisB t htV).2
  obtain ⟨P,F,hP,hxP,hPa,hF,hFP⟩ := coordinate_representative a hai hf ha
  obtain ⟨Q,G,hQ,hyQ,hQb,hG,hGQ⟩ := coordinate_representative b hbi hf hb
  have hFm := coordinate_representative_germ a ha hP hxP hFP
  have hGm := coordinate_representative_germ b hb hQ hyQ hGQ
  have htrans := coordinate_pair_surjective a b has hbs ha hb hF hG hFm hGm hreg
  rw [hac,hbc] at htrans
  let J := U ∩ V ∩ (fun s => (![0,s] : Base)) ⁻¹' (P ∩ Q)
  have hJ : IsOpen J := (hU.inter hV).inter ((hP.inter hQ).preimage (by fun_prop))
  have htJ : t ∈ J := by
    refine ⟨⟨htU,htV⟩,?_,?_⟩
    · change (![0,t] : Base) ∈ P
      rwa [← hac]
    · change (![0,t] : Base) ∈ Q
      rwa [← hbc]
  have haxis : (fun s => F ![0,s]) =ᶠ[𝓝 t] (fun s => G ![0,s]) := by
    filter_upwards [hJ.mem_nhds htJ] with s hs
    have hsa := haxisA s hs.1.1
    have hsb := haxisB s hs.1.2
    calc
      F ![0,s] = f (a.symm ![0,s]) := hFP hs.2.1
      _ = f (A s) := by rw [← hsa.2,a.left_inv hsa.1]
      _ = f (B s) := (c.coord.symm s).property.2
      _ = G ![0,s] := by
        rw [hGQ hs.2.2]
        change f (B s) = f (b.symm ![0,s])
        rw [← hsb.2,b.left_inv hsb.1]
  exact ⟨⟨a,b,F,G,ha,hb,hac,hbc,has,hbs,hai,hbi,hF,hG,hFm,hGm,haxis,htrans⟩⟩

end SmoothDoubleChart

omit [IsManifold planeModel ∞ M] in
lemma LocalDoubleSheetModel.crossing_regular {f : M → ProjectionTarget 3}
    {x y : M} {t : ℝ} (m : LocalDoubleSheetModel f x y t) :
    Function.Bijective (fderiv ℝ (crossingCoordinateMap m.F m.G) (0,t)) :=
  crossingCoordinateMap_regular m.F_smooth m.G_smooth t m.common_axis m.transverse

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
