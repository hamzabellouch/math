import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.TwoChartIntersection
import OAI.AlgebraicGeometry.Seshadri.Geometry.PencilCharts
import OAI.AlgebraicGeometry.Seshadri.Geometry.PencilOverlap
import OAI.AlgebraicGeometry.Seshadri.Geometry.ChartCoherence

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames

variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseIntersection (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊓
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

theorem finite_pencil_intersection (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K ↥(twoBaseIntersection k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k (show W ≤ U from inf_le_left))
    (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k (show W ≤ V from inf_le_right))
    (L.restrict V.ι).sheaf d
  let : Module.Finite K ↥(F.range ⊓ G.range) :=
    two_chart_intersection_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu hv
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊓ G.range).map E.toLinearMap = twoBaseIntersection k L.sheaf U V := by
    rw [Submodule.map_inf E.toLinearMap E.injective]
    change F.range.map E.toLinearMap ⊓ G.range.map E.toLinearMap =
      (res k L.sheaf (show W ≤ U from inf_le_left)).range ⊓
        (res k L.sheaf (show W ≤ V from inf_le_right)).range
    exact congrArg₂ (· ⊓ ·)
      (chartMap_range_coherent k L.sheaf (show W ≤ U from inf_le_left))
      (chartMap_range_coherent k L.sheaf (show W ≤ V from inf_le_right))
  let : Module.Finite K ↥((F.range ⊓ G.range).map E.toLinearMap) :=
    Module.Finite.equiv (E.submoduleMap (F.range ⊓ G.range))
  rw [← he]
  infer_instance
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
