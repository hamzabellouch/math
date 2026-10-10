import OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso
import OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

def LineBundle.inverseCover (L : LineBundle X) (x : X) : X.Opens :=
  (L.locallyRankOne x).choose

lemma LineBundle.mem_inverseCover (L : LineBundle X) (x : X) :
    x ∈ L.inverseCover x := (L.locallyRankOne x).choose_spec.1

def LineBundle.inverseCoverFrame (L : LineBundle X) (x : X) :
    L.sheaf.restrict (L.inverseCover x).ι ≅ structureSheaf (L.inverseCover x).toScheme :=
  (L.locallyRankOne x).choose_spec.2.some

lemma LineBundle.inverseCover_covers (L : LineBundle X) :
    ⊤ ≤ ⨆ x, L.inverseCover x := by
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, L.mem_inverseCover x⟩

def LineBundle.inverseCocycle (L : LineBundle X) :
    LineBundleGluing.Cocycle L.inverseCover :=
  LineBundleFrameCocycle.ofFrames L.sheaf L.inverseCover L.inverseCoverFrame

def LineBundle.inverse (L : LineBundle X) : LineBundle X :=
  LineBundleGluing.lineBundle L.inverseCocycle.inverse L.inverseCover_covers

def lineTensorInverseIso (L : LineBundle X) :
    moduleTensor X L.sheaf L.inverse.sheaf ≅ structureSheaf X :=
  moduleTensorIso
    (LineBundleFrameCocycle.isoSheaf L.sheaf L.inverseCover L.inverseCoverFrame
      L.inverseCover_covers) (Iso.refl _) ≪≫
    LineBundleGluing.tensorInverseIso L.inverseCocycle L.inverseCover_covers

def moduleTensorInverseCancelIso (M : X.Modules) (L : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) L.inverse.sheaf ≅ M :=
  moduleLineTensorAssoc M L L.inverse ≪≫
    moduleTensorIso (Iso.refl M) (lineTensorInverseIso L) ≪≫ moduleTensorRightUnit M

def LineBundle.dualSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    L.inverse.sheaf ⟶ structureSheaf X :=
  (moduleTensorUnit L.inverse.sheaf).inv ≫ moduleTensorMap s (𝟙 _) ≫
    (lineTensorInverseIso L).hom

end
end PiExponentSeshadri.Geometry

end OAI
