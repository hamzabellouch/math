import OAI.NumberTheory.PiExponent.Cohomology.CurveFinitePushforwardCohomology
import OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationEuler
import OAI.NumberTheory.PiExponent.Geometry.BirationalOpenIso
import OAI.NumberTheory.PiExponent.Geometry.CurveFinitePushforwardCoherent
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationUnit

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem lowCohomologyFinite_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Spec (.of ℂ))
    (M : Y.Modules) [M.IsFinitePresentation]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (hM : LowCohomologyFinite (f ≫ p) M) :
    LowCohomologyFinite p ((Scheme.Modules.pushforward f).obj M) := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj M)).choose.isQuasicoherent
  intro n hn
  apply CurveFinitePushforwardCohomology.finiteDimensional_pushforward
    f (baseScalars p) M U V hU hV hcover n hn
  have hm := hM n hn
  rw [CurveFinitePushforwardCohomology.baseScalars_comp] at hm
  exact hm

theorem pullback_euler_degree_of_open_iso [IsIntegral X]
    [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X) [IsFinite f]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (f ∣_ W)]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (L : LineBundle X)
    (hO : LowCohomologyFinite p (structureSheaf X))
    (hL : LowCohomologyFinite p L.sheaf)
    (hOY : LowCohomologyFinite (f ≫ p) (structureSheaf Y))
    (hLY : LowCohomologyFinite (f ≫ p) (L.pullback f).sheaf)
    [Subsingleton (cohomology (structureSheaf X) 2)]
    [Subsingleton (cohomology L.sheaf 2)] :
    eulerCharacteristic (f ≫ p) 1 (L.pullback f).sheaf -
        eulerCharacteristic (f ≫ p) 1 (structureSheaf Y) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : IsDominant f := dominant_of_iso_restrict f W hW
  let : Mono (unitMap f) := unitMap_mono f
  let : (structureSheaf Y).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (L.pullback f).sheaf.IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (L.pullback f)
  let : (structureSheaf Y).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf Y)).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj (structureSheaf Y)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj (structureSheaf Y))).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf)).choose.isQuasicoherent
  have hB := lowCohomologyFinite_pushforward f p (structureSheaf Y) U V hU hV hcover hOY
  have hPL := lowCohomologyFinite_pushforward f p (L.pullback f).sheaf U V hU hV hcover hLY
  have hBL := lowCohomologyFinite_of_iso p (pushforwardPullbackIso f L) hPL
  have h := generic_extension_tensor_euler p hd
    ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) (unitMap f)
    (unitMap_isoOpen_ne_bot f W hW) L hO hB hL hBL
  rw [eulerCharacteristic_iso p (pushforwardPullbackIso f L)] at h
  rw [CurveFinitePushforwardCohomology.euler_one_pushforward f p
    (L.pullback f).sheaf U V hU hV hcover,
    CurveFinitePushforwardCohomology.euler_one_pushforward f p
      (structureSheaf Y) U V hU hV hcover] at h
  exact h

theorem pullback_euler_degree [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X) [IsFinite f]
    (e : Y.functionField ≃+* X.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) ≫ f = X.fromSpecStalk (genericPoint X))
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (L : LineBundle X)
    (hO : LowCohomologyFinite p (structureSheaf X))
    (hL : LowCohomologyFinite p L.sheaf)
    (hOY : LowCohomologyFinite (f ≫ p) (structureSheaf Y))
    (hLY : LowCohomologyFinite (f ≫ p) (L.pullback f).sheaf)
    [Subsingleton (cohomology (structureSheaf X) 2)]
    [Subsingleton (cohomology L.sheaf 2)] :
    eulerCharacteristic (f ≫ p) 1 (L.pullback f).sheaf -
        eulerCharacteristic (f ≫ p) 1 (structureSheaf Y) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  obtain ⟨W,hW,hiso⟩ := BirationalOpenIso.exists_open_iso_of_generic_inverse f e he
  let := hiso
  have hw : W ≠ ⊥ := by
    intro hw
    simp only [hw, TopologicalSpace.Opens.mem_bot] at hW
  exact pullback_euler_degree_of_open_iso f p hd W hw U V hU hV hcover L hO hL hOY hLY

end PiExponent.CurveNormalizationDegree

end

end OAI
