import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.LineClosedUnit

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

lemma LineBundle.pullback_unit_isIso [IsIso (IdealModule.structureMap f)]
    (L : LineBundle Y) : IsIso (LineClosedUnit.map f L) := by
  let OY : LineBundle Y := ⟨O Y,fun _ => ⟨⊤,trivial,⟨Scheme.Modules.restrictUnitIso _⟩⟩⟩
  have hu := pullbackUnit_adjunction f
  rw [Adjunction.homEquiv_unit] at hu
  have : IsIso (LineClosedUnit.map f OY ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom) := by
    change IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom)
    rw [hu]
    exact inferInstanceAs (IsIso (IdealModule.structureMap f))
  have unitIsIso : IsIso (C := Y.Modules) (LineClosedUnit.map f OY) :=
    (isIso_comp_right_iff _ _).mp ‹IsIso (_ ≫ _)›
  have hU (U : Y.Opens) : IsIso (IdealModule.structureMap (f ∣_ U)) := by
    rw [← LineClosedUnit.framed_map f OY U (Scheme.Modules.restrictUnitIso U.ι)]
    exact ((Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      (Scheme.Modules.restrictFunctor U.ι).mapIso
        (@asIso Y.Modules _ _ _ (LineClosedUnit.map f OY) unitIsIso) ≪≫
      LineClosedUnit.frame f OY U (Scheme.Modules.restrictUnitIso U.ι)).isIso_hom
  apply ModuleLocal.isIso_of_local
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U,hy,?_⟩
  have : IsIso (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (LineClosedUnit.map f L) ≫
      (LineClosedUnit.frame f L U e).hom) := by
    exact (LineClosedUnit.framed_map f L U e).symm ▸ hU U
  have : IsIso (C := U.toScheme.Modules) e.inv := e.isIso_inv
  have : IsIso (C := U.toScheme.Modules) (LineClosedUnit.frame f L U e).hom :=
    (LineClosedUnit.frame f L U e).isIso_hom
  have hi := (isIso_comp_left_iff (C := U.toScheme.Modules) e.inv _).mp ‹IsIso (e.inv ≫ _)›
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hi

lemma pullbackSection_adjunction {M : Y.Modules} (s : O Y ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullbackUnitIso f).hom ≫ pullbackSection f s) =
    s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  simp only [pullbackSection,Iso.hom_inv_id_assoc]
  rw [Adjunction.homEquiv_unit]
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality s

lemma LineBundle.pullbackSection_bijective [IsIso (IdealModule.structureMap f)]
    (L : LineBundle Y) : Function.Bijective (pullbackSection f (M := L.sheaf)) := by
  let := L.pullback_unit_isIso f
  let η := LineClosedUnit.map f L
  have hi : Function.Injective (fun t : O X ⟶ (Scheme.Modules.pullback f).obj L.sheaf =>
      (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((pullbackUnitIso f).hom ≫ t)) :=
    (Equiv.injective _).comp (fun a b h => (cancel_epi (pullbackUnitIso f).hom).mp h)
  constructor
  · intro a b h
    have hh := congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullbackUnitIso f).hom ≫ t)) h
    rw [pullbackSection_adjunction,pullbackSection_adjunction] at hh
    exact (cancel_mono η).mp hh
  · intro t
    let a := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((pullbackUnitIso f).hom ≫ t)
    refine ⟨a ≫ inv η,hi ?_⟩
    dsimp only
    rw [pullbackSection_adjunction]
    change (a ≫ inv η) ≫ η = a
    simp

end
end MaximalSeshadri.Geometry

end

end OAI
