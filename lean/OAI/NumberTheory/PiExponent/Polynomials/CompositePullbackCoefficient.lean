import OAI.NumberTheory.PiExponent.Polynomials.PullbackFrameCoefficient

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CompositePullbackCoefficient


theorem exists_frame {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (e : (Scheme.Modules.pullback (f ≫ g)).obj M ≅ O X) :
    ∃ e' : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅ O X,
      ∀ s : O Z ⟶ M,
      coefficient e' (pullbackSection f (pullbackSection g s)) =
        coefficient e (pullbackSection (f ≫ g) s) := by
  let F := Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback (f ≫ g)
  let uF : F.obj (O Z) ≅ O X :=
    (Scheme.Modules.pullback f).mapIso (pullbackUnitIso g) ≪≫ pullbackUnitIso f
  obtain ⟨e', he'⟩ := PullbackFrameCoefficient.exists_frame_natIso_all
    F G (Scheme.Modules.pullbackComp f g) uF (pullbackUnitIso (f ≫ g)) e
  refine ⟨e', fun s => ?_⟩
  simpa only [F, G, uF, pullbackSection, Iso.trans_inv, Functor.mapIso_inv,
    Functor.comp_map, Functor.map_comp, Category.assoc] using he' s

end PiExponent.CompositePullbackCoefficient

end

end OAI
