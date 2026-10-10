import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Polynomials.PullbackFrameCoefficient

namespace OAI

noncomputable section
namespace PiExponent.CompositePullbackFrame
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

private theorem mapIso_trans_inv_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U : D} (e : A ≅ B) (u : F.obj B ≅ U)
    (s : A ⟶ T) :
    (F.mapIso e ≪≫ u).inv ≫ F.map s = u.inv ≫ F.map (e.inv ≫ s) := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc]

private theorem map_comp_iso_inv {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U : D} (u : U ⟶ F.obj A)
    (s : A ⟶ B) (e : B ≅ T) :
    (u ≫ F.map (s ≫ e.hom)) ≫ (F.mapIso e).inv = u ≫ F.map s := by
  simp only [Functor.mapIso_inv, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, Category.comp_id]

theorem exists_frame (f : X ⟶ Y) (φ : Z ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Z ⟶ V.toScheme) (h : φ ≫ f = g ≫ V.ι)
    {M : Y.Modules} (e : M.restrict V.ι ≅ O V.toScheme) :
    ∃ E : ((Scheme.Modules.pullback f).obj M).restrict φ ≅ O Z,
      ∀ s : O Y ⟶ M,
        coefficient E (restrictSection φ (pullbackSection f s)) =
          g.appTop (coefficient e (restrictSection V.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor φ
  let G := Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback g
  let v : F ≅ G :=
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback φ) ≪≫
    Scheme.Modules.pullbackComp φ f ≪≫
    Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp g V.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm
      (Scheme.Modules.pullback g)
  let uF : F.obj (O Y) ≅ O Z :=
    (Scheme.Modules.restrictFunctor φ).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso φ
  let uG : G.obj (O Y) ≅ O Z :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso V.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨E, hE⟩ := PullbackFrameCoefficient.exists_frame_natIso_all F G v uF uG
    (pullbackFrame g e)
  refine ⟨E, fun s => ?_⟩
  have hs : coefficient E (restrictSection φ (pullbackSection f s)) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection V.ι s)) := by
    simp only [restrictSection, pullbackSection]
    exact (congrArg (coefficient E)
      (mapIso_trans_inv_comp (Scheme.Modules.restrictFunctor φ)
        (pullbackUnitIso f) (Scheme.Modules.restrictUnitIso φ)
        ((Scheme.Modules.pullback f).map s)).symm).trans
      ((hE s).trans (congrArg (coefficient (pullbackFrame g e))
        (mapIso_trans_inv_comp (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictUnitIso V.ι) (pullbackUnitIso g)
          ((Scheme.Modules.restrictFunctor V.ι).map s))))
  rw [hs, coefficient_pullback]

theorem exists_power_frame (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Z ⟶ X) [IsOpenImmersion φ] (V : Y.Opens)
    (g : Z ⟶ V.toScheme) (h : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ O V.toScheme) :
    ∃ E : (modulePow X (L.pullback f).sheaf n).restrict φ ≅ O Z,
      ∀ s : O Y ⟶ modulePow Y L.sheaf n,
        coefficient E (restrictSection φ (pullbackPowerSection L f n s)) =
          g.appTop (coefficient e (restrictSection V.ι s)) := by
  obtain ⟨E, hE⟩ := exists_frame f φ V g h e
  refine ⟨(Scheme.Modules.restrictFunctor φ).mapIso
    (PiExponentSeshadri.PullbackTensor.powIso f L n).symm ≪≫ E, fun s => ?_⟩
  erw [coefficient_transport]
  have hs : restrictSection φ (pullbackPowerSection L f n s) ≫
      ((Scheme.Modules.restrictFunctor φ).mapIso (PiExponentSeshadri.PullbackTensor.powIso f L n).symm).hom =
      restrictSection φ (pullbackSection f s) := by
    simp only [restrictSection, pullbackPowerSection, Functor.mapIso_hom, Iso.symm_hom]
    exact map_comp_iso_inv (Scheme.Modules.restrictFunctor φ)
      (Scheme.Modules.restrictUnitIso φ).inv (pullbackSection f s)
      (PiExponentSeshadri.PullbackTensor.powIso f L n)
  exact (congrArg (coefficient E) hs).trans (hE s)

end PiExponent.CompositePullbackFrame
end

end OAI
