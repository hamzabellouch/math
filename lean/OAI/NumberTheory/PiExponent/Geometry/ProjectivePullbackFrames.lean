import OAI.NumberTheory.PiExponent.Polynomials.PullbackFrameCoefficient

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

def pullbackRestrictFactorNatIso (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback V.ι) ≪≫
  Scheme.Modules.pullbackComp V.ι f ≪≫
  Scheme.Modules.pullbackCongr h ≪≫
  (Scheme.Modules.pullbackComp g U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback g)

theorem exists_restricted_pullback_frame_all_of_factor
    (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict V.ι ≅ O V.toScheme,
      ∀ s : O X ⟶ M,
      coefficient eF (restrictSection V.ι (pullbackSection f s)) =
        g.appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ V.toScheme.Modules :=
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι
  let G : X.Modules ⥤ V.toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g
  let uF : F.obj (O X) ≅ O V.toScheme :=
    (Scheme.Modules.restrictFunctor V.ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso V.ι
  let uG : G.obj (O X) ≅ O V.toScheme :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨eF, he⟩ := PiExponent.PullbackFrameCoefficient.exists_frame_natIso_all
    F G (pullbackRestrictFactorNatIso f U V g h) uF uG (pullbackFrame g e)
  refine ⟨eF, fun s => ?_⟩
  have hs : coefficient eF (restrictSection V.ι (pullbackSection f s)) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection U.ι s)) := by
    let P : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback f
    let R : Y.Modules ⥤ V.toScheme.Modules :=
      Scheme.Modules.restrictFunctor V.ι
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ V.toScheme.Modules :=
      Scheme.Modules.pullback g
    let p : P.obj (O X) ≅ O Y := pullbackUnitIso f
    let r : R.obj (O Y) ≅ O V.toScheme :=
      Scheme.Modules.restrictUnitIso V.ι
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O V.toScheme := pullbackUnitIso g
    have hl : restrictSection V.ι (pullbackSection f s) = uF.inv ≫ F.map s := by
      change r.inv ≫ R.map (p.inv ≫ P.map s) = (r.inv ≫ R.map p.inv) ≫ R.map (P.map s)
      exact (congrArg (fun k => r.inv ≫ k) (R.map_comp p.inv (P.map s))).trans
        (Category.assoc r.inv (R.map p.inv) (R.map (P.map s))).symm
    have hr : pullbackSection g (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact (congrArg (coefficient eF) hl).trans
      ((he s).trans (congrArg (coefficient (pullbackFrame g e)) hr).symm)
  rw [hs, coefficient_pullback]

theorem exists_restricted_pullback_frame_all (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      ∀ s : O X ⟶ M,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) :=
  exists_restricted_pullback_frame_all_of_factor f U (f ⁻¹ᵁ U) (f ∣_ U)
    (morphismRestrict_ι f U).symm e

def restrictedPullbackFrame (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ((Scheme.Modules.pullback f).obj M).restrict V.ι ≅ O V.toScheme :=
  (exists_restricted_pullback_frame_all_of_factor f U V g h e).choose

lemma restrictedPullbackFrame_coefficient (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (restrictedPullbackFrame f U V g h e)
      (restrictSection V.ι (pullbackSection f s)) =
      g.appTop (coefficient e (restrictSection U.ι s)) :=
  (exists_restricted_pullback_frame_all_of_factor f U V g h e).choose_spec s

end
end PiExponentSeshadri.Geometry

end OAI
