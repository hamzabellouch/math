import OAI.NumberTheory.PiExponent.Approximation.FramedPullback

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.PullbackFrameCoefficient

theorem exists_frame_natIso_all {X Y : Scheme.{0}}
    (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) :
    ∃ eF : F.obj M ≅ O Y, ∀ s : O X ⟶ M,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  intro s
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b (uG.inv ≫ G.map s ≫ e.hom)

theorem exists_frame_of_factors_through_open {X Y : Scheme.{0}}
    (U : X.Opens) (g : Y ⟶ U.toScheme)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : (Scheme.Modules.pullback (g ≫ U.ι)).obj M ≅ O Y,
      ∀ s : O X ⟶ M,
      coefficient eF (pullbackSection (g ≫ U.ι) s) =
        g.appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback (g ≫ U.ι)
  let G : X.Modules ⥤ Y.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g
  let v : F ≅ G := (Scheme.Modules.pullbackComp g U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback g)
  let uG : G.obj (O X) ≅ O Y :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨eF, he⟩ := exists_frame_natIso_all F G v (pullbackUnitIso (g ≫ U.ι)) uG
    (pullbackFrame g e)
  refine ⟨eF, fun s => ?_⟩
  have hs := he s
  have hs' : coefficient eF (pullbackSection (g ≫ U.ι) s) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection U.ι s)) := by
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ Y.Modules := Scheme.Modules.pullback g
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O Y := pullbackUnitIso g
    have hr : pullbackSection g (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact hs.trans (congrArg (coefficient (pullbackFrame g e)) hr).symm
  rw [hs', coefficient_pullback]

end PiExponent.PullbackFrameCoefficient

end

end OAI
