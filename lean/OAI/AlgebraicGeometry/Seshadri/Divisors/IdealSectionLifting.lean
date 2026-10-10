import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.LocalUniversal
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AffineOrderRestriction
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.PowerIdeal

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullback_affine_coefficient (f : Y ⟶ X) (V : X.affineOpens)
    {M : X.Modules} (e : M.restrict V.1.ι ≅ O V.1.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ V.1).ι ≅
      O (f ⁻¹ᵁ V.1).toScheme,
      ∀ (W : Y.affineOpens) (h : W.1 ≤ f ⁻¹ᵁ V.1) (s : O X ⟶ M),
        affineCoefficient W (frameOnSmaller eF W.1 h) (pullbackSection f s) =
          f.appLE V.1 W.1 h (affineCoefficient V e s) := by
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame_all f V.1 e
  refine ⟨eF,fun W h s => ?_⟩
  unfold affineCoefficient
  rw [frameOnSmaller_coefficient,he s]
  have hmap : (f.resLE V.1 W.1 h).appTop ≫ W.1.topIso.hom =
      V.1.topIso.hom ≫ f.appLE V.1 W.1 h :=
    (arrowResLEAppIso f V.1 W.1 h).hom.w.symm
  exact congrArg (fun restriction : Γ(V.1.toScheme, ⊤) ⟶ Γ(Y, W.1) =>
    restriction (coefficient e (restrictSection V.1.ι s))) hmap

lemma InvertibleLocal.pullback_frame_equation {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    (I.ideal V).map (f.appLE V.1 U.1 hUV).hom =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ MaximalSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι
  have H : ((I.comap f).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← MaximalSeshadri.InvertibleLocal.restricted_image_on_chart J ι hJ U.1.ι
        ⟨⊤,isAffineOpen_top _⟩ V (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
    ext r
    change (∃ s, (MaximalSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤) s = r) ↔
      ∃ s, (MaximalSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤)
        (e.inv.val.app (.op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (.op ⊤) s,?_⟩
      have ht : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (.op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩; exact ⟨e.inv.val.app (.op ⊤) s,hs⟩
  rw [IdealPullback.comap_ι_top,IdealPullback.comap_ideal I f U V hUV] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

lemma ideal_power_tensor_equation (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (M : LineBundle Y) (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (d : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {affineMapCoefficient U
      (tensorFrame (J.pow n) M U.1 (idealPowerFrame J U.1 d n) e) e
      (tensorInclusion (J.pow n) M (idealPowerInclusion J ι n))} =
      ((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom := by
  trans Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 d n)
    (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n)}
  · exact tensor_inclusion_ideal (J.pow n) M (idealPowerInclusion J ι n) U _ e
  rw [idealPowerInclusion_ideal,← InvertibleLocal.pullback_frame_equation J ι hJ U V hUV,
    Ideal.map_pow]

theorem lift_section_of_local_ideal_power (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (M : LineBundle X) (n : ℕ) (s : O X ⟶ M.sheaf)
    (hs : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ e : M.sheaf.restrict V.1.ι ≅ O V.1.toScheme,
        affineCoefficient V e s ∈ (I.ideal V)^n) :
    ∃! q : O Y ⟶ ((J.pow n).tensor (M.pullback f)).sheaf,
      q ≫ tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) =
        pullbackSection f s := by
  let hmono : Mono (C := Y.Modules) (idealPowerInclusion J ι n) :=
    @idealPowerInclusion_mono Y J ι hJ.1 n
  let : Mono (C := Y.Modules)
      (tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n)) :=
    @tensorInclusion_mono Y (J.pow n) (M.pullback f) (idealPowerInclusion J ι n) hmono
  apply global_division_of_local_lifts
  intro y
  obtain ⟨V,hyV,eV,hsV⟩ := hs (f y)
  obtain ⟨eF,heF⟩ := pullback_affine_coefficient f V eV
  obtain ⟨W,hyW,⟨eW⟩⟩ := J.locallyRankOne y
  obtain ⟨_,⟨U₀,hU₀,rfl⟩,hyU,hUW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ W ⊓ f ⁻¹ᵁ V.1 from ⟨hyW,hyV⟩) (W ⊓ f ⁻¹ᵁ V.1).isOpen
  let U : Y.affineOpens := ⟨U₀,hU₀⟩
  let d := frameOnSmaller eW U.1 (fun z hz => (hUW hz).1)
  let e : (M.pullback f).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
    frameOnSmaller eF U.1 (fun z hz => (hUW hz).2)
  let d' := idealPowerFrame J U.1 d n
  have hm : affineCoefficient U e (pullbackSection f s) ∈
      Ideal.span {affineMapCoefficient U (tensorFrame (J.pow n) (M.pullback f) U.1 d' e)
        e (tensorInclusion (J.pow n) (M.pullback f) (idealPowerInclusion J ι n))} := by
    dsimp only [d']
    rw [ideal_power_tensor_equation f I J ι hJ (M.pullback f) n U V
      (fun z hz => (hUW hz).2) d e]
    have hcoeff : affineCoefficient U e (pullbackSection f s) =
        f.appLE V.1 U.1 (fun z hz => (hUW hz).2) (affineCoefficient V eV s) :=
      heF U (fun z hz => (hUW hz).2) s
    rw [hcoeff]
    exact Ideal.mem_map_of_mem _ hsV
  refine ⟨U.1,hyU,?_⟩
  apply framed_local_division (tensorFrame (J.pow n) (M.pullback f) U.1 d' e) e
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hm
  rw [Ideal.mem_span_singleton]
  refine ⟨U.1.topIso.inv a,?_⟩
  have H := congrArg U.1.topIso.inv ha
  simpa only [affineCoefficient,affineMapCoefficient,map_mul,U.1.topIso.hom_inv_id_apply] using H

end
end MaximalSeshadri.Geometry

end

end OAI
