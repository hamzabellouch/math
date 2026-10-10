import OAI.NumberTheory.PiExponent.Approximation.LineClosedUnit
import OAI.NumberTheory.PiExponent.Geometry.PrincipalCartierSequence

namespace OAI


namespace PiExponentSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma chart_topIso_naturality {Y : Scheme.{0}} (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

lemma restriction_principal (_p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) (r : Γ(U.1.toScheme,⊤))
    (hI : I.ideal U = Ideal.span {U.1.topIso.hom r}) :
    (I.subschemeι ∣_ U.1).ker.ideal ⟨⊤,isAffineOpen_top U.1.toScheme⟩ =
      Ideal.span {r} := by
  ext z
  rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
  change (I.subschemeι ∣_ U.1).appTop z = 0 ↔ z ∈ Ideal.span {r}
  have hz : (I.subschemeι ∣_ U.1).appTop z = 0 ↔
      U.1.topIso.hom z ∈ I.ideal U := by
    rw [← chart_topIso_naturality]
    simp only [CommRingCat.comp_apply]
    rw [← I.ker_subschemeι_app U]
    change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv
      (I.subschemeι.app U.1 (U.1.topIso.hom z)) = 0 ↔
      I.subschemeι.app U.1 (U.1.topIso.hom z) = 0
    exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective
  rw [hz,hI,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.inv a,?_⟩
    have h := congrArg U.1.topIso.inv ha
    simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.hom a,?_⟩
    simpa only [map_mul] using congrArg U.1.topIso.hom ha

theorem exact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    ∃ hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).ShortExact := by
  have local_exact (U : X.affineOpens)
      (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (hI : I.ideal U = Ideal.span {U.1.topIso.hom
        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :=
    PrincipalSequence.exact (I.subschemeι ∣_ U.1)
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
      (restriction_principal p I U _ hI)
  have hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0 := by
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U,hx,e,d,hI⟩ := heq x
    obtain ⟨hzero,hex⟩ := local_exact U e d hI
    refine ⟨U.1,hx,?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono (LineClosedUnit.frame I.subschemeι N U.1 d).hom).mp
    rw [Functor.map_comp,comp_zero,zero_comp]
    rw [Category.assoc,Category.assoc]
    rw [← d.hom_inv_id_assoc ((Scheme.Modules.restrictFunctor U.1.ι).map
      (LineClosedUnit.map I.subschemeι N))]
    simp only [Category.assoc]
    rw [LineClosedUnit.framed_map]
    simpa only [Category.assoc] using! hzero
  refine ⟨hz,{ exact := ?_, epi_g := LineClosedUnit.epi _ _ }⟩
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  obtain ⟨hzero,hex⟩ := local_exact U e d hI
  refine ⟨U.1,hx,?_⟩
  let S := (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).map
    (Scheme.Modules.restrictFunctor U.1.ι)
  let T := ShortComplex.mk (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
    (IdealModule.structureMap (I.subschemeι ∣_ U.1)) hzero
  let ee : S ≅ T := ShortComplex.isoMk e d (LineClosedUnit.frame I.subschemeι N U.1 d)
    (by simp [S,T]) (by
      change d.hom ≫ IdealModule.structureMap (I.subschemeι ∣_ U.1) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (LineClosedUnit.map I.subschemeι N) ≫ _
      rw [← LineClosedUnit.framed_map I.subschemeι N U.1 d]
      exact d.hom_inv_id_assoc _)
  exact ShortComplex.exact_of_iso ee.symm hex.exact

end
end PiExponentSeshadri.CartierSequence

end OAI
