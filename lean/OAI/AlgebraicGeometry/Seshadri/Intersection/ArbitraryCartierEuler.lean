import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.CartierSequence
import OAI.AlgebraicGeometry.Seshadri.Intersection.SurfaceEuler

namespace OAI


                                               
section

namespace MaximalSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma restriction_principal_closed (f : Y ⟶ X) [IsClosedImmersion f] (U : X.affineOpens)
    (r : Γ(U.1.toScheme,⊤))
    (hI : f.ker.ideal U = Ideal.span {U.1.topIso.hom r}) :
    (f ∣_ U.1).ker.ideal ⟨⊤,isAffineOpen_top U.1.toScheme⟩ = Ideal.span {r} := by
  ext z
  rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
  change (f ∣_ U.1).appTop z = 0 ↔ z ∈ Ideal.span {r}
  have hz : (f ∣_ U.1).appTop z = 0 ↔ U.1.topIso.hom z ∈ f.ker.ideal U := by
    rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
    rw [← chart_topIso_naturality]
    simp only [CommRingCat.comp_apply]
    change (f ⁻¹ᵁ U.1).topIso.inv ((f.app U.1) (U.1.topIso.hom z)) = 0 ↔
      (f.app U.1) (U.1.topIso.hom z) = 0
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U.1).topIso.inv).injective)
  rw [hz,hI,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.inv a,?_⟩
    have h := congrArg U.1.topIso.inv ha
    simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.hom a,?_⟩
    simpa only [map_mul] using congrArg U.1.topIso.hom ha

theorem exact_closed {Y : Scheme.{0}} (f : Y ⟶ X) [IsClosedImmersion f]
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
        (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        f.ker.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    ∃ hz : φ ≫ LineClosedUnit.map f N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map f N) hz).ShortExact := by
  have local_exact (U : X.affineOpens)
      (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (hI : f.ker.ideal U = Ideal.span {U.1.topIso.hom
        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :=
    PrincipalSequence.exact (f ∣_ U.1)
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
      (restriction_principal_closed f U _ hI)
  have hz : φ ≫ LineClosedUnit.map f N = 0 := by
    apply ModuleLocal.eq_zero_of_local
    intro x
    obtain ⟨U,hx,e,d,hI⟩ := heq x
    obtain ⟨hzero,hex⟩ := local_exact U e d hI
    refine ⟨U.1,hx,?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono (LineClosedUnit.frame f N U.1 d).hom).mp
    rw [Functor.map_comp,comp_zero,zero_comp]
    rw [Category.assoc,Category.assoc]
    rw [← d.hom_inv_id_assoc ((Scheme.Modules.restrictFunctor U.1.ι).map
      (LineClosedUnit.map f N))]
    simp only [Category.assoc]
    rw [LineClosedUnit.framed_map]
    exact ((Category.assoc e.inv _ _).trans
      (congrArg (e.inv ≫ ·) (Category.assoc _ _ _))).symm.trans hzero
  refine ⟨hz,{ exact := ?_, epi_g := LineClosedUnit.epi _ _ }⟩
  apply ModuleLocal.exact_of_local
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  obtain ⟨hzero,hex⟩ := local_exact U e d hI
  refine ⟨U.1,hx,?_⟩
  let S := (ShortComplex.mk φ (LineClosedUnit.map f N) hz).map
    (Scheme.Modules.restrictFunctor U.1.ι)
  let T := ShortComplex.mk (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
    (IdealModule.structureMap (f ∣_ U.1)) hzero
  let ee : S ≅ T := ShortComplex.isoMk e d (LineClosedUnit.frame f N U.1 d)
    (by simp [S,T]) (by
      change d.hom ≫ IdealModule.structureMap (f ∣_ U.1) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (LineClosedUnit.map f N) ≫ _
      rw [← LineClosedUnit.framed_map f N U.1 d]
      exact d.hom_inv_id_assoc _)
  exact ShortComplex.exact_of_iso ee.symm hex.exact

end
end MaximalSeshadri.CartierSequence

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem IntegralCurve.cartier_euler_difference (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (M N : LineBundle S.scheme) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (C : IntegralCurve S)
    (heq : ∀ x : S.scheme, ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        C.embedding.ker.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    eulerCharacteristic S.structureMap 2 N.sheaf - eulerCharacteristic S.structureMap 2 M.sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj N.sheaf) := by
  let P := N.pullback C.embedding
  let : Subsingleton (cohomology M.sheaf (2+1)) := ⟨fun x y =>
    (S.lineBundle_cohomology_zero_above_two A hA M 0 x).trans
      (S.lineBundle_cohomology_zero_above_two A hA M 0 y).symm⟩
  obtain ⟨hz,hseq⟩ := CartierSequence.exact_closed C.embedding M N φ heq
  have he := eulerCharacteristic_add S.structureMap hseq 2
    (fun n _ => S.cohomology_finite A hA M n)
    (fun n _ => S.cohomology_finite A hA N n)
    (fun n _ => C.pushforward_cohomology_finite S A hA P n)
  change eulerCharacteristic S.structureMap 2 N.sheaf =
    eulerCharacteristic S.structureMap 2 M.sheaf +
      eulerCharacteristic S.structureMap 2 ((Scheme.Modules.pushforward C.embedding).obj P.sheaf) at he
  rw [C.euler_pushforward S A hA P] at he
  exact sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))

end
end MaximalSeshadri.Geometry

end

end OAI
