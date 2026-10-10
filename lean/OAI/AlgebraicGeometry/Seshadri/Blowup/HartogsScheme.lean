import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.HartogsPrincipal

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Hartogs
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma spec_restriction_algebraMap {B : CommRingCat}
    {U V : (Spec B).Opens} (h : U ≤ V) (b : B) :
    (Spec B).presheaf.map (homOfLE h).op
        (algebraMap B Γ(Spec B, V) b) =
      algebraMap B Γ(Spec B, U) b := by
  simp only [IsAffineOpen.algebraMap_Spec_obj, CommRingCat.hom_comp, RingHom.comp_apply]
  change ((Scheme.ΓSpecIso B).inv ≫
    (Spec B).presheaf.map (homOfLE le_top).op ≫
      (Spec B).presheaf.map (homOfLE h).op) b = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem sections_injective_of_joint_localizations {B : CommRingCat}
    (x y : B)
    (hinj : Function.Injective ((algebraMap B (Localization.Away x)).prod
      (algebraMap B (Localization.Away y))))
    (U : (Spec B).Opens)
    (hx : PrimeSpectrum.basicOpen x ≤ U) (hy : PrimeSpectrum.basicOpen y ≤ U) :
    Function.Injective (algebraMap B Γ(Spec B, U)) := by
  let (element : B) : Algebra B Γ(Spec B, PrimeSpectrum.basicOpen element) := by
    change Algebra B ((Spec.structureSheaf B).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen element)))
    infer_instance
  let (element : B) : IsLocalization.Away element
      Γ(Spec B, PrimeSpectrum.basicOpen element) := by
    change IsLocalization.Away element ((Spec.structureSheaf B).obj.obj
      (Opposite.op (PrimeSpectrum.basicOpen element)))
    infer_instance
  rw [injective_iff_map_eq_zero]
  intro b hb
  apply hinj
  apply Prod.ext
  · have hzero : algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen x) b = 0 := by
      exact (spec_restriction_algebraMap hx b).symm.trans (by rw [hb, map_zero])
    have hh := congrArg (IsLocalization.algEquiv (Submonoid.powers x)
      Γ(Spec B, PrimeSpectrum.basicOpen x) (Localization.Away x)) hzero
    change algebraMap B (Localization.Away x) b = algebraMap B (Localization.Away x) 0
    rw [map_zero]
    simpa only [AlgEquiv.commutes, map_zero] using hh
  · have hzero : algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen y) b = 0 := by
      exact (spec_restriction_algebraMap hy b).symm.trans (by rw [hb, map_zero])
    have hh := congrArg (IsLocalization.algEquiv (Submonoid.powers y)
      Γ(Spec B, PrimeSpectrum.basicOpen y) (Localization.Away y)) hzero
    change algebraMap B (Localization.Away y) b = algebraMap B (Localization.Away y) 0
    rw [map_zero]
    simpa only [AlgEquiv.commutes, map_zero] using hh

theorem nonempty_of_joint_localizations {B : CommRingCat} [Nontrivial B]
    (x y : B)
    (hinj : Function.Injective ((algebraMap B (Localization.Away x)).prod
      (algebraMap B (Localization.Away y))))
    (U : (Spec B).Opens)
    (hx : PrimeSpectrum.basicOpen x ≤ U) (hy : PrimeSpectrum.basicOpen y ≤ U) :
    Nonempty U := by
  have hi := sections_injective_of_joint_localizations x y hinj U hx hy
  let : Nontrivial Γ(Spec B, U) := hi.nontrivial
  have hUne : Nonempty U := by
    by_contra h
    let : IsEmpty U := not_nonempty_iff.mp h
    let : Subsingleton Γ(U.toScheme, ⊤) := inferInstance
    let : Subsingleton Γ(Spec B, U) :=
      U.topIso.commRingCatIsoToRingEquiv.symm.injective.subsingleton
    exact (zero_ne_one : (0 : Γ(Spec B, U)) ≠ 1) (Subsingleton.elim _ _)
  exact hUne

theorem domain_of_detecting_preintegral_open {B : CommRingCat} [Nontrivial B]
    (x y : B)
    (hinj : Function.Injective ((algebraMap B (Localization.Away x)).prod
      (algebraMap B (Localization.Away y))))
    (U : (Spec B).Opens)
    (hx : PrimeSpectrum.basicOpen x ≤ U) (hy : PrimeSpectrum.basicOpen y ≤ U)
    [IsReduced U.toScheme] [PreirreducibleSpace U] : IsDomain B := by
  have hi := sections_injective_of_joint_localizations x y hinj U hx hy
  have hUne := nonempty_of_joint_localizations x y hinj U hx hy
  let := hUne
  let : IrreducibleSpace U := { toPreirreducibleSpace := inferInstance, toNonempty := hUne }
  let : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  let : IsDomain Γ(Spec B, U) :=
    U.topIso.commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _
  exact Function.Injective.isDomain (algebraMap B Γ(Spec B, U)) hi

theorem principal_quotient_domain_of_preintegral_open
    {A : Type} [CommRing A] [IsDomain A] (x y f : A) (hx : x ≠ 0)
    (hxy : ∀ b : A, x ∣ y * b → x ∣ b)
    [Nontrivial (A ⧸ Ideal.span {f})]
    (U : (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Opens)
    (hUx : PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {f}) x) ≤ U)
    (hUy : PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {f}) y) ≤ U)
    [IsReduced U.toScheme] [PreirreducibleSpace U] :
    IsDomain (A ⧸ Ideal.span {f}) :=
  domain_of_detecting_preintegral_open _ _
    (principal_quotient_localizations_jointly_injective x y f hx hxy) U hUx hUy

end
end MaximalSeshadri.Hartogs
end


end
end

end OAI
