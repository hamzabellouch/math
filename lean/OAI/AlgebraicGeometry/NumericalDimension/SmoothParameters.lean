import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.NormalizationRings

namespace OAI

/-! Smooth Parameters. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace LocalSmoothFiber
open IsLocalRing
open scoped TensorProduct
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing R] [Algebra.EssFiniteType R S] [Module.Flat R S]

theorem formallySmooth [Algebra.FormallyUnramified R S] :
    Algebra.FormallySmooth R S := by
  have : Algebra.FormallyEtale (ResidueField R) (ResidueField R ⊗[R] S) :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FinitePresentation R (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
    (P := Algebra.EssFiniteType.subalgebra R S) (Algebra.EssFiniteType.submonoid R S)
end LocalSmoothFiber
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace DVRParameter
open IsLocalRing
variable (k A : Type*) [Field k] [IsAlgClosed k] [CharZero k]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra k A]
  [Algebra.EssFiniteType k A] [Module.Finite k (ResidueField A)]

theorem etale_aeval (t : A) (ht : Irreducible t) :
    letI : Algebra (Polynomial k) A := (Polynomial.aeval t).toRingHom.toAlgebra
    Algebra.FormallyEtale (Polynomial k) A := by
  have httr : Transcendental k t := by
    intro h
    have hi : IsIntegral k t := h.isIntegral
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := k) (K := integralClosure k A)).2 ⟨t, hi⟩
    have he : algebraMap k A c = t := congrArg Subtype.val hc
    by_cases hcz : c = 0
    · exact ht.ne_zero (by simpa [hcz] using he.symm)
    · exact ht.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hcz).map (algebraMap k A))
  let f : Polynomial k →+* A := (Polynomial.aeval t).toRingHom
  let : Algebra (Polynomial k) A := f.toAlgebra
  have : IsScalarTower k (Polynomial k) A :=
    IsScalarTower.of_algebraMap_eq fun c => ((Polynomial.aeval t).commutes c).symm
  let p : Ideal (Polynomial k) := (maximalIdeal A).comap f
  have : p.IsPrime := Ideal.comap_isPrime f _
  let P := Localization.AtPrime p
  have hd (y : p.primeCompl) : IsUnit (f y) := by
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  let g : P →+* A := IsLocalization.lift hd
  let : Algebra P A := g.toAlgebra
  have hcomp (x : Polynomial k) : g (algebraMap (Polynomial k) P x) = f x :=
    IsLocalization.lift_eq hd x
  have : IsScalarTower (Polynomial k) P A :=
    IsScalarTower.of_algebraMap_eq fun c => (hcomp c).symm
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k A c = g (algebraMap (Polynomial k) P (Polynomial.C c))
    rw [hcomp]
    exact (Polynomial.aeval t).commutes c |>.symm
  have hg : Function.Injective g := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective P p.primeCompl_le_nonZeroDivisors).eq_iff]
    exact (transcendental_iff_injective.mp httr).eq_iff.symm
  have : IsLocalHom (algebraMap P A) := ⟨by
    intro x hx
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    apply (IsLocalization.AtPrime.isUnit_mk'_iff P p r s).mpr
    change f r ∉ maximalIdeal A
    rw [IsLocalRing.notMem_maximalIdeal]
    have he : f r = f s * g (IsLocalization.mk' P r s) :=
      (IsLocalization.lift_mk'_spec hd r _ s).mp rfl
    rw [he]
    exact (hd s).mul hx⟩
  have : Module.IsTorsionFree P A :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hg
  have : Module.Flat P A := inferInstance
  have : Algebra.EssFiniteType P A := Algebra.EssFiniteType.of_comp k P A
  have : Module.Finite (ResidueField P) (ResidueField A) :=
    Module.Finite.of_restrictScalars_finite k _ _
  have : CharZero (ResidueField P) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField P)).injective
  have hm : (maximalIdeal P).map (algebraMap P A) = maximalIdeal A := by
    apply le_antisymm
    · exact ((local_hom_TFAE (algebraMap P A)).out 1 3 rfl rfl).mp inferInstance
    · rw [ht.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
      have hx : (Polynomial.X : Polynomial k) ∈ p := by
        change f Polynomial.X ∈ maximalIdeal A
        simpa [f] using (mem_nonunits_iff.mpr ht.not_isUnit)
      have hxP : algebraMap (Polynomial k) P Polynomial.X ∈ maximalIdeal P := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hx
      have hh := Ideal.mem_map_of_mem (algebraMap P A) hxP
      change g (algebraMap (Polynomial k) P Polynomial.X) ∈ _ at hh
      rw [hcomp] at hh
      change (Polynomial.aeval t) Polynomial.X ∈ _ at hh
      simpa only [Polynomial.aeval_X] using hh
  have : Algebra.FormallyUnramified P A := Algebra.FormallyUnramified.of_map_maximalIdeal hm
  have : Algebra.FormallySmooth P A := LocalSmoothFiber.formallySmooth
  have : Algebra.FormallyEtale P A := ⟨inferInstance, inferInstance⟩
  exact Algebra.FormallyEtale.comp (Polynomial k) P A
end DVRParameter
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace CurveEtaleChart
open IsLocalRing
open scoped KaehlerDifferential
universe u
variable (k A : Type u) [Field k] [IsAlgClosed k] [CharZero k]
  [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A]

omit [CharZero k] in
lemma polynomial_dimension : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) := by
  let b : Module.Basis Unit (Polynomial k) Ω[Polynomial k⁄k] :=
    (Module.Basis.singleton Unit (Polynomial k)).map (KaehlerDifferential.polynomialEquiv k).symm
  have : Algebra.IsStandardSmooth k (Polynomial k) :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential b (by
      rintro _ ⟨i, rfl⟩
      exact ⟨Polynomial.X, by simp [b]⟩)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [(KaehlerDifferential.polynomialEquiv k).rank_eq]
  simp

theorem exists_chart (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    ∃ s ∉ p, Algebra.IsStandardSmoothOfRelativeDimension 1 k (Localization.Away s) := by
  let P := Localization.AtPrime p
  have : IsDiscreteValuationRing P :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp _
  have : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance
  have : Algebra.FiniteType k p.ResidueField :=
    Algebra.FiniteType.trans (R := k) (S := A) inferInstance inferInstance
  have : Module.Finite k p.ResidueField := finite_of_finite_type_of_isJacobsonRing k _
  have : Algebra.EssFiniteType A P := Algebra.EssFiniteType.of_isLocalization _ p.primeCompl
  have : Algebra.EssFiniteType k P := Algebra.EssFiniteType.comp k A P
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible P
  obtain ⟨r, d, hr⟩ := IsLocalization.exists_mk'_eq p.primeCompl t
  have hrI : Irreducible (algebraMap A P r) := by
    have e : algebraMap A P r = t * algebraMap A P d := by
      rw [← hr, mul_comm, IsLocalization.mk'_spec']
    rw [e, irreducible_mul_isUnit (IsLocalization.map_units P d)]
    exact ht
  let f : Polynomial k →ₐ[k] A := Polynomial.aeval r
  let : Algebra (Polynomial k) A := f.toAlgebra
  have : IsScalarTower k (Polynomial k) A := .of_algebraMap_eq fun c => (f.commutes c).symm
  have : IsScalarTower k (Polynomial k) P := .to₁₂₄ k (Polynomial k) A P
  have he : (IsScalarTower.toAlgHom k A P).comp f = Polynomial.aeval (algebraMap A P r) := by
    ext
    simp [f]
  have : Algebra.IsEtaleAt (Polynomial k) p := by
    have hh := DVRParameter.etale_aeval k P (algebraMap A P r) hrI
    change Algebra.FormallyEtale (Polynomial k) P
    have heA : (inferInstance : Algebra (Polynomial k) P) =
        (Polynomial.aeval (algebraMap A P r)).toRingHom.toAlgebra := by
      apply Algebra.algebra_ext
      intro x
      have hx := congrArg (fun g : Polynomial k →ₐ[k] P => g x) he
      exact hx
    exact Eq.mp (congrArg (fun I : Algebra (Polynomial k) P =>
      @Algebra.FormallyEtale (Polynomial k) P _ _ I) heA.symm) hh
  have : Algebra.FiniteType (Polynomial k) A := Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation (Polynomial k) A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨s, hsp, hs⟩ := Algebra.exists_etale_of_isEtaleAt (R := Polynomial k) p
  have : Algebra.Etale (Polynomial k) (Localization.Away s) := hs
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (Polynomial k) (Localization.Away s) :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp hs
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (Polynomial k) := polynomial_dimension k
  exact ⟨s, hsp, by simpa using
    (Algebra.IsStandardSmoothOfRelativeDimension.trans (R := k) (S := Polynomial k)
      (T := Localization.Away s) 1 0)⟩
end CurveEtaleChart
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u

theorem smooth_dimension_one_of_dedekind
    (k A : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : ¬ IsField A) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
  change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap k A)
  rw [RingHom.locally_iff_span_eq_top]
  by_contra hn
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hn
  let := hp
  obtain ⟨s, hsp, hs⟩ := CurveEtaleChart.exists_chart k A p
    (Ring.ne_bot_of_isMaximal_of_not_isField hp hA)
  apply hsp
  apply hle
  apply Ideal.subset_span
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap A (Localization.Away s)).comp (algebraMap k A))
  rw [← IsScalarTower.algebraMap_eq]
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr hs
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem integrallyClosed_affine_of_stalks
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X,U) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let q : Spec Γ(X,U) := ⟨p, hp.isPrime⟩
  have : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec q)) := hN _
  let e := (asIso (hU.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv
  have : IsIntegrallyClosed ((Spec Γ(X,U)).presheaf.stalk q) :=
    IsIntegrallyClosed.of_equiv e
  let : Algebra Γ(X,U) ((Spec Γ(X,U)).presheaf.stalk q) :=
    StructureSheaf.stalkAlgebra Γ(X,U) q
  let : IsLocalization.AtPrime ((Spec Γ(X,U)).presheaf.stalk q) p :=
    StructureSheaf.IsLocalization.to_stalk Γ(X,U) q
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv p.primeCompl ((Spec Γ(X,U)).presheaf.stalk q)
      (Localization.AtPrime p)).toRingEquiv

theorem dedekind_affine_of_stalks [IsLocallyNoetherian X]
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ∀ x : X, Order.coheight x ≤ 1)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsDedekindDomain Γ(X,U) := by
  have : IsIntegrallyClosed Γ(X,U) := integrallyClosed_affine_of_stalks hN hU
  have : IsNoetherianRing Γ(X,U) := IsLocallyNoetherian.component_noetherian ⟨U,hU⟩
  have hdim : ringKrullDim Γ(X,U) ≤ 1 := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height]
    apply iSup_le
    intro p
    rw [← PrimeSpectrum.height_eq_orderHeight]
    rw [idealHeight_eq_coheight Γ(X,U) (show Spec Γ(X,U) from p)]
    have he := coheight_eq_of_isOpenImmersion (x := p) hU.fromSpec
    exact WithBot.coe_le_coe.mpr (he ▸ hd (hU.fromSpec p))
  have : Ring.KrullDimLE 1 Γ(X,U) := Ring.krullDimLE_iff.mpr hdim
  have : Ring.DimensionLEOne Γ(X,U) := ⟨fun hp hp' => hp'.isMaximal_of_ne_bot hp⟩
  exact { }

theorem affine_not_isField [JacobsonSpace X] [Nontrivial X]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    ¬ IsField Γ(X,U) := by
  intro hf
  let : Field Γ(X,U) := hf.toField
  have : Subsingleton (PrimeSpectrum Γ(X,U)) := inferInstance
  have : Subsingleton (Spec Γ(X,U)) := inferInstanceAs (Subsingleton (PrimeSpectrum Γ(X,U)))
  have hss : Subsingleton {x : X // x ∈ U} := hU.isoSpec.hom.injective.subsingleton
  obtain ⟨x⟩ := (inferInstance : Nonempty U)
  have hsingle : (U : Set X) = {x.1} := by
    ext y
    exact ⟨fun hy => congrArg Subtype.val (@Subsingleton.elim {x : X // x ∈ U} hss ⟨y, hy⟩ x),
      fun hy => by
        change y ∈ U
        rw [Set.mem_singleton_iff.mp hy]
        exact x.2⟩
  have hc : IsClosed ({x.1} : Set X) :=
    isClosed_singleton_of_isLocallyClosed_singleton ((hsingle ▸ U.isOpen).isLocallyClosed)
  have hη : genericPoint X = x.1 := by
    have hm : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U))
    change genericPoint X ∈ (U : Set X) at hm
    rwa [hsingle, Set.mem_singleton_iff] at hm
  have hηc : IsClosed ({genericPoint X} : Set X) := hη ▸ hc
  have hu : ({genericPoint X} : Set X) = Set.univ := by
    rw [← hηc.closure_eq]
    exact genericPoint_spec X
  have : Subsingleton X := ⟨fun a b => by
    have ha : a = genericPoint X := by
      have hm : a ∈ ({genericPoint X} : Set X) := by rw [hu]; trivial
      exact hm
    have hb : b = genericPoint X := by
      have hm : b ∈ ({genericPoint X} : Set X) := by rw [hu]; trivial
      exact hm
    exact ha.trans hb.symm⟩
  exact not_subsingleton X this

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

theorem smooth_dimension_one_of_normal_curve
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [Nontrivial X]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ∀ x : X, Order.coheight x ≤ 1) :
    SmoothOfRelativeDimension 1 sX := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  apply (HasRingHomProperty.iff_appLE (P := @SmoothOfRelativeDimension 1)).mpr
  rintro ⟨U, hU⟩ ⟨V, hV⟩ e
  by_cases hne : Nonempty V
  · have : Nonempty V := hne
    have hUt : U = ⊤ := by
      apply top_unique
      intro y _
      obtain ⟨v⟩ := hne
      have hev : sX v.1 ∈ U := e v.2
      rwa [Subsingleton.elim (sX v.1) y] at hev
    subst U
    let φ : k →+* Γ(X,V) :=
      (sX.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    let : Algebra k Γ(X,V) := φ.toAlgebra
    have : Algebra.FiniteType k Γ(X,V) := by
      apply RingHom.finiteType_algebraMap.mp
      exact (sX.finiteType_appLE hU hV e).comp
        (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
    have : IsDedekindDomain Γ(X,V) := dedekind_affine_of_stalks hN hd hV
    have hs := smooth_dimension_one_of_dedekind k Γ(X,V) (affine_not_isField hV)
    have hφ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hs
    exact ((HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension 1)).respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (.of k)).inv (sX.appLE ⊤ V e)).mp hφ
  · have hv : V = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      exact hne ⟨⟨x,hx⟩⟩
    subst V
    change RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) _
    rw [RingHom.locally_iff_span_eq_top]
    exact Subsingleton.elim _ _
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem coheight_le_one_of_bounded_embedding
    {α β : Type*} [Preorder α] [Preorder β] [Nonempty β]
    (f : α → β) (hf : StrictMono f) (p : β)
    (hfp : ∀ x, f x ≤ p) (hp : Order.coheight p = 1)
    (hd : ∀ y : β, Order.coheight y ≤ 2) (x : α) :
    Order.coheight x ≤ 1 := by
  have hb : Order.krullDim β ≤ 2 := by
    rw [Order.krullDim_eq_iSup_coheight]
    exact iSup_le (fun y => WithBot.coe_le_coe.mpr (hd y))
  have hh : Order.height p ≤ 1 := by
    have ht : (Order.height p + Order.coheight p : ℕ∞) ≤ 2 := by
      apply WithBot.coe_le_coe.mp
      exact (WithBot.coe_le_coe.mpr (le_iSup
        (fun y => Order.height y + Order.coheight y) p)).trans
        (by rwa [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := β)] at hb)
    rw [hp] at ht
    exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp ht
  let g : α → Set.Iic p := fun y => ⟨f y, hfp y⟩
  have hg : StrictMono g := fun _ _ h => hf h
  have hc : Order.krullDim α ≤ (Order.height p : WithBot ℕ∞) := by
    rw [Order.height_eq_krullDim_Iic]
    exact Order.krullDim_le_of_strictMono g hg
  exact WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans
    (hc.trans (WithBot.coe_le_coe.mpr hh)))

open AlgebraicGeometry CategoryTheory

theorem strictMono_of_locallyQuasiFinite {X Y : Scheme}
    (f : X ⟶ Y) [LocallyQuasiFinite f] : StrictMono f := by
  intro x y hxy
  apply lt_iff_le_not_ge.mpr
  refine ⟨hxy.le.map f.continuous, ?_⟩
  intro hyx
  have he : f x = f y := (Specializes.antisymm hyx (hxy.le.map f.continuous)).eq
  have hd := f.isDiscrete_preimage_singleton (f x)
  have hxy' : y ⤳ x := hxy.le
  have hexy := hd.eq_of_specializes hxy' (show y ∈ f ⁻¹' {f x} from he.symm)
    (show x ∈ f ⁻¹' {f x} from rfl)
  exact hxy.ne hexy.symm

theorem coheight_le_of_locallyQuasiFinite {X Y : Scheme}
    (f : X ⟶ Y) [LocallyQuasiFinite f] (x : X) :
    Order.coheight x ≤ Order.coheight (f x) := by
  exact Order.coheight_le_coheight_apply_of_strictMono f
    (strictMono_of_locallyQuasiFinite f) x
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {X : Scheme.{u}} [IsIntegral X] [Nontrivial X] [QuasiSeparatedSpace X]
variable (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]

omit [Nontrivial X] [QuasiSeparatedSpace X] in

theorem surjective_genericNormalization :
    Surjective (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  let f := X.fromSpecStalk (genericPoint X)
  have : IsDominant f := by
    constructor
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
    rw [← (genericPoint_spec X)]
    apply closure_mono
    rintro y rfl
    exact ⟨IsLocalRing.closedPoint X.functionField, Scheme.fromSpecStalk_closedPoint⟩
  have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
    simpa only [Scheme.Hom.toNormalization_fromNormalization] using (inferInstance : IsDominant f)
  have : IsDominant f.fromNormalization := IsDominant.of_comp f.toNormalization f.fromNormalization
  infer_instance

theorem smooth_genericNormalization
    (hd : ∀ x : X, Order.coheight x ≤ 1) :
    SmoothOfRelativeDimension 1
      ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ sX) := by
  let f := X.fromSpecStalk (genericPoint X)
  have : AlgebraicGeometry.IsFinite f.fromNormalization := finite_genericNormalization sX
  have : IsIntegral f.normalization := integral_genericNormalization
  have : Surjective f.fromNormalization := surjective_genericNormalization
  have : Nontrivial f.normalization := f.fromNormalization.surjective.nontrivial
  apply smooth_dimension_one_of_normal_curve
  · exact fun x => (genericNormalization_stalk x).2
  · exact fun x => (coheight_le_of_locallyQuasiFinite f.fromNormalization x).trans (hd _)

omit [IsAlgClosed k] [Nontrivial X] [LocallyOfFiniteType sX] in

theorem proper_genericNormalization [IsProper sX] :
    IsProper ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ sX) := by
  have : AlgebraicGeometry.IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization :=
    finite_genericNormalization sX
  infer_instance

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace EtaleRegular
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] [Module.Flat R S]
include R in

theorem regular_local : IsRegularLocalRing S := by
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hspan : (maximalIdeal S).spanFinrank ≤ (maximalIdeal R).spanFinrank := by
    rw [← hmax]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
  have hlies : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  have hd : (maximalIdeal R).height ≤ (maximalIdeal S).height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ (maximalIdeal R).spanFinrank := by
      exact_mod_cast hspan
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := by
      rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
      exact_mod_cast hd
end EtaleRegular
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace EtaleRegular
variable {R S : Type*} [CommRing R] [CommRing S]
    [IsRegularRing R] [Algebra R S] [Algebra.Etale R S]
include R in

theorem regular_ring : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isRegularRing_iff.mpr
  intro q hq
  let p := q.under R
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FormallyEtale R (Localization.AtPrime q) :=
    .comp R S _
  have : Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q) :=
    .localization_base p.primeCompl
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_comp R _ _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q)).mpr inferInstance
  exact regular_local (R := Localization.AtPrime p)
end EtaleRegular
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

universe u

theorem regular_stalk_of_smooth_dimension
    {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  obtain ⟨g, _, hg⟩ := hs.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin n) k) Γ(X, U) := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, U) := hg
  have : IsRegularRing Γ(X, U) := EtaleRegular.regular_ring (R := MvPolynomial (Fin n) k)
  let y : U := ⟨x, hxU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := hU.isLocalization_stalk y
  let p := (hU.primeIdealOf y).asIdeal
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk x)).toRingEquiv
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem polynomial_maximal_height (k : Type*) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsMaximal] : p.height = n := by
  induction n with
  | zero =>
    have hdim : (p.height : WithBot ℕ∞) ≤ 0 := by
      have h := Ideal.height_le_ringKrullDim_of_ne_top (inferInstance : p.IsMaximal).ne_top
      simpa using h
    simpa using le_antisymm (WithBot.coe_le_coe.mp hdim) (bot_le : 0 ≤ p.height)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
    let P := p.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q := P.comap (Polynomial.C : MvPolynomial (Fin n) k →+* _)
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver q := ⟨rfl⟩
    rw [← e.height_map p, Polynomial.height_eq_height_add_one q P, ih q]
    simp
end NumericalDimensionOne

end OAI
