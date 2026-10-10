import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.ProjectiveCoordinates

namespace OAI

/-! Boundary Discrepancies. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u v w
lemma quotient_ringSmooth_of_affine_subscheme
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (s : X ⟶ Y)
    (J : Ideal Γ(X,⊤))
    [Smooth ((Scheme.IdealSheafData.ofIdealTop J).subschemeι ≫ s)] :
    ((Ideal.Quotient.mk J).comp s.appTop.hom).Smooth := by
  let I := Scheme.IdealSheafData.ofIdealTop J
  let U : X.affineOpens := ⟨⊤,isAffineOpen_top X⟩
  have : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have h := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp
    (inferInstance : Smooth (I.subschemeι ≫ s))
  change RingHom.Smooth (I.subschemeι.appTop.hom.comp s.appTop.hom) at h
  have he : Function.Bijective (I.subschemeObjIso U).hom.hom :=
    (I.subschemeObjIso U).commRingCatIsoToRingEquiv.bijective
  have h' := h.comp (RingHom.Smooth.of_bijective he)
  have happ := I.subschemeι_app U
  change I.subschemeι.appTop = _ at happ
  erw [happ,CommRingCat.hom_comp] at h'
  have h'' : ((Ideal.Quotient.mk (I.ideal U)).comp s.appTop.hom).Smooth := by
    convert h' using 1
    ext x
    exact ((I.subschemeObjIso U).inv_hom_id_apply _).symm
  have hI : I.ideal U = J := by simp [I,U,Scheme.IdealSheafData.ofIdealTop_ideal]
  rwa [hI] at h''

theorem formallySmooth_quotient_localization
    {k : Type u} [CommRing k] {R : Type v} [CommRing R]
    {S : Type w} [CommRing S] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] (M : Submonoid R) [IsLocalization M S]
    (I : Ideal R) [Algebra.FormallySmooth k (R ⧸ I)] :
    Algebra.FormallySmooth k (S ⧸ I.map (algebraMap R S)) := by
  let : Algebra.FormallySmooth (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    Algebra.FormallySmooth.of_isLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M)
  let : IsScalarTower k (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change (Ideal.Quotient.mk _) (algebraMap k S x) =
        (Ideal.Quotient.mk _) (algebraMap R S (algebraMap k R x))
      rw [IsScalarTower.algebraMap_apply k R S])
  exact Algebra.FormallySmooth.comp k (R ⧸ I) _
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u

theorem affine_hypersurface_stalk_formallySmooth
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsAffine X]
    (sX : X ⟶ Spec (.of k)) (a : Γ(X,⊤))
    [Smooth ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {a})).subschemeι ≫ sX)]
    (x : X) :
    letI := schemeStalkAlgebra (.of k) sX x
    Algebra.FormallySmooth k ((X.presheaf.stalk x) ⧸
      Ideal.span {X.presheaf.germ ⊤ x (by trivial) a}) := by
  let := schemeStalkAlgebra (.of k) sX x
  let := schemeOpenAlgebra sX (⊤ : X.Opens)
  let y : (⊤ : X.Opens) := ⟨x,trivial⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := open_stalk_scalar_tower sX ⊤ y
  let M := ((isAffineOpen_top X).primeIdealOf y).asIdeal.primeCompl
  let := (isAffineOpen_top X).isLocalization_stalk y
  let I : Ideal Γ(X,⊤) := Ideal.span {a}
  have hQ := quotient_ringSmooth_of_affine_subscheme sX I
  have he : Function.Bijective (Scheme.ΓSpecIso (.of k)).inv.hom :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective
  have h := (RingHom.Smooth.of_bijective he).comp hQ
  have heq : ((Ideal.Quotient.mk I).comp sX.appTop.hom).comp
      (Scheme.ΓSpecIso (.of k)).inv.hom = algebraMap k (Γ(X,⊤) ⧸ I) := by
    ext z
    change (Ideal.Quotient.mk I) (sX.appTop ((Scheme.ΓSpecIso (.of k)).inv z)) =
      (Ideal.Quotient.mk I) (schemeOpenScalar sX ⊤ z)
    congr 1
    change _ = (sX.appTop ≫ X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_rfl)).op) _
    simp
  rw [heq] at h
  have : Algebra.FormallySmooth k (Γ(X,⊤) ⧸ I) :=
    RingHom.formallySmooth_algebraMap.mp h.formallySmooth
  have H := formallySmooth_quotient_localization (k := k) (S := X.presheaf.stalk x) M I
  have hI : I.map (algebraMap Γ(X,⊤) (X.presheaf.stalk x)) =
      Ideal.span {X.presheaf.germ ⊤ x (by trivial) a} := by
    change Ideal.map _ (Ideal.span {a}) = _
    rw [Ideal.map_span,Set.image_singleton]
    rfl
  rw [hI] at H
  exact H
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
lemma open_top_germ {X : Scheme} (U : X.Opens) (x : U) (a : Γ(X,U)) :
    (U.stalkIso x).hom (U.toScheme.presheaf.germ ⊤ x (by trivial) (U.topIso.inv a)) =
      X.presheaf.germ U x x.2 a := by
  erw [← CommRingCat.comp_apply,Scheme.Opens.germ_stalkIso_hom]
  change (U.topIso.inv ≫ X.presheaf.germ (U.ι ''ᵁ ⊤) x.1 _) a = _
  change (X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ U from by rw [U.ι_image_top])).op ≫
    X.presheaf.germ (U.ι ''ᵁ ⊤) x.1 _) a = _
  erw [TopCat.Presheaf.germ_res]

theorem affineOpen_hypersurface_stalk_formallySmooth
    {X : Scheme} [IsIntegral X] (sX : X ⟶ Spec (.of ℂ))
    (U : X.Opens) [IsAffine U] (a : Γ(X,U))
    [Smooth ((Scheme.IdealSheafData.ofIdealTop (Ideal.span {U.topIso.inv a})).subschemeι ≫
      (U.ι ≫ sX))] (x : U) :
    letI := schemeStalkAlgebra (.of ℂ) sX x.1
    Algebra.FormallySmooth ℂ ((X.presheaf.stalk x.1) ⧸
      Ideal.span {X.presheaf.germ U x.1 x.2 a}) := by
  let : Nonempty U := ⟨x⟩
  let := schemeStalkAlgebra (.of ℂ) sX x.1
  let := schemeStalkAlgebra (.of ℂ) (U.ι ≫ sX) x
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x.1,x.2⟩)
  let e : (X.presheaf.stalk x.1) ≃ₐ[ℂ] (U.toScheme.presheaf.stalk x) :=
    { (U.stalkIso x).symm.commRingCatIsoToRingEquiv with
      commutes' := fun z => by
        change (U.stalkIso x).inv (schemeStalkScalar (.of ℂ) sX x.1 z) = _
        rw [U.stalkIso_inv]
        exact dominant_stalk_scalar (.of ℂ) (U.ι ≫ sX) sX U.ι rfl x z }
  have h := affine_hypersurface_stalk_formallySmooth (U.ι ≫ sX) (U.topIso.inv a) x
  let I : Ideal (X.presheaf.stalk x.1) := Ideal.span {X.presheaf.germ U x.1 x.2 a}
  let J : Ideal (U.toScheme.presheaf.stalk x) :=
    Ideal.span {U.toScheme.presheaf.germ ⊤ x (by trivial) (U.topIso.inv a)}
  have he : J = I.map e.toRingHom := by
    change Ideal.span {_} = (Ideal.span {_}).map e.toRingHom
    rw [Ideal.map_span,Set.image_singleton]
    congr 2
    apply (U.stalkIso x).commRingCatIsoToRingEquiv.injective
    change (U.stalkIso x).hom _ = (U.stalkIso x).hom ((U.stalkIso x).inv _)
    simpa only [Iso.inv_hom_id_apply] using open_top_germ U x a
  let q := Ideal.quotientEquivAlg I J e he
  exact Algebra.FormallySmooth.of_equiv q.symm
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct

namespace NumericalDimensionOne
noncomputable section
lemma alternating_update_basis {R M N ι : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M)
    (f : M [⋀^ι]→ₗ[R] N) (x : M) (i : ι) :
    f (Function.update b i x) = b.repr x i • f b := by
  rw [← b.sum_repr x, f.map_update_sum]
  simp only [f.map_update_smul]
  rw [Finset.sum_eq_single i]
  · simp only [Function.update_eq_self,b.sum_repr]
  · intro j _ hji
    rw [f.map_update_self b hji.symm,smul_zero]
  · simp

theorem topDifferentialMap_divisible_of_primitive
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    {n : ℕ} (b : Module.Basis (Fin n) A Ω[A⁄k])
    (g : A) (hprim : ∃ i, IsUnit (b.repr (KaehlerDifferential.D k A g) i))
    (t u : B) (e : ℕ) (heq : algebraMap A B g = u * t^e)
    (v : ⋀[A]^n Ω[A⁄k]) :
    ∃ w : ⋀[B]^n Ω[B⁄k], topDifferentialMap k A B n v = t^(e-1) • w := by
  classical
  cases e with
  | zero => exact ⟨topDifferentialMap k A B n v,by simp⟩
  | succ e =>
    obtain ⟨i,hi⟩ := hprim
    obtain ⟨a,ha⟩ := hi
    obtain ⟨c,hc⟩ := exterior_volume_spans b v
    let F := topDifferentialMap k A B n
    let L := KaehlerDifferential.map k k A B
    let z : Ω[B⁄k] := (e+1) • u • KaehlerDifferential.D k B t + t • KaehlerDifferential.D k B u
    have hd : L (KaehlerDifferential.D k A g) = t^e • z := by
      dsimp [L,z]
      rw [KaehlerDifferential.map_D,heq,Derivation.leibniz,Derivation.leibniz_pow]
      simp only [Nat.add_sub_cancel,smul_add,smul_smul,pow_succ]
      module
    let bv : Fin n → Ω[B⁄k] := fun j => L (b j)
    let w : ⋀[B]^n Ω[B⁄k] := exteriorPower.ιMulti B n (Function.update bv i z)
    have hw : F (exteriorPower.ιMulti A n (Function.update b i (KaehlerDifferential.D k A g))) = t^e • w := by
      rw [topDifferentialMap_ιMulti]
      have he : (fun j => L ((Function.update b i (KaehlerDifferential.D k A g)) j)) =
          Function.update bv i (L (KaehlerDifferential.D k A g)) := by
        ext j
        by_cases hj : j = i <;> simp [hj,bv]
      change exteriorPower.ιMulti B n (fun j => L ((Function.update b i (KaehlerDifferential.D k A g)) j)) = _
      rw [he,hd,(exteriorPower.ιMulti B n).map_update_smul]
    have hvol : F (exteriorPower.ιMulti A n b) =
        t^e • ((↑(a⁻¹) : A) • w) := by
      have hw' := hw
      rw [alternating_update_basis b, map_smul, ← ha] at hw'
      calc
        _ = (↑(a⁻¹) : A) • ((↑a : A) • F (exteriorPower.ιMulti A n b)) := by simp [smul_smul]
        _ = (↑(a⁻¹) : A) • (t^e • w) := by rw [hw']
        _ = _ := smul_comm _ _ _
    refine ⟨c • ((↑(a⁻¹) : A) • w),?_⟩
    rw [hc,map_smul,hvol]
    simpa only [Nat.add_sub_cancel] using smul_comm c (t^e) ((↑(a⁻¹) : A) • w)
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct

namespace NumericalDimensionOne
noncomputable section

theorem smooth_hypersurface_differential_primitive
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k A]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A Ω[A⁄k])
    (g : A) (hg : g ≠ 0) (hgm : g ∈ IsLocalRing.maximalIdeal A)
    [Algebra.FormallySmooth k (A ⧸ Ideal.span {g})] :
    ∃ i, IsUnit (b.repr (KaehlerDifferential.D k A g) i) := by
  classical
  let I : Ideal A := Ideal.span {g}
  let B := A ⧸ I
  let J : Ideal A := RingHom.ker (algebraMap A B)
  have hJI : J = I := Ideal.mk_ker
  have hgJ : g ∈ J := by rw [hJI]; exact Ideal.subset_span (by simp)
  let cg : J.Cotangent := J.toCotangent ⟨g,hgJ⟩
  obtain ⟨l,hl⟩ := (Algebra.FormallySmooth.iff_split_injection
    (R := k) (P := A) (A := B) Ideal.Quotient.mk_surjective).mp inferInstance
  by_contra h
  have hm : ∀ i, b.repr (KaehlerDifferential.D k A g) i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hi => h ⟨i,hi⟩
  have hc : cg ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A J.Cotangent) := by
    have he : cg = l (1 ⊗ₜ[A] KaehlerDifferential.D k A g) := by
      exact (LinearMap.congr_fun hl cg).symm
    rw [he, ← b.sum_repr (KaehlerDifferential.D k A g)]
    simp only [TensorProduct.tmul_sum,TensorProduct.tmul_smul,map_sum,map_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hm i) (Submodule.mem_top))
  have ht : (⊤ : Submodule A J.Cotangent) ≤
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A J.Cotangent) := by
    intro x _
    obtain ⟨y,rfl⟩ := J.toCotangent_surjective x
    have hy : g ∣ (y : A) := Ideal.mem_span_singleton.mp (by simpa only [hJI] using y.2)
    obtain ⟨a,ha⟩ := hy
    have he : y = a • (⟨g,hgJ⟩ : J) := by
      apply Subtype.ext
      simpa only [SetLike.val_smul,smul_eq_mul,mul_comm] using ha
    rw [he,map_smul]
    exact Submodule.smul_mem _ a hc
  let : IsNoetherian A J := isNoetherian_of_injective J.subtype Subtype.val_injective
  let : IsNoetherian A J.Cotangent := isNoetherian_of_surjective J.toCotangent (LinearMap.range_eq_top.mpr J.toCotangent_surjective)
  have hz : (⊤ : Submodule A J.Cotangent) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal A) _
      (IsNoetherian.noetherian _) ht (by rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top])
  have hcz : cg = 0 := by
    have hh : cg ∈ (⊤ : Submodule A J.Cotangent) := trivial
    rw [hz] at hh
    exact hh
  have hg2 : g ∈ I^2 := hJI ▸ (J.toCotangent_eq_zero ⟨g,hgJ⟩).mp hcz
  have hdiv : g^2 ∣ g := by
    change g ∈ (Ideal.span {g})^2 at hg2
    rw [Ideal.span_singleton_pow] at hg2
    exact Ideal.mem_span_singleton.mp hg2
  obtain ⟨a,ha⟩ := hdiv
  have hunit : IsUnit g := IsUnit.of_mul_eq_one a (mul_left_cancel₀ hg (by
    simpa only [pow_two,mul_assoc,mul_one] using ha.symm))
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hgm
  exact hgm hunit
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TensorProduct
open TensorProduct

namespace NumericalDimensionOne
noncomputable section

def IsSmoothEffectiveCartierDivisor (X : ComplexProjectiveVariety)
    [StalkwiseNormal X.scheme] (D : WeilDivisor X.scheme) : Prop :=
  IsCartierDivisor D ∧ 0 ≤ D ∧ ∀ x : X.scheme,
    letI := schemeStalkAlgebra (.of ℂ) X.structureMap x
    ∃ a : CartierStalkEquation D x,
      Algebra.FormallySmooth ℂ ((X.scheme.presheaf.stalk x) ⧸ Ideal.span {a.regular})

universe u

lemma formallySmooth_smooth_stalk
    {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n sX] (x : X) :
    letI := schemeStalkAlgebra (.of k) sX x
    Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  let := schemeStalkAlgebra (.of k) sX x
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  let y : U := ⟨x, hxU⟩
  let : Nonempty U := ⟨y⟩
  let := schemeOpenAlgebra sX U
  let : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, U) := hs
  let : Algebra.IsStandardSmooth k Γ(X, U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := open_stalk_scalar_tower sX U y
  let := hU.isLocalization_stalk y
  let : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf y).asIdeal.primeCompl
  exact Algebra.FormallySmooth.comp k Γ(X,U) (X.presheaf.stalk x)

lemma order_stalk_irreducible {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] (p : PrimeDivisor X) (t : X.presheaf.stalk p.1)
    (ht : Irreducible t) : X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField t) p.1 = 1 := by
  let : IsDiscreteValuationRing (X.presheaf.stalk p.1) := dvr_at_prime_divisor p
  have htf : algebraMap (X.presheaf.stalk p.1) X.functionField t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (X.presheaf.stalk p.1) X.functionField).ne ht.ne_zero
  apply (X.ord_eq_iff p.2 htf).mpr
  exact Ring.ordFrac_irreducible ht

lemma order_stalk_unit_mul_pow {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [StalkwiseNormal X] (p : PrimeDivisor X) (t : X.presheaf.stalk p.1)
    (ht : Irreducible t) (u : (X.presheaf.stalk p.1)ˣ) (e : ℕ) :
    X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField (↑u * t^e)) p.1 = e := by
  have htf : algebraMap (X.presheaf.stalk p.1) X.functionField t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (X.presheaf.stalk p.1) X.functionField).ne ht.ne_zero
  rw [map_mul,map_pow,X.ord_mul (show algebraMap (X.presheaf.stalk p.1) X.functionField (↑u) ≠ 0 from
    (u.isUnit.map (algebraMap _ _)).ne_zero) (pow_ne_zero e htf),
    order_stalk_unit p u.isUnit, order_pow _ htf,order_stalk_irreducible p t ht]
  simp

lemma order_stalk_divisible_pow_lower_bound {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [StalkwiseNormal X] (p : PrimeDivisor X)
    (t : X.presheaf.stalk p.1) (ht : Irreducible t) (e : ℕ)
    (c w : X.presheaf.stalk p.1)
    (hc : algebraMap (X.presheaf.stalk p.1) X.functionField c ≠ 0)
    (he : c = t^(e-1) * w) :
    (e : ℤ) ≤ X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField c) p.1 + 1 := by
  have hw : algebraMap (X.presheaf.stalk p.1) X.functionField w ≠ 0 := by
    intro hw
    apply hc
    rw [he,map_mul,hw,mul_zero]
  have htf : algebraMap (X.presheaf.stalk p.1) X.functionField t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective
      (X.presheaf.stalk p.1) X.functionField).ne ht.ne_zero
  have hwpos : 0 ≤ X.ord (algebraMap (X.presheaf.stalk p.1) X.functionField w) p.1 :=
    (ord_nonnegative_iff_regular p _ hw).mpr ⟨w,rfl⟩
  rw [he,map_mul,map_pow,X.ord_mul (pow_ne_zero _ htf) hw,
    order_pow _ htf,order_stalk_irreducible p t ht,mul_one]
  omega

theorem smooth_boundary_discrepancy_bound
    (X Y : ComplexProjectiveVariety) (n : ℕ)
    (hX : IsSmoothNfold X n) (hY : IsSmoothNfold Y n)
    [StalkwiseNormal Y.scheme]
    (f : X.scheme ⟶ Y.scheme) [IsDominant f]
    (hf : f ≫ Y.structureMap = X.structureMap)
    (ω : rationalTopForms (.of ℂ) Y.structureMap n)
    (DX : WeilDivisor X.scheme) (DY : WeilDivisor Y.scheme)
    (hDX : IsCanonicalDivisorOf (.of ℂ) X.structureMap n
      (rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω) DX)
    (hDY : IsCanonicalDivisorOf (.of ℂ) Y.structureMap n ω DY)
    (P : WeilDivisor X.scheme) (hP : IsCartierPullback f DY P)
    (D : WeilDivisor Y.scheme) (hD : IsSmoothEffectiveCartierDivisor Y D)
    (T : WeilDivisor X.scheme) (hT : IsCartierPullback f D T) :
    ∀ p : PrimeDivisor X.scheme, T p ≤ (DX-P) p + 1 := by
  classical
  let : SmoothOfRelativeDimension n X.structureMap := hX
  let : SmoothOfRelativeDimension n Y.structureMap := hY
  let : StalkwiseNormal X.scheme := smoothNormal X hX
  let : StalkwiseNormal Y.scheme := smoothNormal Y hY
  let := schemeFieldAlgebra (.of ℂ) X.structureMap
  let := schemeFieldAlgebra (.of ℂ) Y.structureMap
  let : Algebra Y.scheme.functionField X.scheme.functionField :=
    (dominantFunctionFieldMap f).toAlgebra
  let : IsScalarTower ℂ Y.scheme.functionField X.scheme.functionField :=
    IsScalarTower.of_algebraMap_eq (fun a =>
      (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf a).symm)
  intro p
  change T p ≤ DX p - P p + 1
  obtain ⟨U, hU, hpU, hs⟩ := exists_standard_smooth_chart Y.structureMap n (f p.1)
  let : Nonempty U := ⟨⟨f p.1, hpU⟩⟩
  let := schemeOpenAlgebra Y.structureMap U
  let : Algebra.IsStandardSmoothOfRelativeDimension n ℂ (Y.scheme.presheaf.obj (op U)) := hs
  let : Algebra.IsStandardSmooth ℂ (Y.scheme.presheaf.obj (op U)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let := open_field_scalar_tower Y.structureMap U
  let := functionField_isFractionRing_of_isAffineOpen Y.scheme U hU
  let : Algebra.FormallyEtale (Y.scheme.presheaf.obj (op U)) Y.scheme.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Y.scheme.presheaf.obj (op U)))
  obtain ⟨bU⟩ := nonempty_topDifferential_basis ℂ (Y.scheme.presheaf.obj (op U)) n
  let bF := (topDifferential_isBaseChange ℂ (Y.scheme.presheaf.obj (op U)) Y.scheme.functionField n).basis bU
  let a := bF.repr ω 0
  have heq : ω = a • topDifferentialMap ℂ (Y.scheme.presheaf.obj (op U)) Y.scheme.functionField n (bU 0) := by
    simpa only [bF, IsBaseChange.basis_apply] using basis_singleton_repr bF ω
  have ha : a ≠ 0 := by
    intro h
    exact hDY.1 (by simpa [h] using heq)
  have hDa := canonical_chart_equation Y.structureMap n hDY U hU hs bU a ha heq
  have hPa := hP.order_eq_of_equation ha hDa p hpU
  let := schemeStalkAlgebra (.of ℂ) X.structureMap p.1
  let := stalk_field_scalar_tower (.of ℂ) X.structureMap p.1
  let u : U := ⟨f p.1, hpU⟩
  let := schemeStalkAlgebra (.of ℂ) Y.structureMap (f p.1)
  let := TopCat.Presheaf.algebra_section_stalk Y.scheme.presheaf u
  let := open_stalk_scalar_tower Y.structureMap U u
  let : Algebra (Y.scheme.presheaf.obj (op U)) (X.scheme.presheaf.stalk p.1) :=
    ((f.stalkMap p.1).hom.comp (Y.scheme.presheaf.germ U (f p.1) hpU).hom).toAlgebra
  let : IsScalarTower ℂ (Y.scheme.presheaf.obj (op U)) (X.scheme.presheaf.stalk p.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change schemeStalkScalar (.of ℂ) X.structureMap p.1 z =
      f.stalkMap p.1 (algebraMap (Y.scheme.presheaf.obj (op U)) (Y.scheme.presheaf.stalk (f p.1))
        (algebraMap ℂ (Y.scheme.presheaf.obj (op U)) z))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominant_stalk_scalar (.of ℂ) X.structureMap Y.structureMap f hf p.1 z).symm
  let : Algebra (Y.scheme.presheaf.obj (op U)) X.scheme.functionField :=
    ((dominantFunctionFieldMap f).comp (Y.scheme.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower (Y.scheme.presheaf.obj (op U)) Y.scheme.functionField X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    rfl
  let : IsScalarTower ℂ (Y.scheme.presheaf.obj (op U)) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap ℂ X.scheme.functionField z =
      dominantFunctionFieldMap f
        (algebraMap (Y.scheme.presheaf.obj (op U)) Y.scheme.functionField (algebraMap ℂ (Y.scheme.presheaf.obj (op U)) z))
    rw [← IsScalarTower.algebraMap_apply]
    exact (dominantFunctionFieldMap_scalar (.of ℂ) X.structureMap Y.structureMap f hf z).symm
  let : IsScalarTower (Y.scheme.presheaf.obj (op U)) (X.scheme.presheaf.stalk p.1) X.scheme.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change dominantFunctionFieldMap f (Y.scheme.germToFunctionField U z) =
      algebraMap (X.scheme.presheaf.stalk p.1) X.scheme.functionField
        (f.stalkMap p.1 (Y.scheme.presheaf.germ U (f p.1) hpU z))
    rw [← dominantFunctionFieldMap_algebraMap, Y.scheme.algebraMap_germ_eq_germToFunctionField]
  obtain ⟨bp⟩ := nonempty_smooth_canonical_stalk_basis X.structureMap n p.1
  let v := topDifferentialMap ℂ (Y.scheme.presheaf.obj (op U)) (X.scheme.presheaf.stalk p.1) n (bU 0)
  let c := bp.repr v 0
  have hc : v = c • bp 0 := basis_singleton_repr bp v
  dsimp only [v] at hc
  let cf := algebraMap (X.scheme.presheaf.stalk p.1) X.scheme.functionField c
  have hpull : rationalTopFormPullback (.of ℂ) X.structureMap Y.structureMap f hf n ω =
      (dominantFunctionFieldMap f a * cf) •
        topDifferentialMap ℂ (X.scheme.presheaf.stalk p.1) X.scheme.functionField n (bp 0) := by
    change topDifferentialMap ℂ Y.scheme.functionField X.scheme.functionField n ω = _
    rw [heq, map_smul, ← IsScalarTower.algebraMap_smul X.scheme.functionField a]
    have hcomp₁ := LinearMap.congr_fun (topDifferentialMap_comp ℂ (Y.scheme.presheaf.obj (op U))
      Y.scheme.functionField X.scheme.functionField n) (bU 0)
    have hcomp₂ := LinearMap.congr_fun (topDifferentialMap_comp ℂ (Y.scheme.presheaf.obj (op U))
      (X.scheme.presheaf.stalk p.1) X.scheme.functionField n) (bU 0)
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hcomp₁ hcomp₂
    change _ • _ = _
    rw [hcomp₁, ← hcomp₂, hc, map_smul,
      ← IsScalarTower.algebraMap_smul X.scheme.functionField c, ← mul_smul]
    rfl
  have hprod : dominantFunctionFieldMap f a * cf ≠ 0 := by
    intro h
    exact hDX.1 (by simpa [h] using hpull)
  have hcf : cf ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  obtain ⟨cp, a', ha', heq', hDXp⟩ := hDX.2 p
  have hDXord := canonical_local_order_unique X.structureMap n p _ cp bp a'
    (dominantFunctionFieldMap f a * cf) hDX.1 ha' hprod heq' hpull
  have hcpos : 0 ≤ X.scheme.ord cf p.1 :=
    (ord_nonnegative_iff_regular p cf hcf).mpr ⟨c, rfl⟩
  obtain ⟨g, hgSmooth⟩ := hD.2.2 (f p.1)
  let gX := f.stalkMap p.1 g.regular
  have hgX : algebraMap (X.scheme.presheaf.stalk p.1) X.scheme.functionField gX =
      dominantFunctionFieldMap f g.function := by
    rw [← g.regular_eq, dominantFunctionFieldMap_algebraMap]
  have hTord := hT.order_eq_of_equation g.nonzero g.equation p g.mem_openSet
  have hgXnz : gX ≠ 0 := by
    intro hz
    have hgn : dominantFunctionFieldMap f g.function ≠ 0 := (map_ne_zero _).mpr g.nonzero
    apply hgn
    rw [← hgX,hz,map_zero]
  have hbound : T p ≤ X.scheme.ord cf p.1 + 1 := by
    by_cases hgu : IsUnit g.regular
    · have hzero : T p = 0 := by
        rw [hTord, ← hgX]
        exact order_stalk_unit p (hgu.map (f.stalkMap p.1).hom)
      rw [hzero]
      omega
    let : Algebra.FormallySmooth ℂ (Y.scheme.presheaf.stalk (f p.1)) :=
      formallySmooth_smooth_stalk Y.structureMap n (f p.1)
    let : Algebra.FormallySmooth ℂ
        ((Y.scheme.presheaf.stalk (f p.1)) ⧸ Ideal.span {g.regular}) := hgSmooth
    obtain ⟨bY⟩ := nonempty_smooth_stalk_differential_basis Y.structureMap n (f p.1)
    have hgnz : g.regular ≠ 0 := by
      intro hz
      exact g.nonzero (by rw [← g.regular_eq,hz,map_zero])
    have hgm : g.regular ∈ IsLocalRing.maximalIdeal (Y.scheme.presheaf.stalk (f p.1)) := by
      rwa [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff]
    have hprim := smooth_hypersurface_differential_primitive bY g.regular hgnz hgm
    let : Algebra (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) :=
      (f.stalkMap p.1).hom.toAlgebra
    let : IsScalarTower ℂ (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) := by
      apply IsScalarTower.of_algebraMap_eq
      intro z
      exact (dominant_stalk_scalar (.of ℂ) X.structureMap Y.structureMap f hf p.1 z).symm
    let : IsScalarTower (Y.scheme.presheaf.obj (op U)) (Y.scheme.presheaf.stalk (f p.1))
        (X.scheme.presheaf.stalk p.1) := by
      apply IsScalarTower.of_algebraMap_eq
      intro z
      rfl
    let : IsDiscreteValuationRing (X.scheme.presheaf.stalk p.1) := dvr_at_prime_divisor p
    obtain ⟨t,ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.scheme.presheaf.stalk p.1)
    obtain ⟨e,u,he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hgXnz ht
    obtain ⟨w,hw⟩ := topDifferentialMap_divisible_of_primitive bY g.regular hprim t (↑u) e he
      (topDifferentialMap ℂ (Y.scheme.presheaf.obj (op U)) (Y.scheme.presheaf.stalk (f p.1)) n (bU 0))
    have hvw : v = t^(e-1) • w := by
      have hh := LinearMap.congr_fun (topDifferentialMap_comp ℂ (Y.scheme.presheaf.obj (op U))
        (Y.scheme.presheaf.stalk (f p.1)) (X.scheme.presheaf.stalk p.1) n) (bU 0)
      simp only [LinearMap.comp_apply,LinearMap.restrictScalars_apply] at hh
      exact hh.symm.trans hw
    have hcg : c = t^(e-1) * (bp.repr w 0) := by
      change bp.repr v 0 = _
      rw [hvw,map_smul]
      rfl
    have hTe : T p = (e : ℤ) := by
      rw [hTord,← hgX,he]
      exact order_stalk_unit_mul_pow p t ht u e
    rw [hTe]
    exact order_stalk_divisible_pow_lower_bound p t ht e c (bp.repr w 0) hcf hcg
  rw [hDXp, hDXord, X.scheme.ord_mul ((map_ne_zero _).mpr ha) hcf, hPa]
  omega
end
end NumericalDimensionOne

end OAI
