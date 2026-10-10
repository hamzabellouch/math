import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.SurfaceSquare

namespace OAI

/-! Affine Curves. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem surface_negativity_of_antinef
    (X : ComplexProjectiveVariety) [StalkwiseNormal X.scheme]
    (hX : IsSmoothNfold X 2)
    {Y : Scheme} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X.scheme ⟶ Y) [IsDominant f] [IsProper f] (hf : IsBirationalMorphism f)
    (D : WeilDivisor X.scheme)
    (hexc : ∀ p ∈ D.support, ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1) :
    letI : SmoothOfRelativeDimension 2 X.structureMap := hX
    (∀ C : CurveOn X, (∃ y, ∀ c, f (C.morphism c) = y) →
      cartierCurveDegree (smoothSurfaceWeilCartier X.structureMap D) C ≤ 0) →
    ∀ p, 0 ≤ D p := by
  classical
  let : SmoothOfRelativeDimension 2 X.structureMap := hX
  intro hanti e
  by_contra hneg
  have heD : D e < 0 := lt_of_not_ge hneg
  let P : WeilDivisor X.scheme := D.mapRange (fun z => max z 0) (by simp)
  let N : WeilDivisor X.scheme := D.mapRange (fun z => max (-z) 0) (by simp)
  have hN (p) : 0 ≤ N p := le_max_right _ _
  have hP (p) : 0 ≤ P p := le_max_right _ _
  have hNe : 0 < N e := by
    change 0 < max (-D e) 0
    exact (neg_pos.mpr heD).trans_le (le_max_left _ _)
  have hNsup : N.support ⊆ D.support := by
    intro p hp
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hnz := Finsupp.mem_support_iff.mp hp
    apply hnz
    change max (-D p) 0 = 0
    rw [hz,neg_zero,max_self]
  have hNc : ∀ p ∈ N.support, ∀ x ∈ closure ({p.1} : Set X.scheme), f x = f p.1 :=
    fun p hp => hexc p (hNsup hp)
  have he := hexc e (Finsupp.mem_support_iff.mpr (ne_of_lt heD))
  obtain ⟨J,hJ⟩ := exists_ampleDivisor_of_projective X
  obtain ⟨ε,hε,hbound⟩ := exceptional_uniform_negative_square X hX f hf J hJ e he
  have hNN := hbound N hNc
  have hNNneg : surfaceIntersection X.structureMap
      (smoothSurfaceWeilCartier X.structureMap N)
      (smoothSurfaceWeilCartier X.structureMap N) < 0 := by
    have hNeR : (0 : ℝ) < N e := by exact_mod_cast hNe
    have hstrict : -ε * (N e : ℝ)^2 < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hε) (sq_pos_of_pos hNeR)
    exact_mod_cast hNN.trans_lt hstrict
  have hNP : 0 ≤ surfaceIntersection X.structureMap
      (smoothSurfaceWeilCartier X.structureMap N)
      (smoothSurfaceWeilCartier X.structureMap P) := by
    apply surfaceIntersection_effective_disjoint X.structureMap _ _ hN hP
    intro p hNp
    change max (D p) 0 = 0
    change max (-D p) 0 ≠ 0 at hNp
    omega
  have hND : surfaceIntersection X.structureMap
      (smoothSurfaceWeilCartier X.structureMap N)
      (smoothSurfaceWeilCartier X.structureMap D) ≤ 0 := by
    unfold surfaceIntersection Finsupp.sum
    apply Finset.sum_nonpos
    intro p hp
    change N p * surfaceCartierPrimeDegree X.structureMap
      (smoothSurfaceWeilCartier X.structureMap D) p ≤ 0
    apply mul_nonpos_of_nonneg_of_nonpos (hN p)
    rw [surfaceCartierPrimeDegree_eq_cartierCurveDegree X hX]
    apply hanti
    refine ⟨f p.1,fun c => hNc p hp _ ?_⟩
    rw [← pointClosure_range]
    exact ⟨_,rfl⟩
  have hsplit : D = P - N := by
    ext p
    change D p = max (D p) 0 - max (-D p) 0
    omega
  have hrepr := congrArg (smoothSurfaceWeilCartier X.structureMap) hsplit
  rw [map_sub] at hrepr
  have heq : surfaceIntersection X.structureMap
      (smoothSurfaceWeilCartier X.structureMap N)
      (smoothSurfaceWeilCartier X.structureMap D) =
      surfaceIntersection X.structureMap
      (smoothSurfaceWeilCartier X.structureMap N)
      (smoothSurfaceWeilCartier X.structureMap P) -
      surfaceIntersection X.structureMap
      (smoothSurfaceWeilCartier X.structureMap N)
      (smoothSurfaceWeilCartier X.structureMap N) := by
    change (surfaceIntersectionHom X.structureMap
      (smoothSurfaceWeilCartier X.structureMap N)) _ = _
    rw [hrepr,map_sub]
    rfl
  omega
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne

theorem ringKrullDim_eq_of_integral_faithful (R S : Type*)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.IsIntegral R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
      (fun I J hIJ => Ideal.IsIntegral.under_lt_under hIJ)
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    unfold Order.krullDim
    apply iSup_le
    intro l
    obtain ⟨P,hP,hPre⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (R := R) (S := S) l.head.asIdeal (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)]
        exact bot_le)
    have := hP
    have : P.LiesOver l.head.asIdeal := ⟨hPre.symm⟩
    obtain ⟨L,hL,-,-⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact le_iSup_of_le L (by rw [hL])
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
universe u

theorem finiteType_dimension_trdeg (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] :
    ∃ n : ℕ, ringKrullDim R = n ∧ Algebra.trdeg k R = n := by
  obtain ⟨n,g,hg,hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let B := MvPolynomial (Fin n) k
  let : Algebra B R := g.toRingHom.toAlgebra
  have : IsScalarTower k B R := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).mpr hg
  have : Module.Finite B R := hfin
  have hd : ringKrullDim R = n := by
    rw [ringKrullDim_eq_of_integral_faithful B R]
    simp [B]
  have ht : Algebra.trdeg k R = n := by
    have h := trdeg_add_eq k B (A := R)
    simpa [B, trdeg_eq_zero] using h.symm
  exact ⟨n,hd,ht⟩

theorem finiteType_dimension_le_one_iff (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] :
    ringKrullDim R ≤ 1 ↔ Algebra.trdeg k R ≤ 1 := by
  obtain ⟨n,hd,ht⟩ := finiteType_dimension_trdeg k R
  rw [hd,ht]
  norm_cast
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
theorem affine_functionField_trdeg (sX : X ⟶ Spec (.of k)) (U : X.Opens)
    [Nonempty U] (hU : IsAffineOpen U) :
    let := schemeOpenAlgebra sX U
    let := schemeFieldAlgebra (.of k) sX
    Algebra.trdeg k Γ(X,U) = Algebra.trdeg k X.functionField := by
  let := schemeOpenAlgebra sX U
  let := schemeFieldAlgebra (.of k) sX
  have := open_field_scalar_tower sX U
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have : Algebra.IsAlgebraic Γ(X,U) X.functionField :=
    IsLocalization.isAlgebraic X.functionField (nonZeroDivisors Γ(X,U))
  have h := trdeg_add_eq k Γ(X,U) (A := X.functionField)
  simpa only [trdeg_eq_zero,add_zero] using h

theorem coheight_le_one_of_functionField_trdeg (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX]
    (hd : let := schemeFieldAlgebra (.of k) sX; Algebra.trdeg k X.functionField ≤ 1) :
    ∀ x : X, Order.coheight x ≤ 1 := by
  let := schemeFieldAlgebra (.of k) sX
  intro x
  obtain ⟨_,⟨U',hUa,rfl⟩,hx,-⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have : Nonempty U' := ⟨⟨x,hx⟩⟩
  let := schemeOpenAlgebra sX U'
  have : Algebra.FiniteType k Γ(X,U') :=
    (sX.finiteType_appLE (isAffineOpen_top _) hUa (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  have hr : ringKrullDim Γ(X,U') ≤ 1 :=
    (finiteType_dimension_le_one_iff k Γ(X,U')).mpr
      ((affine_functionField_trdeg k sX U' hUa).trans_le hd)
  let y : U' := ⟨x,hx⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := hUa.isLocalization_stalk y
  have hs : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hUa.primeIdealOf y).asIdeal]
    exact (Ideal.height_le_ringKrullDim_of_ne_top
      (hUa.primeIdealOf y).isPrime.ne_top).trans hr
  rw [ringKrullDim_stalk_eq_coheight] at hs
  exact WithBot.coe_le_coe.mp hs
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

theorem coheight_le_one_of_affine_chart (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (hd : ringKrullDim Γ(X,U) ≤ 1) :
    ∀ x : X, Order.coheight x ≤ 1 := by
  let := schemeOpenAlgebra sX U
  let := schemeFieldAlgebra (.of k) sX
  have : Algebra.FiniteType k Γ(X,U) :=
    (sX.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  apply coheight_le_one_of_functionField_trdeg k sX
  change Algebra.trdeg k X.functionField ≤ 1
  rw [← affine_functionField_trdeg k sX U hU]
  exact (finiteType_dimension_le_one_iff k Γ(X,U)).mp hd
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

theorem affine_curve_image (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (R : Type u) [CommRing R] [IsDomain R]
    (f : Spec (.of R) ⟶ X) [IsImmersion f] [QuasiCompact f]
    (hd : ringKrullDim R = 1) :
    IsIntegral f.image ∧ Nontrivial f.image ∧
      (∀ x : f.image, Order.coheight x ≤ 1) := by
  have hI : IsIntegral f.image := integral_image f
  have hN : Nontrivial (Spec (.of R)) := by
    by_contra h
    have : Subsingleton (Spec (.of R)) := not_nontrivial_iff_subsingleton.mp h
    have : Subsingleton (PrimeSpectrum R) := this
    have hle : ringKrullDim R ≤ 0 := Order.krullDim_nonpos_of_subsingleton
    rw [hd] at hle
    norm_num at hle
  have hNi : Nontrivial f.image := f.toImage.isOpenEmbedding.injective.nontrivial
  refine ⟨hI,hNi,?_⟩
  let U := f.toImage ''ᵁ ⊤
  have hUa : IsAffineOpen U := (isAffineOpen_top _).image_of_isOpenImmersion f.toImage
  have : Nonempty U := by
    obtain ⟨x⟩ := (show Nonempty (Spec (.of R)) from inferInstance)
    exact ⟨⟨f.toImage x, ⟨x,trivial,rfl⟩⟩⟩
  apply coheight_le_one_of_affine_chart (f.imageι ≫ sX) U hUa
  let e : Γ(f.image,U) ≃+* R :=
    ((CategoryTheory.Iso.commRingCatIsoToRingEquiv (f.toImage.appIso ⊤)).trans
      (CategoryTheory.Iso.commRingCatIsoToRingEquiv (Scheme.ΓSpecIso (.of R))))
  rw [ringKrullDim_eq_of_ringEquiv e,hd]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace AffineCurveSelection
open Polynomial MvPolynomial
variable {k : Type*} [Field k] [Infinite k] {ι : Type*}

theorem polynomial_line (a : ι → k) (F : MvPolynomial ι k)
    (hF : F ≠ 0) (ha : MvPolynomial.eval a F = 0) :
    ∃ e : MvPolynomial ι k →ₐ[k] Polynomial k,
      Function.Surjective e ∧
      (Polynomial.aeval (0 : k)).comp e = MvPolynomial.aeval a ∧ e F ≠ 0 := by
  classical
  obtain ⟨b,hb⟩ : ∃ b : ι → k, MvPolynomial.eval b F ≠ 0 := by
    by_contra! h
    exact hF (MvPolynomial.funext (by simpa only [map_zero] using h))
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  obtain ⟨i,hi⟩ : ∃ i, b i - a i ≠ 0 := by
    by_contra! h
    apply hab
    funext j
    exact (sub_eq_zero.mp (h j)).symm
  let e : MvPolynomial ι k →ₐ[k] Polynomial k :=
    MvPolynomial.aeval (fun i => Polynomial.C (a i) + Polynomial.X * Polynomial.C (b i - a i))
  have hzero : (Polynomial.aeval (0 : k)).comp e = MvPolynomial.aeval a := by
    ext i
    simp only [AlgHom.comp_apply, e, MvPolynomial.aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, zero_mul, add_zero,
      Algebra.algebraMap_self, RingHom.id_apply]
  have hone : (Polynomial.aeval (1 : k)).comp e = MvPolynomial.aeval b := by
    ext i
    simp only [AlgHom.comp_apply, e, MvPolynomial.aeval_X, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, add_sub_cancel]
  have hX : ∃ p, e p = (Polynomial.X : Polynomial k) := by
    refine ⟨(MvPolynomial.X i - MvPolynomial.C (a i)) * MvPolynomial.C (b i - a i)⁻¹, ?_⟩
    simp only [map_mul, map_sub, e, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Polynomial.algebraMap_eq]
    rw [← Polynomial.C_sub,add_sub_cancel_left,mul_assoc,← Polynomial.C_mul,mul_inv_cancel₀ hi,
      Polynomial.C_1,mul_one]
  have hsurj : Function.Surjective e := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨p',hp'⟩ := hp
      obtain ⟨q',hq'⟩ := hq
      exact ⟨p'+q', by rw [map_add,hp',hq']⟩
    | monomial n c =>
      obtain ⟨v,hv⟩ := hX
      refine ⟨MvPolynomial.C c * v^n, ?_⟩
      rw [map_mul,map_pow,hv]
      simp only [e,MvPolynomial.aeval_C,Polynomial.algebraMap_eq]
      exact Polynomial.C_mul_X_pow_eq_monomial
  refine ⟨e,hsurj,hzero,?_⟩
  intro he
  apply hb
  have h := congrArg (fun f : MvPolynomial ι k →ₐ[k] k => f F) hone
  change MvPolynomial.aeval b F = 0
  simpa only [AlgHom.comp_apply, he, map_zero] using h.symm
end AffineCurveSelection
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne.AffineCurveSelection
open Polynomial MvPolynomial
variable {k R : Type*} [Field k] [Infinite k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

theorem affine_curve_through_point (a : R →ₐ[k] k) (h : R)
    (hh : h ≠ 0) (ha : a h = 0) :
    ∃ p : Ideal R, p.IsPrime ∧ p ≤ RingHom.ker a ∧ h ∉ p ∧
      ringKrullDim (R ⧸ p) = 1 := by
  classical
  obtain ⟨n,g,hg,hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let B := MvPolynomial (Fin n) k
  let : Algebra B R := g.toRingHom.toAlgebra
  have : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).mpr hg
  have : Module.Finite B R := hfin
  let I : Ideal R := Ideal.span {h}
  have hI : I.comap (algebraMap B R) ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hh (Ideal.subset_span (Set.mem_singleton h))
      (Algebra.IsIntegral.isIntegral h)
  obtain ⟨F,hFI,hF⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hfa : (a.comp g) F = 0 := by
    have hgF : g F ∈ I := hFI
    have hIk : I ≤ RingHom.ker a := by
      change Ideal.span {h} ≤ RingHom.ker a
      rw [Ideal.span_le]
      intro r hr
      obtain rfl := Set.mem_singleton_iff.mp hr
      exact ha
    exact hIk hgF
  let v : Fin n → k := fun i => a (g (MvPolynomial.X i))
  have hav : a.comp g = MvPolynomial.aeval v := by ext i; simp only [AlgHom.comp_apply,MvPolynomial.aeval_X]; rfl
  have hFv : MvPolynomial.eval v F = 0 := by
    rw [hav] at hfa
    exact hfa
  obtain ⟨e,he,hzero,hFe⟩ := polynomial_line v F hF hFv
  let Q : Ideal B := RingHom.ker e
  let M : Ideal R := RingHom.ker a
  have : Q.IsPrime := RingHom.ker_isPrime e
  have : M.IsPrime := RingHom.ker_isPrime a
  have hQM : Q ≤ M.under B := by
    intro r hr
    change a (g r) = 0
    have her : e r = 0 := hr
    have hz := congrArg (fun f : B →ₐ[k] k => f r) hzero
    rw [← hav] at hz
    simpa only [AlgHom.comp_apply,her,map_zero] using hz.symm
  obtain ⟨p,hp,hprime,hP⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (R := B) (S := R) (p := Q) (q := M.under B) M hQM
  have := hprime
  have := hP
  have hhp : h ∉ p := by
    intro hmem
    have hIp : I ≤ p := Ideal.span_le.mpr (by simpa using hmem)
    have hFQ : F ∈ Q := (Ideal.mem_of_liesOver p Q F).mpr (hIp hFI)
    exact hFe hFQ
  have hdB : Ring.DimensionLEOne (B ⧸ Q) := Ring.DimensionLEOne.of_ringEquiv
    (RingHom.quotientKerEquivOfSurjective (f := e.toRingHom) he)
  have := hdB
  have hdR : Ring.DimensionLEOne (R ⧸ p) := Ring.DimensionLEOne.of_isIntegral
    (R := B ⧸ Q) (R ⧸ p)
  have := hdR
  have hdim : Ring.KrullDimLE 1 (R ⧸ p) :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mpr (fun I hI hprime => hdR.maximalOfPrime hI hprime)
  refine ⟨p,hprime,hp,hhp,le_antisymm (Ring.krullDimLE_iff.mp hdim) ?_⟩
  let a' : R ⧸ p →+* k := Ideal.Quotient.lift p a.toRingHom (fun r hr => hp hr)
  have hk : RingHom.ker a' ≠ ⊥ := by
    intro hbot
    have hm : Ideal.Quotient.mk p h ∈ RingHom.ker a' := ha
    rw [hbot] at hm
    exact hhp (Ideal.Quotient.eq_zero_iff_mem.mp hm)
  apply Order.one_le_krullDim_iff.mpr
  exact ⟨⊥,⟨RingHom.ker a',RingHom.ker_isPrime a'⟩,
    bot_lt_iff_ne_bot.mpr (fun heq => hk (congrArg PrimeSpectrum.asIdeal heq))⟩
end NumericalDimensionOne.AffineCurveSelection

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable {k R : Type u} [Field k] [Infinite k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R] {X : Scheme.{u}}

theorem affine_global_curve_through_point
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (f : Spec (.of R) ⟶ X) [IsImmersion f] [QuasiCompact f]
    (a : R →ₐ[k] k) (h : R) (hh : h ≠ 0) (ha : a h = 0)
    (Z : Set X) (hZ : f ⁻¹' Z ⊆ PrimeSpectrum.zeroLocus {h}) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X), IsClosedImmersion i ∧ IsIntegral C ∧
      Nontrivial C ∧ (∀ c : C, Order.coheight c ≤ 1) ∧
      f ⟨RingHom.ker a, RingHom.ker_isPrime a⟩ ∈ Set.range i ∧
      ¬ Set.range i ⊆ Z := by
  obtain ⟨p,hp,hpa,hhp,hd⟩ := AffineCurveSelection.affine_curve_through_point a h hh ha
  have := hp
  let q : Spec (.of (R ⧸ p)) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
  have : IsClosedImmersion q := by
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p)))
    exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let g := q ≫ f
  have : IsImmersion g := IsImmersion.comp q f
  obtain ⟨hI,hN,hD⟩ := affine_curve_image sX (R ⧸ p) g hd
  refine ⟨g.image,g.imageι,inferInstance,hI,hN,hD,?_,?_⟩
  · let aq : R ⧸ p →+* k := Ideal.Quotient.lift p a.toRingHom (fun r hr => hpa hr)
    let xq : Spec (.of (R ⧸ p)) := ⟨RingHom.ker aq, RingHom.ker_isPrime aq⟩
    have hqx : q xq = ⟨RingHom.ker a, RingHom.ker_isPrime a⟩ := by
      apply PrimeSpectrum.ext
      ext r
      change aq (Ideal.Quotient.mk p r) = 0 ↔ a r = 0
      rfl
    refine ⟨g.toImage xq, ?_⟩
    have he := congrArg (fun t : Spec (.of (R ⧸ p)) ⟶ X => t xq) g.toImage_imageι
    simpa only [Scheme.Hom.comp_apply, g, hqx] using he
  · intro hsub
    let η : Spec (.of (R ⧸ p)) := ⟨⊥,Ideal.isPrime_bot⟩
    have he := congrArg (fun t : Spec (.of (R ⧸ p)) ⟶ X => t η) g.toImage_imageι
    have hgZ : g η ∈ Z := he ▸ hsub ⟨g.toImage η,rfl⟩
    have hhmem := hZ hgZ (Set.mem_singleton h)
    apply hhp
    change Ideal.Quotient.mk p h = 0 at hhmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hhmem
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
variable {k R : Type*} [Field k] [IsAlgClosed k] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R]

theorem exists_rationalPoint_with_kernel (p : Ideal R) [p.IsMaximal] :
    ∃ a : R →ₐ[k] k, RingHom.ker a = p := by
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  have : Module.Finite k (R ⧸ p) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ p)
  let e : k ≃ₐ[k] (R ⧸ p) := AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ p))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k p), ?_⟩
  change RingHom.ker (e.symm.toRingHom.comp (Ideal.Quotient.mk p)) = p
  rw [RingHom.ker_comp_of_injective _ e.symm.injective, Ideal.mk_ker]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [IsIntegral X]

theorem closed_curve_through_point_avoiding
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (x : X) (hx : IsClosed {x}) (Z : Set X) (hZ : IsClosed Z)
    (hne : Z ≠ Set.univ) (hxZ : x ∈ Z) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X), IsClosedImmersion i ∧ IsIntegral C ∧
      Nontrivial C ∧ (∀ c : C, Order.coheight c ≤ 1) ∧
      x ∈ Set.range i ∧ ¬ Set.range i ⊆ Z := by
  obtain ⟨U,hUa,hxU⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty U := ⟨⟨x,hxU.1⟩⟩
  let R := Γ(X,U)
  let := schemeOpenAlgebra sX U
  have : Algebra.FiniteType k R :=
    (sX.finiteType_appLE (isAffineOpen_top _) hUa (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (.of k)).inv).2)
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let f : Spec R ⟶ X := hUa.fromSpec
  have : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  obtain ⟨y,hy⟩ : ∃ y : Spec R, f y = x := by
    have hr : x ∈ Set.range f := by rw [hUa.range_fromSpec]; exact hxU.1
    exact hr
  have hyclosed : IsClosed {y} := by
    have h := hx.preimage f.continuous
    have he : f ⁻¹' {x} = {y} := by
      ext z
      simp only [Set.mem_preimage,Set.mem_singleton_iff]
      rw [← hy]
      exact f.isOpenEmbedding.injective.eq_iff
    exact he ▸ h
  have hymax : y.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hyclosed
  have := hymax
  obtain ⟨a,ha⟩ := exists_rationalPoint_with_kernel (k := k) y.asIdeal
  obtain ⟨I,hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (f ⁻¹' Z)).mp
    (hZ.preimage f.continuous)
  have hIne : I ≠ ⊥ := by
    intro hbot
    have hfZ : Set.range f ⊆ Z := by
      rintro _ ⟨z,rfl⟩
      have hfull : f ⁻¹' Z = Set.univ := hI.trans (by rw [hbot]; exact PrimeSpectrum.zeroLocus_bot)
      exact Set.eq_univ_iff_forall.mp hfull z
    have hηU : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (show Nonempty U from inferInstance))
    have hηZ : genericPoint X ∈ Z := hfZ (by rw [hUa.range_fromSpec]; exact hηU)
    apply hne
    apply Set.eq_univ_of_univ_subset
    rw [← (genericPoint_spec X)]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηZ) hZ
  obtain ⟨h,hhI,hh⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIne
  have hyI : y ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [← hI]
    change f y ∈ Z
    rwa [hy]
  have hah : a h = 0 := by
    change h ∈ RingHom.ker a
    rw [ha]
    exact hyI hhI
  have hZeq : f ⁻¹' Z ⊆ PrimeSpectrum.zeroLocus {h} := by
    intro z hz r hr
    have hzI : z ∈ PrimeSpectrum.zeroLocus (I : Set R) := hI ▸ hz
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact hzI hhI
  have hey : (⟨RingHom.ker a,RingHom.ker_isPrime a⟩ : PrimeSpectrum R) = y :=
    PrimeSpectrum.ext ha
  obtain ⟨C,i,hi,hCi,hCn,hCd,hxC,hCZ⟩ :=
    affine_global_curve_through_point sX f a h hh hah Z hZeq
  refine ⟨C,i,hi,hCi,hCn,hCd,?_,hCZ⟩
  simpa only [hey,hy] using hxC
end NumericalDimensionOne

end OAI
