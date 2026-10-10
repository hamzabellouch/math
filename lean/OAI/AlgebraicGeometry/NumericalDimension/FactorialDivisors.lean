import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.PrimeSpecialization

namespace OAI

/-! Factorial Divisors. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

lemma affine_equation_of_generization_orders (D : WeilDivisor X) (x : X)
    (f : X.functionField)
    (he : ∀ p : PrimeDivisor X, p.1 ⤳ x → D p = X.ord f p.1) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord f p.1 := by
  classical
  let E := D - principalWeilDivisor f
  let Z : Set X := ⋃ p ∈ E.support, closure {p.1}
  have hZ : IsClosed Z := isClosed_biUnion_finset (fun _ _ => isClosed_closure)
  have hx : x ∉ Z := by
    intro hmem
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.mp hmem
    have hpx : p.1 ⤳ x := specializes_iff_mem_closure.mpr hx
    have hzero : E p = 0 := by
      simp only [E, Finsupp.sub_apply, principalWeilDivisor_apply, he p hpx, sub_self]
    exact (Finsupp.mem_support_iff.mp hp) hzero
  obtain ⟨U, hU, hxU, hUZ⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens) from hx)
  refine ⟨U, hU, hxU, ?_⟩
  intro p hp
  have hpzero : E p = 0 := by
    by_contra hn
    apply hUZ hp
    exact Set.mem_iUnion₂.mpr ⟨p, Finsupp.mem_support_iff.mpr hn,
      subset_closure (Set.mem_singleton _)⟩
  exact sub_eq_zero.mp (by simpa only [E, Finsupp.sub_apply,
    principalWeilDivisor_apply] using hpzero)

theorem isCartierDivisor_of_factorial_stalks
    (hfac : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (D : WeilDivisor X) : IsCartierDivisor D := by
  classical
  have hsingle (p : PrimeDivisor X) : IsCartierDivisor (Finsupp.single p 1) := by
    intro x
    by_cases hpx : p.1 ⤳ x
    · let := hfac x
      have hp := generizationPrime_height hpx p.2
      obtain ⟨a, ha⟩ :=
        UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp
      have ha0 : a ≠ 0 := by
        intro hzero
        exact (generizationPrime hpx).ne_bot_of_height_eq_one hp
          (by simpa only [hzero, Ideal.span_singleton_zero] using ha)
      let f := algebraMap (X.presheaf.stalk x) X.functionField a
      have hf : f ≠ 0 := by
        simpa only [f, map_zero] using
          (IsFractionRing.injective (X.presheaf.stalk x) X.functionField).ne ha0
      have he (q : PrimeDivisor X) (hqx : q.1 ⤳ x) :
          Finsupp.single p (1 : ℤ) q = X.ord f q.1 := by
        have ho := order_stalk_generator hpx hqx p.2 q.2 a ha
        simpa only [Finsupp.single_apply, Subtype.ext_iff] using ho.symm
      obtain ⟨U, hU, hx, heq⟩ := affine_equation_of_generization_orders
        (Finsupp.single p 1) x f he
      exact ⟨U, hU, hx, f, hf, heq⟩
    · have he (q : PrimeDivisor X) (hqx : q.1 ⤳ x) :
          Finsupp.single p (1 : ℤ) q = X.ord (1 : X.functionField) q.1 := by
        have hpq : p ≠ q := by rintro rfl; exact hpx hqx
        simp only [Finsupp.single_apply, ite_eq_right hpq, order_one]
      obtain ⟨U, hU, hx, heq⟩ := affine_equation_of_generization_orders
        (Finsupp.single p 1) x 1 he
      exact ⟨U, hU, hx, 1, one_ne_zero, heq⟩
  change D ∈ cartierDivisors (X := X)
  rw [← D.sum_single, Finsupp.sum]
  apply AddSubgroup.sum_mem
  intro p hp
  have he : Finsupp.single p (D p) = (D p) • Finsupp.single p (1 : ℤ) := by
    ext q
    simp [Finsupp.single_apply]
  rw [he]
  exact (cartierDivisors (X := X)).zsmul_mem (hsingle p) (D p)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
section LocalVanishingOrder
variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

lemma exists_local_order_bound {a : A} (ha : a ≠ 0) :
    ∃ r : ℕ, a ∉ IsLocalRing.maximalIdeal A ^ (r + 1) := by
  by_contra h
  push Not at h
  have hm : a ∈ ⨅ r : ℕ, IsLocalRing.maximalIdeal A ^ r := by
    apply Ideal.mem_iInf.mpr
    intro r
    cases r with
    | zero => simp
    | succ r => exact h r
  rw [(IsLocalRing.maximalIdeal A).iInf_pow_eq_bot_of_isLocalRing (by exact Ideal.IsMaximal.ne_top inferInstance)] at hm
  exact ha hm

noncomputable def localVanishingOrder (a : A) (ha : a ≠ 0) : ℕ :=
  by
    classical
    exact Nat.find (exists_local_order_bound ha)

lemma localVanishingOrder_not_mem (a : A) (ha : a ≠ 0) :
    a ∉ IsLocalRing.maximalIdeal A ^ (localVanishingOrder a ha + 1) := by
  classical
  exact Nat.find_spec (exists_local_order_bound ha)

lemma localVanishingOrder_mem_iff (a : A) (ha : a ≠ 0) (r : ℕ) :
    a ∈ IsLocalRing.maximalIdeal A ^ r ↔ r ≤ localVanishingOrder a ha := by
  classical
  constructor
  · intro h
    by_contra hn
    have hle : localVanishingOrder a ha + 1 ≤ r := by omega
    exact localVanishingOrder_not_mem a ha (Ideal.pow_le_pow_right hle h)
  · intro h
    cases r with
    | zero => simp
    | succ r =>
      by_contra hn
      have hmin := Nat.find_min' (exists_local_order_bound ha) hn
      change localVanishingOrder a ha ≤ r at hmin
      omega

lemma localVanishingOrder_unit_mul (a : A) (ha : a ≠ 0) (u : A) (hu : IsUnit u) :
    localVanishingOrder (u * a) ((hu.mul_right_eq_zero.not.mpr ha)) = localVanishingOrder a ha := by
  apply Nat.le_antisymm
  · apply (localVanishingOrder_mem_iff a ha _).mp
    have h := (localVanishingOrder_mem_iff (u * a) ((hu.mul_right_eq_zero.not.mpr ha)) _).mpr le_rfl
    obtain ⟨u, rfl⟩ := hu
    have h' := (IsLocalRing.maximalIdeal A ^ localVanishingOrder (↑u * a)
      ((u.isUnit.mul_right_eq_zero.not.mpr ha))).mul_mem_left (↑(u⁻¹) : A) h
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using h'
  · apply (localVanishingOrder_mem_iff _ _ _).mp
    exact (IsLocalRing.maximalIdeal A ^ localVanishingOrder a ha).mul_mem_left u
      ((localVanishingOrder_mem_iff a ha _).mpr le_rfl)

end LocalVanishingOrder
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace PrincipalLocal
open IsLocalRing
variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem isDomain_of_principal_maximal {t : A}
    (hm : maximalIdeal A = Ideal.span {t}) (ht : ¬IsNilpotent t) : IsDomain A := by
  have hform (a : A) (ha : a ≠ 0) : ∃ (n : ℕ) (u : A), IsUnit u ∧ a = t ^ n * u := by
    let n := localVanishingOrder a ha
    have hn : a ∈ maximalIdeal A ^ n := (localVanishingOrder_mem_iff a ha n).2 le_rfl
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn
    obtain ⟨u, hu⟩ := hn
    refine ⟨n, u, ?_, hu⟩
    by_contra hnu
    have huM : u ∈ maximalIdeal A := mem_nonunits_iff.mpr hnu
    have hat : a ∈ maximalIdeal A ^ (n + 1) := by
      rw [hu, pow_succ]
      apply Ideal.mul_mem_mul
      · rw [hm, Ideal.span_singleton_pow]
        exact Ideal.subset_span (Set.mem_singleton _)
      · exact huM
    exact localVanishingOrder_not_mem a ha hat
  have hpow (n : ℕ) : t ^ n ≠ 0 := fun h => ht ⟨n, h⟩
  have : NoZeroDivisors A := ⟨by
    intro a b hab
    by_contra h
    push Not at h
    obtain ⟨m, u, hu, rfl⟩ := hform a h.1
    obtain ⟨n, v, hv, rfl⟩ := hform b h.2
    have he : t ^ (m+n) * (u*v) = 0 := by
      rw [pow_add]
      calc
        t ^ m * t ^ n * (u * v) = (t ^ m * u) * (t ^ n * v) := by ring
        _ = 0 := hab
    exact hpow (m+n) ((hu.mul hv).mul_left_eq_zero.mp he)⟩
  exact { }
end PrincipalLocal
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace TwoParameters
open IsLocalRing
variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem quotient_principal_domain {x y : A}
    (hm : maximalIdeal A = Ideal.span {x, y})
    (hd : ringKrullDim A = 2) :
    IsDomain (A ⧸ Ideal.span {x}) ∧ IsPrincipalIdealRing (A ⧸ Ideal.span {x}) := by
  let I : Ideal A := Ideal.span {x}
  have hIM : I ≤ maximalIdeal A := by
    rw [hm]
    exact Ideal.span_mono (by simp)
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hIM
  have : I.IsTwoSided := inferInstance
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hmax : maximalIdeal (A ⧸ I) = Ideal.span {q y} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective, hm,
      Ideal.map_span]
    have hx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simp only [Set.image_insert_eq, Set.image_singleton, hx, Ideal.span_insert_zero]
  have hyn : ¬IsNilpotent (q y) := by
    rintro ⟨n, hn⟩
    have hyI : y ^ n ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_pow] using hn)
    have hrad : I.radical = maximalIdeal A := by
      apply le_antisymm
      · exact (Ideal.IsPrime.radical_le_iff (inferInstance : (maximalIdeal A).IsPrime)).mpr hIM
      · rw [hm, Ideal.span_le]
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact Ideal.le_radical (Ideal.subset_span (Set.mem_singleton _))
        · have he : z = y := Set.mem_singleton_iff.mp hz
          subst z
          exact ⟨n, hyI⟩
    have hmin : maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, hrad]
      exact ⟨⟨inferInstance, le_rfl⟩, fun _ h _ => h.2⟩
    have hh := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I (maximalIdeal A) hmin
    have hh' : (↑(maximalIdeal A).height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hh
    rw [maximalIdeal_height_eq_ringKrullDim, hd] at hh'
    norm_num at hh'
  have hdQ : IsDomain (A ⧸ I) := PrincipalLocal.isDomain_of_principal_maximal hmax hyn
  have : IsDomain (A ⧸ I) := hdQ
  refine ⟨hdQ, ?_⟩
  have hpr : (maximalIdeal (A ⧸ I)).IsPrincipal := ⟨⟨q y, hmax⟩⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (A ⧸ I)).out 5 1).mp hpr
end TwoParameters
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace PrincipalQuotientLift
open IsLocalRing
variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem principal_of_quotient (p : Ideal A) [p.IsPrime] (x : A)
    (hx : x ∈ maximalIdeal A) (hxp : x ∉ p)
    [IsPrincipalIdealRing (A ⧸ Ideal.span {x})] : p.IsPrincipal := by
  let I : Ideal A := Ideal.span {x}
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  let g0 := Submodule.IsPrincipal.generator (p.map q)
  have hg0 : g0 ∈ p.map q := Submodule.IsPrincipal.generator_mem _
  obtain ⟨g, hg, hqg⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hg0
  have hmap : p.map q = Ideal.span {q g} := by
    rw [hqg]
    exact (Ideal.span_singleton_generator (p.map q)).symm
  have hle : p ≤ Ideal.span {g} ⊔ maximalIdeal A • p := by
    intro r hr
    have hqr : q r ∈ Ideal.span {q g} := hmap ▸ Ideal.mem_map_of_mem q hr
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.mp hqr
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c0
    have hsub : r - c * g ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (r - c * g) = 0
      rw [map_sub, map_mul, hc0, sub_self]
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hsub
    have hdp : d ∈ p := by
      have hprod : x * d ∈ p := hd ▸ p.sub_mem hr (p.mul_mem_left c hg)
      exact (Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hprod).resolve_left hxp
    apply Submodule.mem_sup.mpr
    refine ⟨c*g, Ideal.mem_span_singleton'.mpr ⟨c,rfl⟩,
      x*d, Submodule.smul_mem_smul hx hdp, ?_⟩
    rw [← hd]
    ring
  have hgen : p ≤ Ideal.span {g} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian p)
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]) hle
  exact ⟨⟨g, le_antisymm hgen (by simpa only [Ideal.span_singleton_le_iff_mem] using hg)⟩⟩
end PrincipalQuotientLift
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace SurfaceFactorial
open IsLocalRing
variable {A : Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]

theorem factorial_of_dimension_two (hd : ringKrullDim A = 2) :
    UniqueFactorizationMonoid A := by
  classical
  have hsr : (maximalIdeal A).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hd] at h
    exact_mod_cast h
  obtain ⟨s, hs, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal A)).exists_span_finset_card_eq_spanFinrank
  rw [hsr] at hs
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  have hm : maximalIdeal A = Ideal.span {x,y} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hspan.symm
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro p hp hheight
  have hpm : p ≠ maximalIdeal A := by
    intro he
    have h := maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← he, hheight, hd] at h
    norm_num at h
  have hle : p ≤ maximalIdeal A := le_maximalIdeal (Ideal.IsPrime.ne_top hp)
  have hnot : x ∉ p ∨ y ∉ p := by
    by_contra hn
    push Not at hn
    apply hpm
    apply le_antisymm hle
    rw [hm, Ideal.span_le]
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hn.1
    · exact (Set.mem_singleton_iff.mp hz) ▸ hn.2
  rcases hnot with hx | hy
  · have := (TwoParameters.quotient_principal_domain hm hd).2
    exact PrincipalQuotientLift.principal_of_quotient p x
      (by rw [hm]; exact Ideal.subset_span (by simp)) hx
  · have hm' : maximalIdeal A = Ideal.span {y,x} := by simpa only [Set.pair_comm] using hm
    have := (TwoParameters.quotient_principal_domain hm' hd).2
    exact PrincipalQuotientLift.principal_of_quotient p y
      (by rw [hm]; exact Ideal.subset_span (by simp)) hy
end SurfaceFactorial
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
namespace SurfaceFactorial
open IsLocalRing
variable {A : Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]

theorem factorial_of_dimension_le_two (hd : ringKrullDim A ≤ 2) :
    UniqueFactorizationMonoid A := by
  have hsr := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
  have hn : (maximalIdeal A).spanFinrank ≤ 2 := by
    rw [← hsr] at hd
    exact_mod_cast hd
  interval_cases he : (maximalIdeal A).spanFinrank
  · have hm : maximalIdeal A = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp he
    have hf : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hm
    let := hf.toField
    infer_instance
  · have hp : (maximalIdeal A).IsPrincipal :=
      ((maximalIdeal A).spanFinrank_eq_one_iff.mp he).1
    have : IsPrincipalIdealRing A :=
      ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 5 1).mp hp
    infer_instance
  · apply factorial_of_dimension_two
    rw [← hsr]
    rfl
end SurfaceFactorial
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

universe u

theorem factorial_stalk_of_smooth_surface
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sX] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  have := regular_stalk_of_smooth_dimension sX 2 x
  apply SurfaceFactorial.factorial_of_dimension_le_two
  rw [ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_le_coe.mpr (coheight_le_of_smooth_dimension sX 2 x)
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem isCartierDivisor_smooth_surface
    {k : Type*} [Field k] {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [CompactSpace X]
    (sX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sX]
    (D : WeilDivisor X) : IsCartierDivisor D := by
  exact isCartierDivisor_of_factorial_stalks (factorial_stalk_of_smooth_surface sX) D
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem pointClosure_affineIdeal {X : Scheme} (x : X) {U : X.Opens}
    (hU : IsAffineOpen U) (hxU : x ∈ U) :
    (X.fromSpecResidueField x).ker.ideal ⟨U,hU⟩ =
      (hU.primeIdealOf ⟨x,hxU⟩).asIdeal := by
  let f := X.fromSpecResidueField x
  let z : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  have hz : f z ∈ U := by simpa [f] using hxU
  have hpre : f ⁻¹ᵁ U = ⊤ := by
    ext t
    simp [f, hxU]
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := by rw [hpre]; exact isAffineOpen_top _
  have hfield : IsField Γ(Spec (X.residueField x), f ⁻¹ᵁ U) := by
    rw [hpre]
    exact (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField _)
  let := hfield.toField
  have hbot : (hV.primeIdealOf ⟨z,hz⟩).asIdeal = ⊥ :=
    (Ideal.eq_bot_or_top _).resolve_right (hV.primeIdealOf ⟨z,hz⟩).isPrime.ne_top
  have he := congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl hz)
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (f.app U).hom = _
  simpa [PrimeSpectrum.comap_asIdeal, hbot, RingHom.ker_eq_comap_bot, Scheme.Hom.appLE, f] using he
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory

theorem closedImmersion_stalk_ker {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) {U : Y.Opens} (hU : IsAffineOpen U) (hx : f x ∈ U) :
    RingHom.ker (f.stalkMap x).hom =
      (f.ker.ideal ⟨U,hU⟩).map (Y.presheaf.germ U (f x) hx).hom := by
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let := Y.presheaf.algebra_section_stalk ⟨f x,hx⟩
  let := X.presheaf.algebra_section_stalk (⟨x,hx⟩ : V)
  have := hU.isLocalization_stalk ⟨f x,hx⟩
  have := hV.isLocalization_stalk ⟨x,hx⟩
  let p := (hU.primeIdealOf ⟨f x,hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x,hx⟩).asIdeal
  let g := (f.app U).hom
  have hq : q.comap g = p := by
    simpa [p, q, g, V, Scheme.Hom.appLE] using congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hx)
  have hM : p.primeCompl.map g = q.primeCompl := by
    simpa only [hq] using
      Ideal.map_primeCompl_comap_of_surjective g (f.app_surjective U hU) q
  have he : (f.stalkMap x).hom =
      IsLocalization.map (X.presheaf.stalk x) g (hM.symm ▸ p.primeCompl.le_comap_map) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change (f.stalkMap x) (algebraMap Γ(Y,U) (Y.presheaf.stalk (f x)) a) =
      IsLocalization.map (X.presheaf.stalk x) g (hM.symm ▸ p.primeCompl.le_comap_map)
        (algebraMap Γ(Y,U) (Y.presheaf.stalk (f x)) a)
    rw [IsLocalization.map_eq]
    exact f.germ_stalkMap_apply U x hx a
  rw [he, IsLocalization.ker_map _ _ hM, Scheme.Hom.ker_apply]
  rfl

noncomputable def closedImmersion_stalkQuotient {X Y : Scheme} (f : X ⟶ Y)
    [IsClosedImmersion f] (x : X) {U : Y.Opens} (hU : IsAffineOpen U) (hx : f x ∈ U) :
    (Y.presheaf.stalk (f x) ⧸
      (f.ker.ideal ⟨U,hU⟩).map (Y.presheaf.germ U (f x) hx).hom) ≃+*
        X.presheaf.stalk x := by
  exact (Ideal.quotEquivOfEq (closedImmersion_stalk_ker f x hU hx).symm).trans
    ((f.stalkMap x).hom.quotientKerEquivOfSurjective (f.stalkMap_surjective x))
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma pointClosure_specializes {X : Scheme} (p : X) (z : pointClosure p) :
    p ⤳ pointClosureι p z := by
  apply specializes_iff_mem_closure.mpr
  rw [← pointClosure_range]
  exact ⟨z,rfl⟩

theorem pointClosure_stalk_ker {X : Scheme} (p : X) (z : pointClosure p) :
    RingHom.ker ((pointClosureι p).stalkMap z).hom =
      generizationPrime (pointClosure_specializes p z) := by
  let y := pointClosureι p z
  obtain ⟨U,hU,hy,_⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : X.Opens) from trivial)
  let h := pointClosure_specializes p z
  have hpU : p ∈ U := h.mem_open U.isOpen hy
  rw [closedImmersion_stalk_ker (pointClosureι p) z hU hy]
  have hideal : (pointClosureι p).ker = (X.fromSpecResidueField p).ker :=
    Scheme.IdealSheafData.ker_subschemeι _
  rw [hideal, pointClosure_affineIdeal p hU hpU,
    ← generizationPrime_affine h hU hy]
  let := X.presheaf.algebra_section_stalk ⟨y,hy⟩
  have := hU.isLocalization_stalk ⟨y,hy⟩
  exact IsLocalization.map_under (hU.primeIdealOf ⟨y,hy⟩).asIdeal.primeCompl
    (X.presheaf.stalk y) (generizationPrime h)

noncomputable def pointClosure_stalkEquiv {X : Scheme} (p : X) (z : pointClosure p) :
    (X.presheaf.stalk (pointClosureι p z) ⧸
      generizationPrime (pointClosure_specializes p z)) ≃+*
        (pointClosure p).presheaf.stalk z :=
  (Ideal.quotEquivOfEq (pointClosure_stalk_ker p z).symm).trans
    (((pointClosureι p).stalkMap z).hom.quotientKerEquivOfSurjective
      ((pointClosureι p).stalkMap_surjective z))
end NumericalDimensionOne

end OAI
