import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.CurveDegrees

namespace OAI

/-! Cartier Intersection. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
variable {C Y : Scheme} [IsIntegral C] [IsIntegral Y]
  [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [StalkwiseNormal Y]
  [CompactSpace C]
variable (sC : C ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 sC] [IsProper sC]

include sC in
lemma proper_principal_degree_zero (t : C.functionField) :
    complexWeilDegree (principalWeilDivisor t) = 0 := by
  let : AlgebraicGeometry.IsNoetherian C := ⟨⟩
  exact NumericalDimensionOneCurveAux.proper_curve_principal_degree_zero sC t
include sC in
lemma proper_representative_degree_eq {f : C ⟶ Y} {D : WeilDivisor Y}
    {E F : WeilDivisor C} (hE : IsPulledCartierRepresentative f D E)
    (hF : IsPulledCartierRepresentative f D F) :
    complexWeilDegree E = complexWeilDegree F := by
  classical
  obtain ⟨a, _, rfl⟩ := pulledCartierRepresentative_difference hE hF
  change (F + principalWeilDivisor a).sum (fun _ a => a) = _
  rw [Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)]
  change complexWeilDegree F + complexWeilDegree (principalWeilDivisor a) = _
  rw [proper_principal_degree_zero sC, add_zero]

noncomputable def properCurveDegree (f : C ⟶ Y)
    (D : cartierDivisors (X := Y)) : ℤ :=
  complexWeilDegree (Classical.choose
    (exists_pulledCartierRepresentative f D.1 D.2))

include sC in
lemma properCurveDegree_eq (f : C ⟶ Y) (D : cartierDivisors (X := Y))
    (E : WeilDivisor C) (hE : IsPulledCartierRepresentative f D E) :
    properCurveDegree f D = complexWeilDegree E := by
  exact proper_representative_degree_eq sC
    (Classical.choose_spec (exists_pulledCartierRepresentative f D.1 D.2)) hE
include sC in
lemma properCurveDegree_add (f : C ⟶ Y) (D E : cartierDivisors (X := Y)) :
    properCurveDegree f (D + E) = properCurveDegree f D + properCurveDegree f E := by
  classical
  let F := Classical.choose (exists_pulledCartierRepresentative f D.1 D.2)
  let G := Classical.choose (exists_pulledCartierRepresentative f E.1 E.2)
  have hF := Classical.choose_spec (exists_pulledCartierRepresentative f D.1 D.2)
  have hG := Classical.choose_spec (exists_pulledCartierRepresentative f E.1 E.2)
  rw [properCurveDegree_eq sC f (D + E) (F + G) (hF.add hG)]
  exact Finsupp.sum_add_index (fun _ _ => rfl) (fun _ _ _ _ => rfl)
include sC in
lemma properCurveDegree_zero (f : C ⟶ Y) : properCurveDegree f 0 = 0 := by
  rw [properCurveDegree_eq sC f 0 0 (isPulledCartierRepresentative_zero f)]
  rfl
noncomputable def properCurveDegreeHom (f : C ⟶ Y) : cartierDivisors (X := Y) →+ ℤ where
  toFun := properCurveDegree f
  map_zero' := properCurveDegree_zero sC f
  map_add' := properCurveDegree_add sC f

lemma properCurveDegree_eq_cartierCurveDegree {X : ComplexProjectiveVariety}
    [StalkwiseNormal X.scheme] (T : CurveOn X) (D : cartierDivisors (X := X.scheme)) :
    properCurveDegree T.morphism D = cartierCurveDegree D T := by
  rfl
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne

theorem ringKrullDim_le_of_quasiFinite (R S : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (f := PrimeSpectrum.comap (algebraMap R S))
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
  intro heq
  have hd := Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton
    (R := R) (S := S) (PrimeSpectrum.comap (algebraMap R S) p)
  have hsp : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).mp hpq.le
  have hp : p ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap R S) p} := rfl
  have hq : q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap R S) p} := heq.symm
  exact hpq.ne (hd.eq_of_specializes hsp hp hq)

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne

universe u

theorem coheight_le_of_smooth_dimension
    {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    Order.coheight x ≤ n := by
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  obtain ⟨g, _, hg⟩ := hs.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin n) k) Γ(X, U) := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, U) := hg
  have hdim : ringKrullDim Γ(X, U) ≤ n := by
    have h := ringKrullDim_le_of_quasiFinite (MvPolynomial (Fin n) k) Γ(X, U)
    simpa using h
  let y : U := ⟨x, hxU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := hU.isLocalization_stalk y
  have hstalk : ringKrullDim (X.presheaf.stalk x) ≤ n := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf y).asIdeal]
    exact (Ideal.height_le_ringKrullDim_of_ne_top
      (hU.primeIdealOf y).isPrime.ne_top).trans hdim
  rw [ringKrullDim_stalk_eq_coheight] at hstalk
  exact WithBot.coe_le_coe.mp hstalk

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

lemma finite_closed_of_closed_points {X : Scheme.{u}} [NoetherianSpace X]
    {Z : Set X} (hZ : IsClosed Z) (hpoint : ∀ x ∈ Z, IsClosed ({x} : Set X)) :
    Z.Finite := by
  obtain ⟨T, hT, hc, hi, heq⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [heq]
  apply hT.sUnion
  intro t ht
  obtain ⟨x, hx⟩ := QuasiSober.sober (hi t ht) (hc t ht)
  have hxZ : x ∈ Z := by
    rw [heq]
    exact Set.mem_sUnion.mpr ⟨t, ht, hx.mem⟩
  rw [← hx, (hpoint x hxZ).closure_eq]
  exact Set.finite_singleton _

lemma eq_of_specializes_of_equal_finite_coheight {X : Scheme.{u}}
    {x y : X} (hxy : x ⤳ y) {n : ℕ}
    (hx : Order.coheight x = n) (hy : Order.coheight y = n) : x = y := by
  by_contra hne
  have hlt : y < x := lt_iff_le_not_ge.mpr
    ⟨hxy, fun h => hne (Specializes.antisymm hxy (show y ⤳ x from h)).eq⟩
  have hbound := Order.coheight_add_one_le hlt
  rw [hx, hy] at hbound
  exact (not_le_of_gt ((ENat.lt_add_one_iff (ENat.natCast_ne_top n)).2 le_rfl)) hbound

lemma isClosed_point_of_max_coheight {X : Scheme.{u}} {n : ℕ}
    (hdim : ∀ y : X, Order.coheight y ≤ n) (x : X)
    (hx : Order.coheight x = n) : IsClosed ({x} : Set X) := by
  apply isClosed_of_closure_subset
  intro y hy
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hne' : x ≠ y := fun h => hne (by simpa only [Set.mem_singleton_iff] using h.symm)
  have hlt : y < x := lt_iff_le_not_ge.mpr
    ⟨hxy, fun h => hne' (Specializes.antisymm hxy (show y ⤳ x from h)).eq⟩
  have hb := (Order.coheight_add_one_le hlt).trans (hdim y)
  rw [hx] at hb
  exact (not_le_of_gt ((ENat.lt_add_one_iff (ENat.natCast_ne_top n)).2 le_rfl)) hb

lemma closed_point_of_distinct_prime_intersection {X : Scheme.{u}}
    (hdim : ∀ x : X, Order.coheight x ≤ 2)
    (p q : PrimeDivisor X) (hpq : p ≠ q) (x : X)
    (hp : x ∈ closure ({p.1} : Set X)) (hq : x ∈ closure ({q.1} : Set X)) :
    IsClosed ({x} : Set X) := by
  have hqx : q.1 ⤳ x := specializes_iff_mem_closure.mpr hq
  have hpx : p.1 ⤳ x := specializes_iff_mem_closure.mpr hp
  have hxp : x ≠ p.1 := by
    intro heq
    have hqp := eq_of_specializes_of_equal_finite_coheight (heq ▸ hqx) q.2 p.2
    exact hpq (Subtype.ext hqp.symm)
  have hlt : x < p.1 := lt_iff_le_not_ge.mpr
    ⟨hpx, fun h => hxp (Specializes.antisymm (show x ⤳ p.1 from h) hpx).eq⟩
  have hlow := Order.coheight_add_one_le hlt
  rw [p.2] at hlow
  have heq : Order.coheight x = 2 := le_antisymm (hdim x) (by simpa only [one_add_one_eq_two] using hlow)
  exact isClosed_point_of_max_coheight hdim x heq

theorem finite_divisorSupport_intersection {X : Scheme.{u}} [NoetherianSpace X]
    (hdim : ∀ x : X, Order.coheight x ≤ 2)
    (D E : WeilDivisor X) (hDE : Disjoint D.support E.support) :
    (divisorSupport D ∩ divisorSupport E).Finite := by
  apply finite_closed_of_closed_points
    ((isClosed_divisorSupport D).inter (isClosed_divisorSupport E))
  rintro x ⟨hxD, hxE⟩
  obtain ⟨p, hp, hpx⟩ := Set.mem_iUnion₂.mp hxD
  obtain ⟨q, hq, hqx⟩ := Set.mem_iUnion₂.mp hxE
  have hpq : p ≠ q := by
    intro heq
    exact (Finset.disjoint_left.mp hDE hp) (heq ▸ hq)
  exact closed_point_of_distinct_prime_intersection hdim p q hpq x hpx hqx

theorem finite_divisorSupport_intersection_smooth
    (T : ComplexProjectiveVariety) (hT : IsSmoothNfold T 2)
    (D E : WeilDivisor T.scheme) (hDE : Disjoint D.support E.support) :
    (divisorSupport D ∩ divisorSupport E).Finite := by
  let : SmoothOfRelativeDimension 2 T.structureMap := hT
  let : AlgebraicGeometry.IsNoetherian T.scheme := ⟨⟩
  exact finite_divisorSupport_intersection
    (coheight_le_of_smooth_dimension T.structureMap 2) D E hDE
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne

def IsGeneratedAt {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [CompactSpace X] (D : WeilDivisor X) (x : X) : Prop :=
  ∃ s : X.functionField, s ≠ 0 ∧ IsDivisorSection D s ∧
    x ∈ sectionNonvanishing D s

lemma coefficient_zero_on_divisorComplement {X : Scheme} (D : WeilDivisor X)
    (p : PrimeDivisor X) (hp : p.1 ∈ divisorComplement D) : D p = 0 := by
  classical
  by_contra h
  apply hp
  exact Set.mem_iUnion₂.mpr ⟨p, Finsupp.mem_support_iff.mpr h,
    subset_closure (Set.mem_singleton p.1)⟩

section LocalSections
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

lemma section_regular_stalk {D : WeilDivisor X} {s g : X.functionField}
    (hs : IsDivisorSection D s) {U : X.Opens} (hU : IsAffineOpen U)
    (hg : g ≠ 0) (hDg : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1)
    {x : X} (hx : x ∈ U) :
    ∃ a : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField a = s * g := by
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  have hsU : IsDivisorSectionOn D U s := hs.imp id (fun h p _ => h p)
  obtain ⟨a, ha⟩ := (cartier_local_section_iff hU hg hDg s).mp hsU
  exact ⟨X.presheaf.germ U x hx a, (X.algebraMap_germ_eq_germToFunctionField hx a).trans ha⟩

lemma section_unit_stalk [CompactSpace X] {D : WeilDivisor X} {s g : X.functionField}
    (hs : s ≠ 0) {U : X.Opens} (hg : g ≠ 0)
    (hDg : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1)
    {x : X} (hxU : x ∈ U) (hx : x ∈ sectionNonvanishing D s) :
    ∃ a : X.presheaf.stalk x, IsUnit a ∧
      algebraMap (X.presheaf.stalk x) X.functionField a = s * g := by
  let V : X.Opens := U ⊓ sectionNonvanishing D s
  have hzero : ∀ p : PrimeDivisor X, p.1 ∈ V → (0 : WeilDivisor X) p =
      X.ord (s * g) p.1 := by
    intro p hp
    rw [X.ord_mul hs hg, ← hDg p hp.1]
    exact (coefficient_zero_on_divisorComplement (principalWeilDivisor s + D) p hp.2).symm
  obtain ⟨a, ha, hea⟩ := local_equation_ratio_unit (mul_ne_zero hs hg) one_ne_zero
    hzero (fun p (_ : p.1 ∈ V) => by simp only [Finsupp.zero_apply, order_one])
    (show x ∈ V from ⟨hxU, hx⟩) (show x ∈ V from ⟨hxU, hx⟩)
  exact ⟨a, ha, by simpa only [div_one] using hea⟩

end LocalSections

lemma IsPulledCartierRepresentative.exists_nonzero_section
    {Y C : Scheme} [IsIntegral Y] [IsIntegral C]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian C]
    [StalkwiseNormal Y] [StalkwiseNormal C] [CompactSpace Y]
    {f : C ⟶ Y} {D : WeilDivisor Y} {E : WeilDivisor C}
    (hE : IsPulledCartierRepresentative f D E)
    (hgen : IsGeneratedAt D (f (genericPoint C))) :
    ∃ t : C.functionField, t ≠ 0 ∧ IsDivisorSection E t := by
  obtain ⟨s, hs, hsec, hnonvan⟩ := hgen
  obtain ⟨U, _, hηU, g, hg, hDg, hEloc⟩ := hE
  obtain ⟨a, ha, hea⟩ := section_unit_stalk hs hg hDg hηU hnonvan
  refine ⟨f.stalkMap (genericPoint C) a, (ha.map (f.stalkMap (genericPoint C)).hom).ne_zero,
    Or.inr ?_⟩
  intro p
  obtain ⟨V, hV, hpV, h, hh, hDh, b, hb, heb, hebord⟩ := hEloc p.1
  obtain ⟨c, hec⟩ := section_regular_stalk hsec hV hh hDh hpV
  let hsp : genericPoint C ⤳ p.1 := (genericPoint_spec C).specializes trivial
  have heq : a * b = Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hsp) c := by
    apply IsFractionRing.injective (Y.presheaf.stalk (f (genericPoint C))) Y.functionField
    rw [map_mul, hea, heb, algebraMap_stalkSpecializes, hec]
    field_simp
  rw [hebord p hpV, ← C.ord_mul
    (ha.map (f.stalkMap (genericPoint C)).hom).ne_zero
    (hb.map (f.stalkMap (genericPoint C)).hom).ne_zero, ← map_mul, heq,
    f.stalkSpecializes_stalkMap_apply (genericPoint C) p.1 hsp c]
  apply (ord_nonnegative_iff_regular p _ ?_).mpr ⟨f.stalkMap p.1 c, rfl⟩
  change C.presheaf.stalkSpecializes hsp (f.stalkMap p.1 c) ≠ 0
  rw [← f.stalkSpecializes_stalkMap_apply, ← heq, map_mul]
  exact mul_ne_zero (ha.map (f.stalkMap (genericPoint C)).hom).ne_zero
    (hb.map (f.stalkMap (genericPoint C)).hom).ne_zero

theorem cartierCurveDegree_nonneg_of_generatedAt
    {X : ComplexProjectiveVariety} [StalkwiseNormal X.scheme]
    (D : cartierDivisors (X := X.scheme)) (C : CurveOn X)
    (hgen : IsGeneratedAt D.1 (C.morphism (genericPoint C.curve.scheme))) :
    0 ≤ cartierCurveDegree D C := by
  obtain ⟨s, hs, hsec⟩ :=
    (pulledCartierRepresentative_spec C D.1 D.2).exists_nonzero_section hgen
  exact divisor_degree_nonnegative C.curve C.smooth _ s hs hsec

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne
section NonvanishingLocal
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
variable [StalkwiseNormal X] [CompactSpace X]

omit [StalkwiseNormal X] in

lemma section_nonvanishing_of_local_unit {D : WeilDivisor X} {s g : X.functionField}
    (hs : s ≠ 0) {U : X.Opens} (hg : g ≠ 0)
    (hDg : ∀ p : PrimeDivisor X, p.1 ∈ U → D p = X.ord g p.1)
    {x : X} (hx : x ∈ U) (a : X.presheaf.stalk x) (ha : IsUnit a)
    (hea : algebraMap (X.presheaf.stalk x) X.functionField a = s * g) :
    x ∈ sectionNonvanishing D s := by
  intro hmem
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hmem
  have hsp : p.1 ⤳ x := specializes_iff_mem_closure.mpr hxp
  have hpU : p.1 ∈ U := hsp.mem_open U.isOpen hx
  have hunit := ha.map (X.presheaf.stalkSpecializes hsp).hom
  have heq : algebraMap (X.presheaf.stalk p.1) X.functionField
      (X.presheaf.stalkSpecializes hsp a) = s * g := by
    rw [algebraMap_stalkSpecializes, hea]
  have hord := order_stalk_unit p hunit
  rw [heq, X.ord_mul hs hg, ← hDg p hpU] at hord
  exact (Finsupp.mem_support_iff.mp hp) hord
end NonvanishingLocal
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u

lemma stalkPrime_eq_comap_closedPoint {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (h : X.fromSpecStalk x p ⤳ x) :
    p = PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom
      (IsLocalRing.closedPoint (X.presheaf.stalk (X.fromSpecStalk x p))) := by
  apply (X.fromSpecStalk x).isEmbedding.injective
  have he := congrArg (fun f : Spec (X.presheaf.stalk (X.fromSpecStalk x p)) ⟶ X =>
    f (IsLocalRing.closedPoint (X.presheaf.stalk (X.fromSpecStalk x p))))
    (X.SpecMap_stalkSpecializes_fromSpecStalk h)
  rw [Scheme.fromSpecStalk_closedPoint] at he
  exact he.symm

section LocalIntersection
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [StalkwiseNormal X] [CompactSpace X]

lemma fromSpecStalk_mem_support_of_mem_prime
    (D : WeilDivisor X) (g : X.functionField) (hg : g ≠ 0)
    (U : X.Opens) (hDg : ∀ q : PrimeDivisor X, q.1 ∈ U → D q = X.ord g q.1)
    (x : X) (hx : x ∈ U) (a : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a = g)
    (p : PrimeSpectrum (X.presheaf.stalk x)) (hap : a ∈ p.asIdeal) :
    X.fromSpecStalk x p ∈ divisorSupport D := by
  have hsp : X.fromSpecStalk x p ⤳ x := X.range_fromSpecStalk.subset ⟨p, rfl⟩
  by_contra hy
  have hone : principalWeilDivisor (1 : X.functionField) = 0 := by
    ext q
    exact order_one q.1
  obtain ⟨v, hv, hev⟩ := section_unit_stalk (D := D) (s := 1) one_ne_zero hg hDg
    (hsp.mem_open U.isOpen hx) (by simpa only [sectionNonvanishing, hone, zero_add, divisorComplement,
      TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff] using hy)
  have hav : X.presheaf.stalkSpecializes hsp a = v := by
    apply IsFractionRing.injective (X.presheaf.stalk (X.fromSpecStalk x p)) X.functionField
    rw [algebraMap_stalkSpecializes, ha, hev, one_mul]
  have hap' : X.presheaf.stalkSpecializes hsp a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk x p)) := by
    rwa [stalkPrime_eq_comap_closedPoint x p hsp] at hap
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hap')) (hav ▸ hv)

theorem localIntersection_isFiniteLength
    (hdim : ∀ x : X, Order.coheight x ≤ 2)
    (D E : WeilDivisor X) (hDE : Disjoint D.support E.support)
    (g h : X.functionField) (hg : g ≠ 0) (hh : h ≠ 0)
    (U : X.Opens)
    (hDg : ∀ q : PrimeDivisor X, q.1 ∈ U → D q = X.ord g q.1)
    (hEh : ∀ q : PrimeDivisor X, q.1 ∈ U → E q = X.ord h q.1)
    (x : X) (hx : x ∈ U) (a b : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a = g)
    (hb : algebraMap (X.presheaf.stalk x) X.functionField b = h) :
    IsFiniteLength (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.span ({a, b} : Set (X.presheaf.stalk x))) := by
  let I : Ideal (X.presheaf.stalk x) := Ideal.span {a, b}
  have hpr : ∀ p : PrimeSpectrum (X.presheaf.stalk x), I ≤ p.asIdeal →
      p = IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    intro p hp
    have hap : a ∈ p.asIdeal := hp (Ideal.subset_span (by simp))
    have hbp : b ∈ p.asIdeal := hp (Ideal.subset_span (by simp))
    have hyD := fromSpecStalk_mem_support_of_mem_prime D g hg U hDg x hx a ha p hap
    have hyE := fromSpecStalk_mem_support_of_mem_prime E h hh U hEh x hx b hb p hbp
    obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp hyD
    obtain ⟨r, hr, hry⟩ := Set.mem_iUnion₂.mp hyE
    have hqr : q ≠ r := by
      intro he
      exact Finset.disjoint_left.mp hDE hq (he ▸ hr)
    have hycl := closed_point_of_distinct_prime_intersection hdim q r hqr _ hqy hry
    have hsp : X.fromSpecStalk x p ⤳ x := X.range_fromSpecStalk.subset ⟨p, rfl⟩
    have hexy : x = X.fromSpecStalk x p := by
      have hmem := specializes_iff_mem_closure.mp hsp
      simpa only [hycl.closure_eq, Set.mem_singleton_iff] using hmem
    apply (X.fromSpecStalk x).isEmbedding.injective
    simpa only [Scheme.fromSpecStalk_closedPoint] using hexy.symm
  have : IsArtinianRing ((X.presheaf.stalk x) ⧸ I) := by
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
    intro P hP
    let p : PrimeSpectrum (X.presheaf.stalk x) :=
      ⟨P.comap (Ideal.Quotient.mk I), hP.comap _⟩
    have hp : I ≤ p.asIdeal := by
      intro v hv
      change Ideal.Quotient.mk I v ∈ P
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hv]
      exact P.zero_mem
    have he := congrArg PrimeSpectrum.asIdeal (hpr p hp)
    have hm : (P.comap (Ideal.Quotient.mk I)).IsMaximal := by
      change p.asIdeal.IsMaximal
      rw [he]
      change (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).IsMaximal
      infer_instance
    have him := Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective hm
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at him
    exact him.resolve_left hP.ne_top
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_quotient I,
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))⟩
end LocalIntersection
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory
universe u
section CartierIntersection
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [StalkwiseNormal X]

structure CartierStalkEquation (D : WeilDivisor X) (x : X) where
  openSet : X.Opens
  mem_openSet : x ∈ openSet
  function : X.functionField
  nonzero : function ≠ 0
  equation : ∀ p : PrimeDivisor X, p.1 ∈ openSet → D p = X.ord function p.1
  regular : X.presheaf.stalk x
  regular_eq : algebraMap (X.presheaf.stalk x) X.functionField regular = function

lemma exists_cartierStalkEquation {D : WeilDivisor X} (hD : IsCartierDivisor D)
    (heff : ∀ p, 0 ≤ D p) (x : X) : Nonempty (CartierStalkEquation D x) := by
  obtain ⟨U, hU, hx, g, hg, heq⟩ := hD x
  have hsec : IsDivisorSection D (1 : X.functionField) :=
    Or.inr (fun p => by simpa only [order_one, zero_add] using heff p)
  obtain ⟨a, ha⟩ := section_regular_stalk hsec hU hg heq hx
  exact ⟨⟨U, hx, g, hg, heq, a, by simpa only [one_mul] using ha⟩⟩

lemma cartierStalkEquation_ideal_eq {D : WeilDivisor X} {x : X}
    (a b : CartierStalkEquation D x) :
    Ideal.span ({a.regular} : Set (X.presheaf.stalk x)) = Ideal.span {b.regular} := by
  obtain ⟨v, hv, hev⟩ := local_equation_ratio_unit a.nonzero b.nonzero
    a.equation b.equation a.mem_openSet b.mem_openSet
  have heq : a.regular = v * b.regular := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [a.regular_eq, map_mul, hev, b.regular_eq, div_mul_cancel₀ _ b.nonzero]
  rw [heq, Ideal.span_singleton_mul_left_unit hv]

noncomputable def effectiveCartierStalkIdeal {D : WeilDivisor X}
    (hD : IsCartierDivisor D) (heff : ∀ p, 0 ≤ D p) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  Ideal.span {(Classical.choice (exists_cartierStalkEquation hD heff x)).regular}

lemma effectiveCartierStalkIdeal_eq {D : WeilDivisor X}
    (hD : IsCartierDivisor D) (heff : ∀ p, 0 ≤ D p) {x : X}
    (a : CartierStalkEquation D x) :
    effectiveCartierStalkIdeal hD heff x = Ideal.span {a.regular} := by
  exact cartierStalkEquation_ideal_eq _ a

noncomputable def effectiveCartierMultiplicity {D E : WeilDivisor X}
    (hD : IsCartierDivisor D) (hE : IsCartierDivisor E)
    (hDeff : ∀ p, 0 ≤ D p) (hEeff : ∀ p, 0 ≤ E p) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    ((X.presheaf.stalk x) ⧸
      (effectiveCartierStalkIdeal hD hDeff x ⊔ effectiveCartierStalkIdeal hE hEeff x))

lemma effectiveCartierMultiplicity_comm {D E : WeilDivisor X}
    (hD : IsCartierDivisor D) (hE : IsCartierDivisor E)
    (hDeff : ∀ p, 0 ≤ D p) (hEeff : ∀ p, 0 ≤ E p) (x : X) :
    effectiveCartierMultiplicity hD hE hDeff hEeff x =
      effectiveCartierMultiplicity hE hD hEeff hDeff x := by
  exact (Submodule.quotEquivOfEq _ _ (sup_comm
    (effectiveCartierStalkIdeal hD hDeff x)
    (effectiveCartierStalkIdeal hE hEeff x))).length_eq

variable [CompactSpace X]

lemma effectiveCartierStalkIdeal_eq_top {D : WeilDivisor X}
    (hD : IsCartierDivisor D) (heff : ∀ p, 0 ≤ D p) {x : X}
    (hx : x ∉ divisorSupport D) : effectiveCartierStalkIdeal hD heff x = ⊤ := by
  let a := Classical.choice (exists_cartierStalkEquation hD heff x)
  have hone : principalWeilDivisor (1 : X.functionField) = 0 := by
    ext q
    exact order_one q.1
  obtain ⟨v, hv, hev⟩ := section_unit_stalk (D := D) (s := 1) one_ne_zero a.nonzero
    a.equation a.mem_openSet (by simpa only [sectionNonvanishing, hone, zero_add,
      divisorComplement, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff] using hx)
  have ha : a.regular = v := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    (a.regular_eq.trans (by simpa only [one_mul] using hev.symm))
  rw [effectiveCartierStalkIdeal_eq hD heff a, Ideal.span_singleton_eq_top]
  exact ha ▸ hv

lemma effectiveCartierMultiplicity_eq_zero {D E : WeilDivisor X}
    (hD : IsCartierDivisor D) (hE : IsCartierDivisor E)
    (hDeff : ∀ p, 0 ≤ D p) (hEeff : ∀ p, 0 ≤ E p) {x : X}
    (hx : x ∉ divisorSupport D ∩ divisorSupport E) :
    effectiveCartierMultiplicity hD hE hDeff hEeff x = 0 := by
  have htop : effectiveCartierStalkIdeal hD hDeff x ⊔
      effectiveCartierStalkIdeal hE hEeff x = ⊤ := by
    by_cases hxD : x ∈ divisorSupport D
    · rw [effectiveCartierStalkIdeal_eq_top hE hEeff (fun hxE => hx ⟨hxD, hxE⟩), sup_top_eq]
    · rw [effectiveCartierStalkIdeal_eq_top hD hDeff hxD, top_sup_eq]
  apply Module.length_eq_zero_iff.mpr
  exact Submodule.Quotient.subsingleton_iff.mpr htop

lemma effectiveCartierMultiplicity_ne_top
    (hdim : ∀ x : X, Order.coheight x ≤ 2)
    {D E : WeilDivisor X} (hD : IsCartierDivisor D) (hE : IsCartierDivisor E)
    (hDeff : ∀ p, 0 ≤ D p) (hEeff : ∀ p, 0 ≤ E p)
    (hDE : Disjoint D.support E.support) (x : X) :
    effectiveCartierMultiplicity hD hE hDeff hEeff x ≠ ⊤ := by
  let a := Classical.choice (exists_cartierStalkEquation hD hDeff x)
  let b := Classical.choice (exists_cartierStalkEquation hE hEeff x)
  rw [effectiveCartierMultiplicity, effectiveCartierStalkIdeal_eq hD hDeff a,
    effectiveCartierStalkIdeal_eq hE hEeff b, ← Ideal.span_insert,
    Module.length_ne_top_iff]
  exact localIntersection_isFiniteLength hdim D E hDE a.function b.function a.nonzero b.nonzero
    (a.openSet ⊓ b.openSet) (fun p hp => a.equation p hp.1) (fun p hp => b.equation p hp.2)
    x ⟨a.mem_openSet, b.mem_openSet⟩ a.regular b.regular a.regular_eq b.regular_eq

lemma effectiveCartierMultiplicity_finite_support
    (hdim : ∀ x : X, Order.coheight x ≤ 2)
    {D E : WeilDivisor X} (hD : IsCartierDivisor D) (hE : IsCartierDivisor E)
    (hDeff : ∀ p, 0 ≤ D p) (hEeff : ∀ p, 0 ≤ E p)
    (hDE : Disjoint D.support E.support) :
    (Function.support (effectiveCartierMultiplicity hD hE hDeff hEeff)).Finite := by
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  apply (finite_divisorSupport_intersection hdim D E hDE).subset
  intro x hx
  by_contra he
  exact hx (effectiveCartierMultiplicity_eq_zero hD hE hDeff hEeff he)
end CartierIntersection
end NumericalDimensionOne

end OAI
