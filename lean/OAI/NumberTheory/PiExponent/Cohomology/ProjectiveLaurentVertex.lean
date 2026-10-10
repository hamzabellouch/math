import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCech

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex

section

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech

variable {ι : Type*} [Fintype ι]

abbrev ChartExponent (i : ι) := {j : ι // j ≠ i} →₀ ℕ

def VertexMonomialSet (i : ι) (d : ℤ) : Set (Monomial ι d) :=
  {a | ∀ j, j ≠ i → 0 ≤ a.val j}

def encode (i : ι) (d : ℤ) (b : ChartExponent i) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) else (b ⟨j, h⟩ : ℤ)
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = (b j : ℤ) := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem encode_self (i : ι) (d : ℤ) (b : ChartExponent i) :
    (encode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by
  classical
  simp [encode]

@[simp] theorem encode_other (i : ι) (d : ℤ) (b : ChartExponent i)
    (j : {j : ι // j ≠ i}) : (encode i d b).val j = (b j : ℤ) := by
  classical
  simp [encode, j.property]

theorem encode_regular (i : ι) (d : ℤ) (b : ChartExponent i) :
    encode i d b ∈ VertexMonomialSet i d := by
  intro j hj
  simpa only [encode_other i d b ⟨j, hj⟩] using Int.natCast_nonneg (b ⟨j, hj⟩)

def decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) : ChartExponent i :=
  Finsupp.equivFunOnFinite.symm (fun j => (a.val.val j).toNat)

@[simp] theorem decode_apply (i : ι) (d : ℤ) (a : VertexMonomialSet i d)
    (j : {j : ι // j ≠ i}) : decode i d a j = (a.val.val j).toNat := rfl

@[simp] theorem decode_encode (i : ι) (d : ℤ) (b : ChartExponent i) :
    decode i d ⟨encode i d b, encode_regular i d b⟩ = b := by
  ext j
  simp

@[simp] theorem encode_decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) :
    encode i d (decode i d a) = a.val := by
  classical
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    rw [encode_self]
    have h := a.val.property
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
    have hs : (∑ k : {j : ι // j ≠ i}, ((decode i d a k : ℕ) : ℤ)) =
        ∑ k : {j : ι // j ≠ i}, a.val.val k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Int.toNat_of_nonneg (a.property k k.property)
    rw [hs]
    omega
  · change (encode i d (decode i d a)).val (⟨j, hj⟩ : {j : ι // j ≠ i}) = _
    rw [encode_other, decode_apply, Int.toNat_of_nonneg (a.property j hj)]

def exponentEquiv (i : ι) (d : ℤ) : ChartExponent i ≃ VertexMonomialSet i d where
  toFun b := ⟨encode i d b, encode_regular i d b⟩
  invFun := decode i d
  left_inv := decode_encode i d
  right_inv a := Subtype.ext (encode_decode i d a)

variable {R : Type*} [CommRing R]

def vertexPolynomialEquiv (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R ≃ₗ[R]
      Finsupp.supported R R (VertexMonomialSet i d) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans <|
    (Finsupp.domLCongr (exponentEquiv i d)).trans
      (Finsupp.supportedEquivFinsupp (VertexMonomialSet i d)).symm

def vertexLaurent (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R →ₗ[R] Laurent ι R d :=
  (Finsupp.supported R R (VertexMonomialSet i d)).subtype.comp
    (vertexPolynomialEquiv i d).toLinearMap

@[simp] theorem vertexLaurent_monomial (i : ι) (d : ℤ) (b : ChartExponent i) (r : R) :
    vertexLaurent i d (MvPolynomial.monomial b r) = Finsupp.single (encode i d b) r := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, MvPolynomial.monomial, exponentEquiv]

@[simp] theorem vertexLaurent_coefficient (i : ι) (d : ℤ) (b : ChartExponent i)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    vertexLaurent i d p (encode i d b) = p.coeff b := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, Finsupp.extendDomain_apply,
    encode_regular, exponentEquiv]

theorem mem_supported_iff_regular (i : ι) (d : ℤ) (p : Laurent ι R d) :
    p ∈ Finsupp.supported R R (VertexMonomialSet i d) ↔ RegularOn {i} p := by
  classical
  rw [Finsupp.mem_supported]
  constructor
  · intro hp a ha j hj
    have h := hp (Finsupp.mem_support_iff.mpr ha)
    by_contra hji
    exact not_lt_of_ge (h j hji) hj
  · intro hp a ha j hj
    by_contra hneg
    exact hj (hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hneg))

theorem vertexLaurent_regular (i : ι) (d : ℤ)
    (p : MvPolynomial {j : ι // j ≠ i} R) : RegularOn {i} (vertexLaurent i d p) :=
  (mem_supported_iff_regular i d _).mp (vertexPolynomialEquiv i d p).property

theorem vertexLaurent_injective (i : ι) (d : ℤ) :
    Function.Injective (vertexLaurent (R := R) i d) :=
  Subtype.val_injective.comp (vertexPolynomialEquiv i d).injective

theorem vertexLaurent_surjective_regular (i : ι) (d : ℤ) (p : Laurent ι R d)
    (hp : RegularOn {i} p) :
    ∃ b : MvPolynomial {j : ι // j ≠ i} R, vertexLaurent i d b = p := by
  let a : Finsupp.supported R R (VertexMonomialSet i d) :=
    ⟨p, (mem_supported_iff_regular i d p).mpr hp⟩
  refine ⟨(vertexPolynomialEquiv i d).symm a, ?_⟩
  change ((vertexPolynomialEquiv i d) ((vertexPolynomialEquiv i d).symm a)).val = p
  rw [LinearEquiv.apply_symm_apply]

end

section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

def fullEncode (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, b k else b ⟨j, h⟩
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, b k := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = b j := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem fullEncode_self (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) :
    (fullEncode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, b k := by
  classical
  simp [fullEncode]

@[simp] theorem fullEncode_other (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ)
    (j : {j : ι // j ≠ i}) : (fullEncode i d b).val j = b j := by
  classical
  simp [fullEncode, j.property]

def fullExponentEquiv (i : ι) (d : ℤ) : ({j : ι // j ≠ i} → ℤ) ≃ Monomial ι d where
  toFun := fullEncode i d
  invFun a j := a.val j
  left_inv b := by funext j; simp
  right_inv a := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      rw [fullEncode_self]
      have h := a.property
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
      change d - (∑ k : {j : ι // j ≠ i}, a.val k) = a.val i
      omega
    · exact fullEncode_other i d _ ⟨j, hj⟩

abbrev chartGroupAlgebra (i : ι) := AddMonoidAlgebra R ({j : ι // j ≠ i} → ℤ)

def natExponentHom (i : ι) : ChartExponent i →+ ({j : ι // j ≠ i} → ℤ) where
  toFun b j := b j
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

def polynomialToGroupAlgebra (i : ι) :
    MvPolynomial {j : ι // j ≠ i} R →+* chartGroupAlgebra (R := R) i :=
  AddMonoidAlgebra.mapDomainRingHom R (natExponentHom i)

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_injective (i : ι) :
    Function.Injective (polynomialToGroupAlgebra (R := R) i) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

def groupAlgebraToLaurent (i : ι) (d : ℤ) : chartGroupAlgebra (R := R) i ≃+ Laurent ι R d :=
  (AddMonoidAlgebra.coeffAddEquiv).trans (Finsupp.domCongr (fullExponentEquiv i d))

def chartProduct (i : ι) (s : Finset {j : ι // j ≠ i}) : MvPolynomial {j : ι // j ≠ i} R :=
  ∏ j ∈ s, MvPolynomial.X j

omit [Fintype ι] in
theorem groupAlgebra_single_isUnit (i : ι) (a : {j : ι // j ≠ i} → ℤ) :
    IsUnit (AddMonoidAlgebra.single a (1 : R) : chartGroupAlgebra (R := R) i) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-a) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [add_neg_cancel, one_mul]
  rfl

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_X (i : ι) (j : {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (MvPolynomial.X j) =
      AddMonoidAlgebra.single (natExponentHom i (Finsupp.single j 1)) 1 := by
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ _) = _
  exact AddMonoidAlgebra.mapDomain_single

omit [Fintype ι] in
theorem groupAlgebra_product_isUnit (i : ι) (s : Finset {j : ι // j ≠ i}) :
    IsUnit (polynomialToGroupAlgebra (R := R) i (chartProduct i s)) := by
  rw [chartProduct, map_prod]
  exact IsUnit.prod_iff.mpr fun j _ => by
    rw [polynomialToGroupAlgebra_X]
    exact groupAlgebra_single_isUnit i _

def overlapToGroupAlgebra (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+* chartGroupAlgebra (R := R) i :=
  Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (groupAlgebra_product_isUnit i s)

omit [Fintype ι] in
@[simp] theorem overlapToGroupAlgebra_base (i : ι) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapToGroupAlgebra i s (algebraMap _ _ p) = polynomialToGroupAlgebra i p := by
  exact IsLocalization.Away.lift_eq (chartProduct i s) (groupAlgebra_product_isUnit i s) p

omit [Fintype ι] in
theorem overlapToGroupAlgebra_injective (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapToGroupAlgebra (R := R) i s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (chartProduct (R := R) i s)) (overlapToGroupAlgebra i s)).mpr
  intro x y
  constructor
  · exact congrArg _
  · intro h
    rw [overlapToGroupAlgebra_base, overlapToGroupAlgebra_base] at h
    exact congrArg _ (polynomialToGroupAlgebra_injective i h)

def overlapLaurent (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+ Laurent ι R d :=
  (groupAlgebraToLaurent i d).toAddMonoidHom.comp (overlapToGroupAlgebra i s).toAddMonoidHom

theorem overlapLaurent_injective (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapLaurent (R := R) i d s) :=
  (groupAlgebraToLaurent i d).injective.comp (overlapToGroupAlgebra_injective i s)

def productExponent (i : ι) (s : Finset {j : ι // j ≠ i}) : {j : ι // j ≠ i} → ℤ :=
  ∑ j ∈ s, natExponentHom i (Finsupp.single j 1)

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_product (i : ι)
    (s : Finset {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (chartProduct i s) =
      AddMonoidAlgebra.single (productExponent i s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [chartProduct, productExponent, Finset.prod_empty, Finset.sum_empty, map_one]
      rfl
  | @insert j s hj ih =>
      simp only [chartProduct, Finset.prod_insert hj, map_mul] at *
      rw [polynomialToGroupAlgebra_X, ih, AddMonoidAlgebra.single_mul_single]
      simp [productExponent, hj]

omit [Fintype ι] in
@[simp] theorem productExponent_outside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : productExponent i s k = 0 := by
  classical
  simp only [productExponent, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : j ≠ k := fun h => hk (h ▸ hj)
  simp [natExponentHom, Ne.symm hne]

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_nonnegative (i : ι)
    (p : MvPolynomial {j : ι // j ≠ i} R) (a : {j : ι // j ≠ i} → ℤ)
    (ha : (polynomialToGroupAlgebra i p).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) : 0 ≤ a k := by
  obtain ⟨b, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ha
  exact Int.natCast_nonneg _

omit [Fintype ι] in
theorem overlapToGroupAlgebra_nonnegative (i : ι) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s))
    (a : {j : ι // j ≠ i} → ℤ) (ha : (overlapToGroupAlgebra i s z).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : 0 ≤ a k := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (chartProduct (R := R) i s) z
  have h := congrArg (overlapToGroupAlgebra i s) hp
  simp only [map_mul, map_pow, overlapToGroupAlgebra_base,
    polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_pow, one_pow] at h
  have hc := congrArg (fun q : chartGroupAlgebra (R := R) i =>
    q.coeff (a + n • productExponent i s)) h
  simp only [AddMonoidAlgebra.coeff_mul_single_add, mul_one] at hc
  have hn := polynomialToGroupAlgebra_nonnegative i p (a + n • productExponent i s)
    (hc ▸ ha) k
  simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
    smul_zero, add_zero] using hn

@[simp] theorem groupAlgebraToLaurent_coefficient (i : ι) (d : ℤ)
    (p : chartGroupAlgebra (R := R) i) (a : Monomial ι d) :
    groupAlgebraToLaurent i d p a = p.coeff (fun j => a.val j) := by
  simp [groupAlgebraToLaurent, fullExponentEquiv]
  rfl

theorem overlapLaurent_regular (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s)) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (overlapLaurent i d s z) := by
  intro a ha k hk
  by_cases hki : k = i
  · exact Or.inl hki
  · apply Or.inr
    by_contra hks
    have hn : (⟨k, hki⟩ : {j : ι // j ≠ i}) ∉ s := by
      intro hm
      exact hks ⟨⟨k, hki⟩, hm, rfl⟩
    change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) a ≠ 0 at ha
    rw [groupAlgebraToLaurent_coefficient] at ha
    exact not_lt_of_ge (overlapToGroupAlgebra_nonnegative i s z _ ha ⟨k, hki⟩ hn) hk

@[simp] theorem fullEncode_nat (i : ι) (d : ℤ) (b : ChartExponent i) :
    fullEncode i d (natExponentHom i b) = encode i d b := rfl

theorem groupAlgebraToLaurent_polynomial (i : ι) (d : ℤ)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    groupAlgebraToLaurent i d (polynomialToGroupAlgebra i p) = vertexLaurent i d p := by
  induction p using MvPolynomial.induction_on'
  case add a b ha hb =>
    simp only [map_add, ha, hb]
  case monomial b r =>
    rw [vertexLaurent_monomial]
    change groupAlgebraToLaurent i d
      (AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r)) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    simp [groupAlgebraToLaurent, fullExponentEquiv]
    rfl

@[simp] theorem overlapLaurent_base (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapLaurent i d s (algebraMap _ _ p) = vertexLaurent i d p := by
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s (algebraMap _ _ p)) = _
  rw [overlapToGroupAlgebra_base, groupAlgebraToLaurent_polynomial]

end

section
variable {ι R : Type*} [Fintype ι] [CommRing R]
theorem overlapLaurent_natural (i : ι) (d : ℤ)
    (s t : Finset {j : ι // j ≠ i})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) i t))
    (hf : ∀ p : MvPolynomial {j : ι // j ≠ i} R,
      f (algebraMap _ _ p) = algebraMap _ _ p)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent i d t (f z) = overlapLaurent i d s z := by
  have h : (overlapToGroupAlgebra i t).comp f = overlapToGroupAlgebra i s := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartProduct (R := R) i s))
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, hf, overlapToGroupAlgebra_base]
  change groupAlgebraToLaurent i d (((overlapToGroupAlgebra i t).comp f) z) = _
  rw [h]
  rfl
end

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
@[simp] theorem productExponent_inside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∈ s) : productExponent i s k = 1 := by
  classical
  simp [productExponent, Finset.sum_apply, natExponentHom, Finsupp.single_apply, hk]

theorem exists_cleared_exponent (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ (n : ℕ) (b : ChartExponent i), natExponentHom i b = a + n • productExponent i s := by
  classical
  let n : ℕ := ∑ j : {j : ι // j ≠ i}, (-a j).toNat
  have hnn : ∀ k, 0 ≤ a k + (n : ℤ) := by
    intro k
    have hn : (-a k).toNat ≤ n :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((-a j).toNat)) (Finset.mem_univ k)
    have hn' : ((-a k).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have hnonneg : ∀ k, 0 ≤ (a + n • productExponent i s) k := by
    intro k
    by_cases hk : k ∈ s
    · simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, productExponent_inside i s k hk] using hnn k
    · simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
        smul_zero, add_zero] using ha k hk
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun k => ((a + n • productExponent i s) k).toNat), ?_⟩
  funext k
  exact Int.toNat_of_nonneg (hnonneg k)

theorem groupAlgebra_single_in_overlap_range (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (r : R) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapToGroupAlgebra i s z = AddMonoidAlgebra.single a r := by
  classical
  obtain ⟨n, b, hb⟩ := exists_cleared_exponent i s a ha
  have hinv : polynomialToGroupAlgebra (R := R) i (chartProduct i s) *
      AddMonoidAlgebra.single (-productExponent i s) 1 = 1 := by
    rw [polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, one_mul]
    rfl
  refine ⟨Localization.mk (MvPolynomial.monomial b r) ⟨(chartProduct i s)^n, n, rfl⟩, ?_⟩
  change Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (isUnit_iff_exists_inv.mpr ⟨_, hinv⟩) _ = _
  rw [Localization.awayLift_mk (polynomialToGroupAlgebra i) (chartProduct i s)
    (MvPolynomial.monomial b r) (AddMonoidAlgebra.single (-productExponent i s) 1) hinv n]
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r) * _ = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single, hb]
  simp

theorem laurent_single_in_overlap_range (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (a : Monomial ι d) (r : R)
    (ha : ∀ k : {j : ι // j ≠ i}, k ∉ s → 0 ≤ a.val k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a r := by
  obtain ⟨z, hz⟩ := groupAlgebra_single_in_overlap_range i s (fun j => a.val j) r ha
  refine ⟨z, ?_⟩
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) = _
  rw [hz]
  change (Finsupp.domCongr (fullExponentEquiv i d))
    (Finsupp.single ((fullExponentEquiv i d).symm a) r) = _
  simp

theorem overlapLaurent_surjective_regular (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ z : Localization.Away (chartProduct (R := R) i s), overlapLaurent i d s z = p := by
  classical
  have hs : ∀ a ∈ p.support, ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a (p a) := by
    intro a ha
    apply laurent_single_in_overlap_range
    intro k hk
    by_contra hn
    have hmem := hp a (Finsupp.mem_support_iff.mp ha) k (lt_of_not_ge hn)
    rcases hmem with hmem | ⟨j, hj, heq⟩
    · exact k.property hmem
    · exact hk ((Subtype.ext heq) ▸ hj)
  choose z hz using hs
  refine ⟨∑ a ∈ p.support, if h : a ∈ p.support then z a h else 0, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ p.support, Finsupp.single a (p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [dite_eq_left ha, hz]
    _ = p := p.sum_single
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

end

end OAI
