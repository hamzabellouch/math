import OAI.NumberTheory.PiExponent.Cohomology.GradedCech
import OAI.NumberTheory.PiExponent.Cohomology.GradedH0

namespace OAI

namespace PiExponent.GradedPolynomialLaurent
noncomputable section
open scoped BigOperators
open PiExponent.GradedCech PiExponent.GradedLocalizationExact PiExponent.ProjectiveMonomialCech
attribute [local instance] Classical.propDecidable MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [CommRing R]

abbrev GroupAlgebra := AddMonoidAlgebra R (J → ℤ)

def natExponentHom : (J →₀ ℕ) →+ (J → ℤ) where
  toFun b j := b j
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

def polynomialToGroupAlgebra : MvPolynomial J R →+* GroupAlgebra (J := J) (R := R) :=
  AddMonoidAlgebra.mapDomainRingHom R natExponentHom

theorem polynomialToGroupAlgebra_injective :
    Function.Injective (polynomialToGroupAlgebra (J := J) (R := R)) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

def product (s : Finset J) : MvPolynomial J R := ∏ j ∈ s, MvPolynomial.X j

def productExponent (s : Finset J) : J → ℤ := ∑ j ∈ s, natExponentHom (Finsupp.single j 1)

theorem single_isUnit (a : J → ℤ) :
    IsUnit (AddMonoidAlgebra.single a (1 : R) : GroupAlgebra (J := J) (R := R)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-a) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [add_neg_cancel, one_mul]
  rfl

@[simp] theorem polynomialToGroupAlgebra_X (j : J) :
    polynomialToGroupAlgebra (R := R) (MvPolynomial.X j) =
      AddMonoidAlgebra.single (natExponentHom (Finsupp.single j 1)) 1 := by
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ _) = _
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem polynomialToGroupAlgebra_product (s : Finset J) :
    polynomialToGroupAlgebra (R := R) (product s) =
      AddMonoidAlgebra.single (productExponent s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [product, productExponent, Finset.prod_empty, Finset.sum_empty, map_one]
      rfl
  | @insert j s hj ih =>
      simp only [product, Finset.prod_insert hj, map_mul] at *
      rw [polynomialToGroupAlgebra_X, ih, AddMonoidAlgebra.single_mul_single]
      simp [productExponent, hj]

theorem product_isUnit (s : Finset J) :
    IsUnit (polynomialToGroupAlgebra (R := R) (product s)) := by
  rw [polynomialToGroupAlgebra_product]
  exact single_isUnit _

def ringLocalizationMap (s : Finset J) :
    Localization.Away (product (R := R) s) →+* GroupAlgebra (J := J) (R := R) :=
  Localization.awayLift polynomialToGroupAlgebra (product s) (product_isUnit s)

@[simp] theorem ringLocalizationMap_base (s : Finset J) (p : MvPolynomial J R) :
    ringLocalizationMap s (algebraMap _ _ p) = polynomialToGroupAlgebra p :=
  IsLocalization.Away.lift_eq (product s) (product_isUnit s) p

theorem ringLocalizationMap_injective (s : Finset J) :
    Function.Injective (ringLocalizationMap (R := R) s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (product (R := R) s)) (ringLocalizationMap s)).mpr
  intro p q
  constructor
  · exact congrArg _
  · intro h
    rw [ringLocalizationMap_base, ringLocalizationMap_base] at h
    exact congrArg _ (polynomialToGroupAlgebra_injective h)

def moduleRingEquiv (s : Finset J) :
    LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R) ≃ₗ[MvPolynomial J R]
      Localization.Away (product (R := R) s) :=
  IsLocalizedModule.iso _ (Algebra.linearMap _ _)

@[simp] theorem moduleRingEquiv_fraction (s : Finset J) (p : MvPolynomial J R) (n : ℕ) :
    moduleRingEquiv s (fraction (product s) p n) = Localization.mk p (powerDenominator (product s) n) := by
  change IsLocalizedModule.mk' (Algebra.linearMap (MvPolynomial J R)
    (Localization.Away (product (R := R) s))) p (powerDenominator (product s) n) = _
  rw [← IsLocalization.mk'_eq_mk', Localization.mk_eq_mk']

def moduleToGroupAlgebra (s : Finset J) :
    LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R) →+
      GroupAlgebra (J := J) (R := R) :=
  (ringLocalizationMap s).toAddMonoidHom.comp (moduleRingEquiv s).toAddMonoidHom

theorem moduleToGroupAlgebra_injective (s : Finset J) :
    Function.Injective (moduleToGroupAlgebra (R := R) s) :=
  (ringLocalizationMap_injective s).comp (moduleRingEquiv s).injective

@[simp] theorem moduleToGroupAlgebra_fraction (s : Finset J) (p : MvPolynomial J R) (n : ℕ) :
    moduleToGroupAlgebra s (fraction (product s) p n) =
      polynomialToGroupAlgebra p * AddMonoidAlgebra.single (-(n • productExponent s)) 1 := by
  have hinv : polynomialToGroupAlgebra (R := R) (product s) *
      AddMonoidAlgebra.single (-productExponent s) 1 = 1 := by
    rw [polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, one_mul]
    rfl
  change ringLocalizationMap s (moduleRingEquiv s (fraction _ p n)) = _
  rw [moduleRingEquiv_fraction]
  change Localization.awayLift polynomialToGroupAlgebra (product s)
    (isUnit_iff_exists_inv.mpr ⟨_, hinv⟩) _ = _
  unfold powerDenominator
  rw [Localization.awayLift_mk polynomialToGroupAlgebra (product s) p
    (AddMonoidAlgebra.single (-productExponent s) 1) hinv n]
  simp only [AddMonoidAlgebra.single_pow, one_pow, smul_neg]

@[simp] theorem productExponent_apply (s : Finset J) (j : J) :
    productExponent s j = if j ∈ s then 1 else 0 := by
  classical
  simp [productExponent, Finset.sum_apply, natExponentHom, Finsupp.single_apply]

variable [Fintype J]

@[simp] theorem sum_productExponent (s : Finset J) : ∑ j, productExponent s j = (s.card : ℤ) := by
  classical
  simp [productExponent_apply]

omit [Fintype J] in
theorem natExponentHom_injective : Function.Injective (natExponentHom (J := J)) := by
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

omit [Fintype J] in
@[simp] theorem polynomialToGroupAlgebra_coefficient (p : MvPolynomial J R) (b : J →₀ ℕ) :
    (polynomialToGroupAlgebra p).coeff (natExponentHom b) = p.coeff b :=
  Finsupp.mapDomain_apply_of_injective natExponentHom_injective p.coeff b

theorem polynomialToGroupAlgebra_support {d : ℤ} (p : MvPolynomial J R)
    (hp : p.IsWeightedHomogeneous (1 : J → ℤ) d) (a : J → ℤ)
    (ha : (polynomialToGroupAlgebra p).coeff a ≠ 0) :
    (∑ j, a j = d) ∧ ∀ j, 0 ≤ a j := by
  obtain ⟨b, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ha
  rw [polynomialToGroupAlgebra_coefficient] at ha
  constructor
  · simpa only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one,
      natExponentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hp ha
  · intro j
    exact Int.natCast_nonneg _

omit [Fintype J] in
@[simp] theorem moduleToGroupAlgebra_fraction_coefficient
    (s : Finset J) (p : MvPolynomial J R) (n : ℕ) (a : J → ℤ) :
    (moduleToGroupAlgebra s (fraction (product s) p n)).coeff a =
      (polynomialToGroupAlgebra p).coeff (a + n • productExponent s) := by
  rw [moduleToGroupAlgebra_fraction]
  simp only [AddMonoidAlgebra.coeff_mul_single_apply, neg_neg, mul_one]

abbrev grading : ℤ → Submodule R (MvPolynomial J R) :=
  MvPolynomial.weightedHomogeneousSubmodule R (1 : J → ℤ)

omit [Fintype J] in
theorem variable_mem (j : J) : MvPolynomial.X j ∈ grading (R := R) (J := J) 1 :=
  MvPolynomial.isWeightedHomogeneous_X R (1 : J → ℤ) j

omit [Fintype J] in
theorem product_mem (s : Finset J) : product (R := R) s ∈ grading (R := R) (s.card : ℤ) := by
  classical
  exact coverProduct_mem grading MvPolynomial.X variable_mem s

abbrev Piece (s : Finset J) (d : ℤ) :=
  degreePiece (grading (J := J) (R := R)) (grading (J := J) (R := R)) (product (R := R) s) (s.card : ℤ) (product_mem (R := R) s) d

theorem piece_support (s : Finset J) (d : ℤ) (z : Piece (R := R) s d)
    (a : J → ℤ) (ha : (moduleToGroupAlgebra s z.val).coeff a ≠ 0) :
    (∑ j, a j = d) ∧ ∀ j, j ∉ s → 0 ≤ a j := by
  obtain ⟨n, p, hp, hz⟩ := z.property
  rw [hz, moduleToGroupAlgebra_fraction_coefficient] at ha
  obtain ⟨hd, hn⟩ := polynomialToGroupAlgebra_support p hp _ ha
  constructor
  · simp only [Pi.add_apply, Finset.sum_add_distrib,
      sum_productExponent, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ← Finset.mul_sum] at hd
    omega
  · intro j hj
    simpa only [Pi.add_apply, Pi.smul_apply, productExponent_apply, ite_eq_right hj,
      smul_zero, add_zero] using hn j

def pieceToLaurent (s : Finset J) (d : ℤ) : Piece (R := R) s d →+ Laurent J R d :=
  (Finsupp.subtypeDomainAddMonoidHom (p := fun a : J → ℤ => ∑ j, a j = d)).comp
    ((AddMonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp
      ((moduleToGroupAlgebra s).comp (degreePiece grading grading (product s)
        s.card (product_mem s) d).subtype))

@[simp] theorem pieceToLaurent_coefficient (s : Finset J) (d : ℤ)
    (z : Piece (R := R) s d) (a : Monomial J d) :
    pieceToLaurent s d z a = (moduleToGroupAlgebra s z.val).coeff a.val := rfl

theorem pieceToLaurent_regular (s : Finset J) (d : ℤ) (z : Piece (R := R) s d) :
    RegularOn (s : Set J) (pieceToLaurent s d z) := by
  intro a ha j hj
  by_contra hjs
  exact (not_lt_of_ge ((piece_support s d z a.val ha).2 j hjs)) hj

theorem pieceToLaurent_injective (s : Finset J) (d : ℤ) :
    Function.Injective (pieceToLaurent (R := R) s d) := by
  intro z w h
  apply Subtype.ext
  apply moduleToGroupAlgebra_injective s
  ext a
  by_cases ha : ∑ j, a j = d
  · exact congrArg (fun l : Laurent J R d => l ⟨a, ha⟩) h
  · have hz : (moduleToGroupAlgebra s z.val).coeff a = 0 := by
      by_contra hz
      exact ha (piece_support s d z a hz).1
    have hw : (moduleToGroupAlgebra s w.val).coeff a = 0 := by
      by_contra hw
      exact ha (piece_support s d w a hw).1
    rw [hz, hw]

theorem exists_cleared_exponent (s : Finset J) (a : J → ℤ)
    (ha : ∀ j, j ∉ s → 0 ≤ a j) :
    ∃ (n : ℕ) (b : J →₀ ℕ), natExponentHom b = a + n • productExponent s := by
  classical
  let n : ℕ := ∑ j, (-a j).toNat
  have hnn : ∀ j, 0 ≤ a j + (n : ℤ) := by
    intro j
    have hn : (-a j).toNat ≤ n :=
      Finset.single_le_sum (fun k _ => Nat.zero_le ((-a k).toNat)) (Finset.mem_univ j)
    have hn' : ((-a j).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have hnonneg : ∀ j, 0 ≤ (a + n • productExponent s) j := by
    intro j
    by_cases hj : j ∈ s
    · simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, productExponent_apply, hj] using hnn j
    · simpa only [Pi.add_apply, Pi.smul_apply, productExponent_apply, ite_eq_right hj,
        smul_zero, add_zero] using ha j hj
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun j => ((a + n • productExponent s) j).toNat), ?_⟩
  funext j
  exact Int.toNat_of_nonneg (hnonneg j)

theorem single_in_piece_range (s : Finset J) (d : ℤ) (a : Monomial J d) (r : R)
    (ha : ∀ j, j ∉ s → 0 ≤ a.val j) :
    ∃ z : Piece (R := R) s d, pieceToLaurent s d z = Finsupp.single a r := by
  classical
  obtain ⟨n, b, hb⟩ := exists_cleared_exponent s a.val ha
  have hdeg : Finsupp.weight (1 : J → ℤ) b = d + (n : ℤ) * (s.card : ℤ) := by
    simp only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one]
    change (∑ j, natExponentHom b j) = _
    rw [hb]
    simp only [Pi.add_apply, Finset.sum_add_distrib,
      sum_productExponent, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ← Finset.mul_sum, a.property]
  let z : Piece (R := R) s d := ⟨fraction (product s) (MvPolynomial.monomial b r) n,
    n, MvPolynomial.monomial b r, MvPolynomial.isWeightedHomogeneous_monomial _ b r hdeg, rfl⟩
  have hz : moduleToGroupAlgebra s z.val = AddMonoidAlgebra.single a.val r := by
    change moduleToGroupAlgebra s (fraction (product s) (MvPolynomial.monomial b r) n) = _
    rw [moduleToGroupAlgebra_fraction]
    change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r) * _ = _
    rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, hb]
    simp
  refine ⟨z, ?_⟩
  ext a'
  rw [pieceToLaurent_coefficient, hz]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  congr 1
  exact propext Subtype.val_inj

theorem pieceToLaurent_surjective_regular (s : Finset J) (d : ℤ) (p : Laurent J R d)
    (hp : RegularOn (s : Set J) p) :
    ∃ z : Piece (R := R) s d, pieceToLaurent s d z = p := by
  classical
  have hs : ∀ a ∈ p.support, ∃ z : Piece (R := R) s d,
      pieceToLaurent s d z = Finsupp.single a (p a) := by
    intro a ha
    apply single_in_piece_range
    intro j hj
    by_contra hn
    exact hj (hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hn))
  choose z hz using hs
  refine ⟨∑ a ∈ p.support, if h : a ∈ p.support then z a h else 0, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ p.support, Finsupp.single a (p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [dite_eq_left ha, hz]
    _ = p := p.sum_single

omit [Fintype J] in
theorem moduleToGroupAlgebra_smul (s : Finset J) (p : MvPolynomial J R)
    (z : LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R)) :
    moduleToGroupAlgebra s (p • z) = polynomialToGroupAlgebra p * moduleToGroupAlgebra s z := by
  change ringLocalizationMap s (moduleRingEquiv s (p • z)) =
    polynomialToGroupAlgebra p * ringLocalizationMap s (moduleRingEquiv s z)
  rw [map_smul, Algebra.smul_def, map_mul, ringLocalizationMap_base]

omit [Fintype J] in
theorem moduleToGroupAlgebra_restriction (s t : Finset J)
    (hst : product (R := R) s ∣ product t)
    (z : LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R)) :
    moduleToGroupAlgebra t (restriction (product s) (product t) hst z) =
      moduleToGroupAlgebra s z := by
  induction z using LocalizedModule.induction_on with
  | _ p den =>
    obtain ⟨n, hn⟩ := den.property
    have hden : den = powerDenominator (product (R := R) s) n := Subtype.ext hn.symm
    subst den
    change moduleToGroupAlgebra t (restriction (product s) (product t) hst
      (fraction (product s) p n)) = moduleToGroupAlgebra s (fraction (product s) p n)
    apply ((product_isUnit (R := R) s).pow n).mul_left_cancel
    rw [← map_pow, ← moduleToGroupAlgebra_smul, ← moduleToGroupAlgebra_smul,
      ← map_smul, power_smul_fraction, restriction_fraction_zero]
    simp only [moduleToGroupAlgebra_fraction, zero_smul, neg_zero]

theorem pieceToLaurent_restriction [DecidableEq J] {s t : Finset J} (hst : s ⊆ t)
    (d : ℤ) (z : Piece (R := R) s d) :
    pieceToLaurent t d (setRestriction grading grading MvPolynomial.X variable_mem hst d z) =
      pieceToLaurent s d z := by
  ext a
  change (moduleToGroupAlgebra t (restriction (product s) (product t)
    (coverProduct_dvd grading MvPolynomial.X variable_mem hst) z.val)).coeff a.val =
    (moduleToGroupAlgebra s z.val).coeff a.val
  exact congrArg (fun l : GroupAlgebra (J := J) (R := R) => l.coeff a.val)
    (moduleToGroupAlgebra_restriction s t
      (coverProduct_dvd grading MvPolynomial.X variable_mem hst) z.val)

end
end PiExponent.GradedPolynomialLaurent

end OAI
