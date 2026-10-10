import OAI.AlgebraicGeometry.SurfaceCones.KummerShiftedDiagonalNormalization

namespace OAI


noncomputable section
open Algebra MvPolynomial
open scoped BigOperators
namespace KummerAffineExtra
open KummerLines
variable (p : ℕ) [Fact p.Prime] (j : Fin 2)
lemma remainingRoot_inv_mem (i : Fin 3) :
    (KummerCover.fieldRoot (p := p) radicand (remainingIndex j i))⁻¹ ∈ chartRootAlgebra p j := by
  let z : chartRootAlgebra p j := ⟨KummerCover.fieldRoot (p := p) radicand (remainingIndex j i),
    remainingRoot_mem_chartRootAlgebra p j i⟩
  have hz : z ^ p = algebraMap (S p j) (chartRootAlgebra p j)
      (algebraMap R (S p j) (lineForm (remainingIndex j i))) := by
    apply Subtype.ext
    exact (KummerCover.fieldRoot_pow radicand (remainingIndex j i)).trans
      (IsScalarTower.algebraMap_apply R (S p j) (L p) _)
  have hu : IsUnit (z ^ p) := by
    rw [hz]
    exact (remaining_unit p j i).map (algebraMap (S p j) (chartRootAlgebra p j))
  exact Submonoid.inv_mem_of_isUnit ((isUnit_pow_iff (NeZero.ne p)).mp hu)
end KummerAffineExtra

namespace FieldPrincipalOpen
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
lemma inv_mem_of_dvd_mem (A : Subalgebra k L) (d x : A) (hd : d ≠ 0)
    (hi : (d : L)⁻¹ ∈ A) (hxd : x ∣ d) : (x : L)⁻¹ ∈ A := by
  have hu : IsUnit d := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(d : L)⁻¹,hi⟩,?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ (by
      intro h
      exact hd (Subtype.ext h))
  exact Submonoid.inv_mem_of_isUnit (isUnit_of_dvd_unit hxd hu)
lemma away_regular (A : Subalgebra k L) [IsFractionRing A L] (d : A) (hd : d ≠ 0)
    [IsRegularRing A] : IsRegularRing (away A d hd) :=
  RegularLocalization.regular (S := away A d hd) (Submonoid.powers d)
end FieldPrincipalOpen

namespace ExplicitCone

def affineRegularAlgebra (j : Fin 2) : Subalgebra ℂ L where
  toSubsemiring := (KummerAffineExtra.chartRootAlgebra 7 j).toSubsemiring
  algebraMap_mem' c := by
    have h := (KummerAffineExtra.chartRootAlgebra 7 j).algebraMap_mem
      (algebraMap (KummerAffineExtra.B 7 j) (KummerAffineExtra.S 7 j)
        (algebraMap ℂ (KummerAffineExtra.B 7 j) c))
    rw [← IsScalarTower.algebraMap_apply (KummerAffineExtra.B 7 j) (KummerAffineExtra.S 7 j) L] at h
    exact h
lemma y_mem_affineRegular (j : Fin 2) (i : Fin 5) : y i ∈ affineRegularAlgebra j :=
  KummerAffineExtra.allRoots_mem_chartRootAlgebra 7 j i
lemma affineUnitRoot_inv_mem (j : Fin 2) (i : Fin 3) :
    (y (KummerAffineExtra.remainingIndex j i))⁻¹ ∈ affineRegularAlgebra j :=
  KummerAffineExtra.remainingRoot_inv_mem 7 j i
instance affineRegular_fractionRing (j : Fin 2) : IsFractionRing (affineRegularAlgebra j) L :=
  inferInstanceAs (IsFractionRing (KummerAffineExtra.chartRootAlgebra 7 j) L)
lemma affineRegular_regular (j : Fin 2) : IsRegularRing (affineRegularAlgebra j) :=
  KummerAffineExtra.chartRootAlgebra_regular 7 j

def affineFirstRoot (j : Fin 2) : affineRegularAlgebra j := ⟨y 0, y_mem_affineRegular j 0⟩
lemma affineFirstRoot_ne_zero (j : Fin 2) : affineFirstRoot j ≠ 0 := by
  intro h
  exact y_ne_zero 0 (congrArg Subtype.val h)
def affinePuncturedRegular (j : Fin 2) : Subalgebra ℂ L :=
  FieldPrincipalOpen.away (affineRegularAlgebra j) (affineFirstRoot j) (affineFirstRoot_ne_zero j)
lemma affineRegular_le_punctured (j : Fin 2) : affineRegularAlgebra j ≤ affinePuncturedRegular j :=
  FieldPrincipalOpen.le_away _ _ _
lemma y_mem_affinePunctured (j : Fin 2) (i : Fin 5) : y i ∈ affinePuncturedRegular j :=
  affineRegular_le_punctured j (y_mem_affineRegular j i)
lemma y0_inv_mem_affinePunctured (j : Fin 2) : (y 0)⁻¹ ∈ affinePuncturedRegular j :=
  FieldPrincipalOpen.inv_mem_away _ _ _
lemma y3_inv_mem_affinePunctured (j : Fin 2) : (y 3)⁻¹ ∈ affinePuncturedRegular j := by
  apply affineRegular_le_punctured j
  fin_cases j
  · exact affineUnitRoot_inv_mem 0 1
  · exact affineUnitRoot_inv_mem 1 2
lemma affinePunctured_regular (j : Fin 2) : IsRegularRing (affinePuncturedRegular j) := by
  have : IsRegularRing (affineRegularAlgebra j) := affineRegular_regular j
  exact FieldPrincipalOpen.away_regular (affineRegularAlgebra j) (affineFirstRoot j) (affineFirstRoot_ne_zero j)

lemma sectionChart_le_affinePunctured (j : Fin 2) : sectionChart ≤ affinePuncturedRegular j := by
  rw [sectionChart_eq]
  apply Algebra.adjoin_le
  rintro t (⟨i,rfl⟩ | ht)
  · exact y_mem_affinePunctured j i
  · rcases (show t = ratioQ ∨ t = ratioR from by simpa using ht) with rfl | rfl
    · unfold ratioQ
      rw [div_eq_mul_inv, mul_inv_rev]
      exact (affinePuncturedRegular j).mul_mem
        ((affinePuncturedRegular j).mul_mem (y_mem_affinePunctured j 1) (y_mem_affinePunctured j 2))
        ((affinePuncturedRegular j).mul_mem (y3_inv_mem_affinePunctured j) (y0_inv_mem_affinePunctured j))
    · unfold ratioR
      rw [div_eq_mul_inv, mul_inv_rev]
      exact (affinePuncturedRegular j).mul_mem (y_mem_affinePunctured j 4)
        ((affinePuncturedRegular j).mul_mem (y3_inv_mem_affinePunctured j) (y0_inv_mem_affinePunctured j))

def affineSectionIndex (j : Fin 2) : Fin 4 → Fin 5 := Fin.cases 0 (KummerAffineExtra.remainingIndex j)
def affineSectionRoot (j : Fin 2) (i : Fin 4) : sectionChart :=
  ⟨y (affineSectionIndex j i), y_mem_sectionChart _⟩
def affineSectionDenominator (j : Fin 2) : sectionChart := ∏ i : Fin 4, affineSectionRoot j i
lemma affineSectionDenominator_ne_zero (j : Fin 2) : affineSectionDenominator j ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ h
  exact y_ne_zero (affineSectionIndex j i) (congrArg Subtype.val h)
def affineSectionOpen (j : Fin 2) : Subalgebra ℂ L :=
  FieldPrincipalOpen.away sectionChart (affineSectionDenominator j) (affineSectionDenominator_ne_zero j)
lemma sectionChart_le_affineOpen (j : Fin 2) : sectionChart ≤ affineSectionOpen j :=
  FieldPrincipalOpen.le_away _ _ _
lemma y_mem_affineOpen (j : Fin 2) (i : Fin 5) : y i ∈ affineSectionOpen j :=
  sectionChart_le_affineOpen j (y_mem_sectionChart i)
lemma affineSectionRoot_inv_mem (j : Fin 2) (i : Fin 4) :
    (y (affineSectionIndex j i))⁻¹ ∈ affineSectionOpen j := by
  let f : sectionChart →ₐ[ℂ] affineSectionOpen j := Subalgebra.inclusion (sectionChart_le_affineOpen j)
  have hn : f (affineSectionDenominator j) ≠ 0 := by
    intro h
    exact affineSectionDenominator_ne_zero j ((Subalgebra.inclusion_injective _).eq_iff.mp h)
  apply FieldPrincipalOpen.inv_mem_of_dvd_mem (affineSectionOpen j)
    (f (affineSectionDenominator j)) (f (affineSectionRoot j i)) hn
    (FieldPrincipalOpen.inv_mem_away _ _ _)
  exact map_dvd f (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
lemma affineSectionOpen_le (j : Fin 2) : affineSectionOpen j ≤ affinePuncturedRegular j := by
  apply (FieldPrincipalOpen.away_le_iff sectionChart (affineSectionDenominator j)
    (affineSectionDenominator_ne_zero j) (affinePuncturedRegular j)).mpr
  refine ⟨sectionChart_le_affinePunctured j,?_⟩
  change (∏ i : Fin 4, y (affineSectionIndex j i))⁻¹ ∈ affinePuncturedRegular j
  rw [← Finset.prod_inv_distrib]
  apply Subalgebra.prod_mem
  intro i _
  refine Fin.cases ?_ (fun k => ?_) i
  · exact y0_inv_mem_affinePunctured j
  · exact affineRegular_le_punctured j (affineUnitRoot_inv_mem j k)

lemma affine_B_mem_sectionOpen (j : Fin 2) (b : KummerAffineExtra.B 7 j) :
    (b : L) ∈ affineSectionOpen j := by
  have h := b.property
  change (b : L) ∈ Algebra.adjoin ℂ (Set.range (KummerAffineExtra.coordinateRoot 7 j)) at h
  exact (Algebra.adjoin_le (by rintro _ ⟨i,rfl⟩; exact y_mem_affineOpen j _)) h
lemma affine_bDenominator_image (j : Fin 2) :
    algebraMap (KummerAffineExtra.B 7 j) L (KummerAffineExtra.bDenominator 7 j) =
    y (KummerAffineExtra.remainingIndex j 0) ^ 7 * y (KummerAffineExtra.remainingIndex j 1) ^ 7 *
      y (KummerAffineExtra.remainingIndex j 2) ^ 7 := by
  change algebraMap (KummerAffineExtra.B 7 j) L
    (algebraMap R (KummerAffineExtra.B 7 j) (KummerAffineExtra.chartDenominator j)) = _
  rw [← IsScalarTower.algebraMap_apply R (KummerAffineExtra.B 7 j) L]
  simp only [KummerAffineExtra.chartDenominator, map_mul, y_power]
lemma affine_bDenominator_inv_mem (j : Fin 2) :
    (algebraMap (KummerAffineExtra.B 7 j) L (KummerAffineExtra.bDenominator 7 j))⁻¹ ∈ affineSectionOpen j := by
  rw [affine_bDenominator_image, mul_inv_rev, mul_inv_rev, ← inv_pow, ← inv_pow, ← inv_pow]
  exact (affineSectionOpen j).mul_mem
    ((affineSectionOpen j).pow_mem (affineSectionRoot_inv_mem j 3) 7)
    ((affineSectionOpen j).mul_mem ((affineSectionOpen j).pow_mem (affineSectionRoot_inv_mem j 2) 7)
      ((affineSectionOpen j).pow_mem (affineSectionRoot_inv_mem j 1) 7))
lemma affine_S_mem_sectionOpen (j : Fin 2) (s : KummerAffineExtra.S 7 j) :
    algebraMap (KummerAffineExtra.S 7 j) L s ∈ affineSectionOpen j := by
  apply FieldPrincipalOpen.localizationImage_mem (affineSectionOpen j) (KummerAffineExtra.bDenominator 7 j)
    ((isUnit_iff_ne_zero).mp (KummerAffineExtra.bDenominator_unit_in_L 7 j))
    (fun b => affine_B_mem_sectionOpen j b) (affine_bDenominator_inv_mem j)
lemma affineRegular_le_sectionOpen (j : Fin 2) : affineRegularAlgebra j ≤ affineSectionOpen j := by
  intro t ht
  change t ∈ Algebra.adjoin (KummerAffineExtra.S 7 j) (KummerAffineExtra.remainingRoots 7 j : Set L) at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    classical
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
    exact y_mem_affineOpen j _
  | algebraMap s => exact affine_S_mem_sectionOpen j s
  | add x y hx hy h₁ h₂ => exact (affineSectionOpen j).add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact (affineSectionOpen j).mul_mem h₁ h₂
lemma affinePunctured_le_sectionOpen (j : Fin 2) : affinePuncturedRegular j ≤ affineSectionOpen j := by
  apply (FieldPrincipalOpen.away_le_iff (affineRegularAlgebra j) (affineFirstRoot j)
    (affineFirstRoot_ne_zero j) (affineSectionOpen j)).mpr
  exact ⟨affineRegular_le_sectionOpen j,affineSectionRoot_inv_mem j 0⟩

theorem affineSectionOpen_eq (j : Fin 2) : affineSectionOpen j = affinePuncturedRegular j :=
  le_antisymm (affineSectionOpen_le j) (affinePunctured_le_sectionOpen j)
theorem sectionChart_affineOpen_regular (j : Fin 2) :
    IsRegularRing (Localization.Away (affineSectionDenominator j)) := by
  have : IsRegularRing (affinePuncturedRegular j) := affinePunctured_regular j
  exact FieldPrincipalOpen.regular_away_of_eq sectionChart (affineSectionDenominator j)
    (affineSectionDenominator_ne_zero j) (affinePuncturedRegular j) (affineSectionOpen_eq j)
end ExplicitCone

end


noncomputable section
namespace KummerSectionCover

/-- The five literal smooth opens of the chosen H-chart cover every
prime, not merely its complex closed points. This is the domain-level
calculation used after reduction by an arbitrary prime. -/
theorem cover {D : Type*} [CommRing D] [IsDomain D]
    (a b c d e q r : D)
    (hac : a ^ 7 - c ^ 7 = 1) (hbd : b ^ 7 - d ^ 7 = 1)
    (he : e ^ 7 = a ^ 7 - b ^ 7) (hqr : q ^ 7 - r ^ 7 = 1)
    (hp : a * d * q = b * c) :
    c * d * r ≠ 0 ∨ c * d * q ≠ 0 ∨
      a * b * r ≠ 0 ∨ a * b * q ≠ 0 ∨ a * a * d * e ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨hcr,hcq,har,haq,had⟩ := hn
  have cancel_pair (x : D) (hxq : x * q = 0) (hxr : x * r = 0) : x = 0 := by
    by_contra hx
    have hq : q = 0 := (mul_eq_zero.mp hxq).resolve_left hx
    have hr : r = 0 := (mul_eq_zero.mp hxr).resolve_left hx
    simp [hq,hr] at hqr
  have hcd := cancel_pair (c*d) hcq hcr
  have hab := cancel_pair (a*b) haq har
  rcases mul_eq_zero.mp hcd with hc | hd
  · rcases mul_eq_zero.mp hab with ha | hb
    · simp [ha,hc] at hac
    · have ha : a ≠ 0 := by intro ha; simp [ha,hc] at hac
      have hd : d ≠ 0 := by intro hd; simp [hb,hd] at hbd
      have he' : e ≠ 0 := by
        intro h
        have h7 : a ^ 7 = 1 := by simpa [hc] using hac
        simp [h,hb,h7] at he
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero ha ha) hd) he') had
  · rcases mul_eq_zero.mp hab with ha | hb
    · have hbc : b * c = 0 := by simpa [ha] using hp.symm
      rcases mul_eq_zero.mp hbc with hb | hc
      · simp [hb,hd] at hbd
      · simp [ha,hc] at hac
    · simp [hb,hd] at hbd
end KummerSectionCover


namespace RegularOnPrincipalOpen
variable {A : Type*} [CommRing A]

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
/-- Transfer regularity from the base-changed principal open to its
canonical localization. -/
theorem away_of_tensor {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R A] [Algebra R T] (d : R) [IsLocalization.Away d T]
    [IsRegularRing (T ⊗[R] A)] :
    IsRegularRing (Localization.Away (algebraMap R A d)) := by
  exact IsRegularRing.of_ringEquiv
    (IsLocalization.Away.tensorRightEquiv (R := R) (A := T) (r := d) A).toRingEquiv


/-- A prime in a regular principal open has regular local ring. -/
theorem atPrime (q : Ideal A) [q.IsPrime] (f : A) (hf : f ∉ q)
    [IsRegularRing (Localization.Away f)] : IsRegularLocalRing (Localization.AtPrime q) := by
  let S := Localization.Away f
  let P := q.map (algebraMap A S)
  have hd : Disjoint (Submonoid.powers f : Set A) (q : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨n, rfl⟩ h
    exact hf ((inferInstance : q.IsPrime).mem_of_pow_mem n h)
  have hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) S q inferInstance hd
  let := hP
  have hc : P.comap (algebraMap A S) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) S inferInstance hd
  have : IsLocalization.AtPrime (Localization.AtPrime P) q := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) (Localization.AtPrime P) P
    simpa only [IsLocalization.AtPrime, hc] using h
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime P)
      (Localization.AtPrime q)).toRingEquiv

/-- Transfer a regular prime local ring across an actual ring isomorphism. -/
theorem atPrime_of_equiv {B : Type*} [CommRing B] (e : A ≃+* B)
    (q : Ideal A) [q.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime (q.comap e.symm.toRingHom))] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  exact IsRegularLocalRing.of_ringEquiv
    (Localization.localRingEquiv (q.comap e.symm.toRingHom) q e.symm rfl)
/-- A principal open on an isomorphic ring suffices for local regularity. -/
theorem atPrime_of_equiv_away {B : Type*} [CommRing B] (e : A ≃+* B)
    (q : Ideal A) [q.IsPrime] (f : B) (hf : e.symm f ∉ q)
    [IsRegularRing (Localization.Away f)] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let q' := q.comap e.symm.toRingHom
  have hf' : f ∉ q' := hf
  let : IsRegularLocalRing (Localization.AtPrime q') := atPrime q' f hf'
  exact atPrime_of_equiv e q
end RegularOnPrincipalOpen

end


noncomputable section
namespace ExplicitCone

/-- The original five roots and the two literal section ratios, as
functions in the actual affine chart of the eighteen source sections. -/
def sRoot (i : Fin 5) : sectionChart := ⟨y i,y_mem_sectionChart i⟩
def sQ : sectionChart := ⟨ratioQ,ratioQ_mem_sectionChart⟩
def sR : sectionChart := ⟨ratioR,ratioR_mem_sectionChart⟩
lemma sRoot_fermat₀ : sRoot 0 ^ 7 - sRoot 2 ^ 7 = 1 := by
  apply Subtype.ext
  change y 0 ^ 7 - y 2 ^ 7 = 1
  rw [y_power_zero,y_power_two]
  ring
lemma sRoot_fermat₁ : sRoot 1 ^ 7 - sRoot 3 ^ 7 = 1 := by
  apply Subtype.ext
  change y 1 ^ 7 - y 3 ^ 7 = 1
  rw [y_power_one,y_power_three]
  ring
lemma sRoot_diagonal : sRoot 4 ^ 7 = sRoot 0 ^ 7 - sRoot 1 ^ 7 := by
  apply Subtype.ext
  exact y_power_four.trans (congrArg₂ (· - ·) y_power_zero.symm y_power_one.symm)
lemma sRatio_fermat : sQ ^ 7 - sR ^ 7 = 1 := Subtype.ext ratio_fermat
lemma sRatio_product : sRoot 0 * sRoot 3 * sQ = sRoot 1 * sRoot 2 :=
  Subtype.ext ratioQ_product
lemma tripleSectionDenominator_eq : tripleSectionDenominator = sRoot 2 * sRoot 3 * sR := rfl
lemma diagonalSectionDenominator_eq : diagonalSectionDenominator = sRoot 2 * sRoot 3 * sQ := rfl
lemma shiftedSectionDenominator_eq : shiftedSectionDenominator = sRoot 0 * sRoot 1 * sR := rfl
lemma shiftedDiagonalSectionDenominator_eq : shiftedDiagonalSectionDenominator = sRoot 0 * sRoot 1 * sQ := rfl
lemma affineSectionDenominator_zero_eq : affineSectionDenominator 0 = sRoot 0 * sRoot 0 * sRoot 3 * sRoot 4 := by
  apply Subtype.ext
  change (∏ i : Fin 4, y (affineSectionIndex 0 i)) = y 0 * y 0 * y 3 * y 4
  rw [Fin.prod_univ_four]
  rfl

/-- The exact five normalization opens cover every prime of the literal
polarization chart; no closed-point restriction is imposed. -/
theorem sectionChart_open_cover (P : Ideal sectionChart) [P.IsPrime] :
    tripleSectionDenominator ∉ P ∨ diagonalSectionDenominator ∉ P ∨
      shiftedSectionDenominator ∉ P ∨ shiftedDiagonalSectionDenominator ∉ P ∨
        affineSectionDenominator 0 ∉ P := by
  let f : sectionChart →+* sectionChart ⧸ P := Ideal.Quotient.mk P
  have ha : f (sRoot 0) ^ 7 - f (sRoot 2) ^ 7 = 1 := by
    simpa only [RingHom.map_sub f, map_pow f, RingHom.map_one f] using
      congrArg f sRoot_fermat₀
  have hb : f (sRoot 1) ^ 7 - f (sRoot 3) ^ 7 = 1 := by
    simpa only [RingHom.map_sub f, map_pow f, RingHom.map_one f] using
      congrArg f sRoot_fermat₁
  have he : f (sRoot 4) ^ 7 = f (sRoot 0) ^ 7 - f (sRoot 1) ^ 7 := by
    simpa only [RingHom.map_sub f, map_pow f] using congrArg f sRoot_diagonal
  have hq : f sQ ^ 7 - f sR ^ 7 = 1 := by
    simpa only [RingHom.map_sub f, map_pow f, RingHom.map_one f] using
      congrArg f sRatio_fermat
  have hp : f (sRoot 0) * f (sRoot 3) * f sQ = f (sRoot 1) * f (sRoot 2) := by
    simpa only [RingHom.map_mul f] using congrArg f sRatio_product
  have h := KummerSectionCover.cover (f (sRoot 0)) (f (sRoot 1)) (f (sRoot 2))
    (f (sRoot 3)) (f (sRoot 4)) (f sQ) (f sR) ha hb he hq hp
  simpa only [tripleSectionDenominator_eq,diagonalSectionDenominator_eq,
    shiftedSectionDenominator_eq,shiftedDiagonalSectionDenominator_eq,
    affineSectionDenominator_zero_eq, ← Ideal.Quotient.eq_zero_iff_mem, map_mul] using h

instance sectionChart_noetherian : IsNoetherianRing sectionChart :=
  Algebra.FiniteType.isNoetherianRing ℂ sectionChart

/-- The ENTIRE affine chart of the fixed source section z₀z₁z₄ is regular,
including all primes above both resolved triple points. -/
theorem sectionChart_regular : IsRegularRing sectionChart := by
  apply isRegularRing_iff.mpr
  intro P hP
  let := hP
  rcases sectionChart_open_cover P with ht | hd | hs | hsd | ha
  · let := sectionChart_tripleOpen_regular
    exact RegularOnPrincipalOpen.atPrime P tripleSectionDenominator ht
  · let := sectionChart_diagonalOpen_regular
    exact RegularOnPrincipalOpen.atPrime P diagonalSectionDenominator hd
  · let := sectionChart_shiftedOpen_regular
    exact RegularOnPrincipalOpen.atPrime P shiftedSectionDenominator hs
  · let := sectionChart_shiftedDiagonalOpen_regular
    exact RegularOnPrincipalOpen.atPrime P shiftedDiagonalSectionDenominator hsd
  · let := sectionChart_affineOpen_regular 0
    exact RegularOnPrincipalOpen.atPrime P (affineSectionDenominator 0) ha
end ExplicitCone


namespace NormalOnPrincipalOpen
variable {A : Type*} [CommRing A] [IsDomain A]

/-- Normality of a principal open implies normality at each prime in it. -/
theorem atPrime (q : Ideal A) [q.IsPrime] (f : A) (hf : f ∉ q)
    [IsIntegrallyClosed (Localization.Away f)] :
    IsIntegrallyClosed (Localization.AtPrime q) := by
  let S := Localization.Away f
  let P := q.map (algebraMap A S)
  have hd : Disjoint (Submonoid.powers f : Set A) (q : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨n, rfl⟩ h
    exact hf ((inferInstance : q.IsPrime).mem_of_pow_mem n h)
  have hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) S q inferInstance hd
  let := hP
  have hf0 : f ≠ 0 := fun h => hf (h ▸ q.zero_mem)
  have hM : Submonoid.powers f ≤ nonZeroDivisors A := by
    rintro a ⟨n,rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hf0)
  have : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors
  have hc : P.comap (algebraMap A S) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) S inferInstance hd
  have : IsLocalization.AtPrime (Localization.AtPrime P) q := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) (Localization.AtPrime P) P
    simpa only [IsLocalization.AtPrime, hc] using h
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime P)
      (Localization.AtPrime q)).toRingEquiv
end NormalOnPrincipalOpen


namespace FieldPrincipalOpen
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable (A : Subalgebra k L) [IsFractionRing A L] (d : A) (hd : d ≠ 0)

lemma normal_away [IsIntegrallyClosed A] : IsIntegrallyClosed (away A d hd) :=
  isIntegrallyClosed_of_isLocalization _ (Submonoid.powers d) (powers_le A d hd)
lemma normal_away_of_eq (B : Subalgebra k L) [IsIntegrallyClosed B]
    (h : away A d hd = B) : IsIntegrallyClosed (Localization.Away d) := by
  have : IsIntegrallyClosed (away A d hd) :=
    IsIntegrallyClosed.of_equiv (Subalgebra.equivOfEq _ _ h.symm).toRingEquiv
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv (Submonoid.powers d) (away A d hd) (Localization.Away d)).toRingEquiv
end FieldPrincipalOpen

namespace ExplicitCone

lemma sectionChart_tripleOpen_normal :
    IsIntegrallyClosed (Localization.Away tripleSectionDenominator) := by
  have : IsIntegrallyClosed tripleRegularAlgebra :=
    inferInstanceAs (IsIntegrallyClosed (KummerTriple.chartRootAlgebra 7))
  exact FieldPrincipalOpen.normal_away_of_eq sectionChart tripleSectionDenominator
    tripleSectionDenominator_ne_zero tripleRegularAlgebra tripleSectionOpen_eq
lemma sectionChart_diagonalOpen_normal :
    IsIntegrallyClosed (Localization.Away diagonalSectionDenominator) := by
  have : IsIntegrallyClosed diagonalRegularAlgebra :=
    inferInstanceAs (IsIntegrallyClosed (KummerTripleDiagonal.chartRootAlgebra 7))
  exact FieldPrincipalOpen.normal_away_of_eq sectionChart diagonalSectionDenominator
    diagonalSectionDenominator_ne_zero diagonalRegularAlgebra diagonalSectionOpen_eq
lemma sectionChart_shiftedOpen_normal :
    IsIntegrallyClosed (Localization.Away shiftedSectionDenominator) := by
  have : IsIntegrallyClosed shiftedRegularAlgebra :=
    inferInstanceAs (IsIntegrallyClosed (KummerShifted.chartRootAlgebra 7))
  exact FieldPrincipalOpen.normal_away_of_eq sectionChart shiftedSectionDenominator
    shiftedSectionDenominator_ne_zero shiftedRegularAlgebra shiftedSectionOpen_eq
lemma sectionChart_shiftedDiagonalOpen_normal :
    IsIntegrallyClosed (Localization.Away shiftedDiagonalSectionDenominator) := by
  have : IsIntegrallyClosed shiftedDiagonalRegularAlgebra :=
    inferInstanceAs (IsIntegrallyClosed (KummerShiftedDiagonal.chartRootAlgebra 7))
  exact FieldPrincipalOpen.normal_away_of_eq sectionChart shiftedDiagonalSectionDenominator
    shiftedDiagonalSectionDenominator_ne_zero shiftedDiagonalRegularAlgebra shiftedDiagonalSectionOpen_eq
lemma affinePunctured_normal (j : Fin 2) : IsIntegrallyClosed (affinePuncturedRegular j) := by
  have : IsIntegrallyClosed (affineRegularAlgebra j) :=
    inferInstanceAs (IsIntegrallyClosed (KummerAffineExtra.chartRootAlgebra 7 j))
  exact FieldPrincipalOpen.normal_away (affineRegularAlgebra j) (affineFirstRoot j) (affineFirstRoot_ne_zero j)
lemma sectionChart_affineOpen_normal (j : Fin 2) :
    IsIntegrallyClosed (Localization.Away (affineSectionDenominator j)) := by
  have : IsIntegrallyClosed (affinePuncturedRegular j) := affinePunctured_normal j
  exact FieldPrincipalOpen.normal_away_of_eq sectionChart (affineSectionDenominator j)
    (affineSectionDenominator_ne_zero j) (affinePuncturedRegular j) (affineSectionOpen_eq j)

/-- Normality is proved by descent from the actual Kummer normalizations,
not assumed as an unformalized consequence of regularity. -/
theorem sectionChart_normal : IsIntegrallyClosed sectionChart := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let := hP
  rcases sectionChart_open_cover P with ht | hd | hs | hsd | ha
  · let := sectionChart_tripleOpen_normal
    exact NormalOnPrincipalOpen.atPrime P tripleSectionDenominator ht
  · let := sectionChart_diagonalOpen_normal
    exact NormalOnPrincipalOpen.atPrime P diagonalSectionDenominator hd
  · let := sectionChart_shiftedOpen_normal
    exact NormalOnPrincipalOpen.atPrime P shiftedSectionDenominator hs
  · let := sectionChart_shiftedDiagonalOpen_normal
    exact NormalOnPrincipalOpen.atPrime P shiftedDiagonalSectionDenominator hsd
  · let := sectionChart_affineOpen_normal 0
    exact NormalOnPrincipalOpen.atPrime P (affineSectionDenominator 0) ha
end ExplicitCone


open Polynomial
namespace PolynomialFieldChart
variable {k L : Type*} [Field k] [Field L] [Algebra k L]
variable (A : Subalgebra k L) (c : L) (hc : c ≠ 0)

def scale : L[X] ≃ₐ[L] L[X] := by
  let := invertibleOfNonzero hc
  exact Polynomial.algEquivCMulXAddC c 0

def polynomialMap : A[X] →ₐ[k] RatFunc L :=
  (IsScalarTower.toAlgHom k L[X] (RatFunc L)).comp
    (((scale c hc).restrictScalars k).toAlgHom.comp (Polynomial.mapAlgHom A.val))

lemma polynomialMap_C (a : A) : polynomialMap A c hc (C a) = RatFunc.C (a : L) := by
  simp [polynomialMap,scale,Polynomial.algEquivCMulXAddC_apply]
lemma polynomialMap_X : polynomialMap A c hc X = RatFunc.C c * RatFunc.X := by
  simp [polynomialMap,scale,Polynomial.algEquivCMulXAddC_apply]
lemma polynomialMap_injective : Function.Injective (polynomialMap A c hc) :=
  (IsFractionRing.injective L[X] (RatFunc L)).comp
    ((scale c hc).injective.comp (Polynomial.map_injective _ Subtype.val_injective))

/-- The polynomial line chart is an actual subalgebra of the ORIGINAL
cone function field, with fibre coordinate cX, not an abstract replacement. -/
def chart : Subalgebra k (RatFunc L) := (polynomialMap A c hc).range

def polynomialEquiv : A[X] ≃ₐ[k] chart A c hc :=
  AlgEquiv.ofInjective (polynomialMap A c hc) (polynomialMap_injective A c hc)

lemma constant_mem (a : A) : RatFunc.C (a : L) ∈ chart A c hc :=
  ⟨C a,polynomialMap_C A c hc a⟩
lemma variable_mem : RatFunc.C c * RatFunc.X ∈ chart A c hc :=
  ⟨X,polynomialMap_X A c hc⟩

def fiberCoordinate : chart A c hc := ⟨RatFunc.C c * RatFunc.X,variable_mem A c hc⟩
lemma variable_ne_zero : fiberCoordinate A c hc ≠ 0 := by
  intro h
  exact mul_ne_zero (by simpa only [map_zero] using RatFunc.C_injective.ne hc)
    RatFunc.X_ne_zero (congrArg Subtype.val h)

/-- The exact universal membership criterion for this concrete chart. -/
lemma chart_le_iff (B : Subalgebra k (RatFunc L)) : chart A c hc ≤ B ↔
    (∀ a : A, RatFunc.C (a : L) ∈ B) ∧ RatFunc.C c * RatFunc.X ∈ B := by
  constructor
  · intro h
    exact ⟨fun a => h (constant_mem A c hc a), h (variable_mem A c hc)⟩
  · rintro ⟨ha,hx⟩ f ⟨p,rfl⟩
    change polynomialMap A c hc p ∈ B
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact B.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        polynomialMap_C, polynomialMap_X]
      exact B.mul_mem (ha a) (B.pow_mem hx _)

lemma regular [IsRegularRing A] : IsRegularRing (chart A c hc) :=
  IsRegularRing.of_ringEquiv (polynomialEquiv A c hc).toRingEquiv
lemma normal [IsIntegrallyClosed A] : IsIntegrallyClosed (chart A c hc) :=
  IsIntegrallyClosed.of_equiv (polynomialEquiv A c hc).toRingEquiv

lemma polynomialEquiv_X : polynomialEquiv A c hc X = fiberCoordinate A c hc := by
  apply Subtype.ext
  exact polynomialMap_X A c hc

/-- The exceptional zero section is the ORIGINAL coefficient chart. -/
def exceptionalEquiv :
    (chart A c hc ⧸ Ideal.span {fiberCoordinate A c hc}) ≃ₐ[k] A := by
  let J : Ideal A[X] := Ideal.span {X - C (0 : A)}
  have hJ : Ideal.span {fiberCoordinate A c hc} =
      J.map (polynomialEquiv A c hc).toRingHom := by
    dsimp [J]
    rw [Ideal.map_span]
    simp only [Set.image_singleton, Polynomial.C_0, sub_zero]
    change Ideal.span {fiberCoordinate A c hc} =
      Ideal.span {polynomialEquiv A c hc X}
    rw [polynomialEquiv_X]
  exact (Ideal.quotientEquivAlg J _ (polynomialEquiv A c hc) hJ).symm.trans
    ((Polynomial.quotientSpanXSubCAlgEquiv (0 : A)).restrictScalars k)

lemma exceptional_prime : (Ideal.span {fiberCoordinate A c hc}).IsPrime := by
  have : IsDomain (chart A c hc ⧸ Ideal.span {fiberCoordinate A c hc}) :=
    (exceptionalEquiv A c hc).injective.isDomain (exceptionalEquiv A c hc).toRingHom
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- Concrete coefficient test in the original cone function field. -/
lemma scaled_coefficient_mem (p : L[X])
    (hp : algebraMap L[X] (RatFunc L) p ∈ chart A c hc) (n : ℕ) :
    p.coeff n / c ^ n ∈ A := by
  obtain ⟨q,hq⟩ := hp
  have he : scale c hc (q.map A.val.toRingHom) = p :=
    IsFractionRing.injective L[X] (RatFunc L) hq
  have hn := congrArg (fun f : L[X] => f.coeff n) he
  simp only [scale, Polynomial.algEquivCMulXAddC_apply, Polynomial.C_0,
    add_zero] at hn
  change ((q.map A.val.toRingHom).comp (C c * X)).coeff n = p.coeff n at hn
  simp only [Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at hn
  rw [← hn, mul_div_cancel_right₀ _ (pow_ne_zero n hc)]
  exact (q.coeff n).property

variable [IsFractionRing A L]
lemma field_generated : IntermediateField.adjoin k (chart A c hc : Set (RatFunc L)) = ⊤ := by
  let S := IntermediateField.adjoin k (chart A c hc : Set (RatFunc L))
  have ha (a : A) : RatFunc.C (a : L) ∈ S :=
    IntermediateField.subset_adjoin k _ (constant_mem A c hc a)
  have hL (a : L) : RatFunc.C a ∈ S := by
    obtain ⟨u,v,_,h⟩ := IsFractionRing.div_surjective A a
    rw [← h,map_div₀]
    exact S.div_mem (ha u) (ha v)
  have hcx : RatFunc.C c * RatFunc.X ∈ S :=
    IntermediateField.subset_adjoin k _ (variable_mem A c hc)
  have hx : (RatFunc.X : RatFunc L) ∈ S := by
    have he : (RatFunc.X : RatFunc L) = (RatFunc.C c * RatFunc.X) / RatFunc.C c := by
      rw [mul_div_cancel_left₀ _ (by simpa only [map_zero] using RatFunc.C_injective.ne hc)]
    rw [he]
    exact S.div_mem hcx (hL c)
  have hp (p : L[X]) : algebraMap L[X] (RatFunc L) p ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
    | monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      exact S.mul_mem (hL a) (pow_mem hx n)
  apply top_unique
  intro f _
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective L[X] f
  exact S.div_mem (hp p) (hp q)

instance : IsFractionRing (chart A c hc) (RatFunc L) :=
  IsFractionRing.of_field (chart A c hc) (RatFunc L) fun f => by
    have hf : f ∈ IntermediateField.adjoin k (chart A c hc : Set (RatFunc L)) := by
      rw [field_generated]; trivial
    obtain ⟨p,hp,q,hq,h⟩ := IntermediateField.mem_adjoin_iff_div.mp hf
    rw [Algebra.adjoin_eq] at hp hq
    exact ⟨⟨p,hp⟩,⟨q,hq⟩,h⟩

/-- A normal actual polynomial chart containing the cone also contains
its WHOLE normalization in the same function field. -/
lemma integralClosure_le [IsIntegrallyClosed A] (B : Subalgebra k (RatFunc L))
    (hB : B ≤ chart A c hc) :
    (integralClosure B (RatFunc L)).restrictScalars k ≤ chart A c hc := by
  let : Algebra B (chart A c hc) := (Subalgebra.inclusion hB).toAlgebra
  let : IsScalarTower B (chart A c hc) (RatFunc L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsIntegrallyClosed (chart A c hc) := normal A c hc
  intro x hx
  have h : IsIntegral (chart A c hc) x := (show IsIntegral B x from hx).tower_top
  obtain ⟨y,hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact hy ▸ y.property
end PolynomialFieldChart

end


noncomputable section
namespace ExplicitCone
open Polynomial

/-- The actual polynomial Cartier chart above the fixed section z₀z₁z₄,
inside the SAME rational function field used for the source cone. -/
def cartierChart : Subalgebra ℂ (RatFunc L) :=
  PolynomialFieldChart.chart sectionChart (sectionCoefficient (0,0))
    sectionCoefficient_base_ne_zero

def cartierParameter : cartierChart :=
  PolynomialFieldChart.fiberCoordinate sectionChart (sectionCoefficient (0,0))
    sectionCoefficient_base_ne_zero

lemma cartierParameter_ne_zero : cartierParameter ≠ 0 :=
  PolynomialFieldChart.variable_ne_zero _ _ _

lemma constant_mem_cartierChart (a : sectionChart) : RatFunc.C (a : L) ∈ cartierChart :=
  PolynomialFieldChart.constant_mem _ _ _ a

lemma ratio_mem_sectionChart (i : Fin 6 × Fin 3) : sectionRatio i ∈ sectionChart :=
  Algebra.subset_adjoin (Set.mem_range_self i)

lemma generator_eq_ratio_mul (i : Fin 6 × Fin 3) :
    generator i = RatFunc.C (sectionRatio i) * generator (0,0) := by
  unfold generator sectionRatio
  rw [map_div₀]
  have h : RatFunc.C (sectionCoefficient (0,0)) ≠ (0 : RatFunc L) := by
    simpa only [map_zero] using RatFunc.C_injective.ne sectionCoefficient_base_ne_zero
  field_simp

lemma generator_mem_cartierChart (i : Fin 6 × Fin 3) : generator i ∈ cartierChart := by
  rw [generator_eq_ratio_mul]
  exact cartierChart.mul_mem (constant_mem_cartierChart ⟨_,ratio_mem_sectionChart i⟩)
    cartierParameter.property

lemma algebra_le_cartierChart : algebra ≤ cartierChart := by
  apply Algebra.adjoin_le
  rintro _ ⟨i,rfl⟩
  exact generator_mem_cartierChart i

/-- The WHOLE integral closure of the literal section-generated cone in
its function field; no smaller radical subalgebra is substituted. -/
def normalizedCone : Subalgebra ℂ (RatFunc L) :=
  (integralClosure algebra (RatFunc L)).restrictScalars ℂ

lemma normalizedCone_le_cartierChart : normalizedCone ≤ cartierChart := by
  let := sectionChart_normal
  exact PolynomialFieldChart.integralClosure_le _ _ _ algebra algebra_le_cartierChart

lemma algebra_le_normalizedCone : algebra ≤ normalizedCone := by
  intro a ha
  exact isIntegral_algebraMap (x := (⟨a,ha⟩ : algebra))

/-- The genuine affine blowup-chart algebra: adjoin the original eighteen
section ratios to the whole normalization, all in the original function
field. This definition is not an interface assuming a Cartier model. -/
def normalizedBlowupChart : Subalgebra ℂ (RatFunc L) :=
  normalizedCone ⊔ Algebra.adjoin ℂ (Set.range fun i => generator i / generator (0,0))

lemma generator_ratio_eq (i : Fin 6 × Fin 3) :
    generator i / generator (0,0) = RatFunc.C (sectionRatio i) := by
  rw [generator_eq_ratio_mul]
  apply mul_div_cancel_right₀
  exact mul_ne_zero (by simpa only [map_zero] using
    RatFunc.C_injective.ne sectionCoefficient_base_ne_zero) RatFunc.X_ne_zero

lemma constant_mem_normalizedBlowupChart (a : sectionChart) :
    RatFunc.C (a : L) ∈ normalizedBlowupChart := by
  have h : sectionChart ≤ normalizedBlowupChart.comap
      (IsScalarTower.toAlgHom ℂ L (RatFunc L)) := by
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    change RatFunc.C (sectionRatio i) ∈ normalizedBlowupChart
    rw [← generator_ratio_eq]
    exact (show Algebra.adjoin ℂ (Set.range fun i => generator i / generator (0,0)) ≤
      normalizedBlowupChart from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_range_self i))
  exact h a.property

/-- Exact equality with the normal polynomial-line chart, not merely a
finite birational map or equality after discarding the exceptional locus. -/
theorem normalizedBlowupChart_eq : normalizedBlowupChart = cartierChart := by
  apply le_antisymm
  · apply sup_le normalizedCone_le_cartierChart
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    change generator i / generator (0,0) ∈ cartierChart
    rw [generator_ratio_eq]
    exact constant_mem_cartierChart ⟨_,ratio_mem_sectionChart i⟩
  · apply (PolynomialFieldChart.chart_le_iff _ _ _ _).mpr
    refine ⟨constant_mem_normalizedBlowupChart, ?_⟩
    exact (show normalizedCone ≤ normalizedBlowupChart from le_sup_left)
      (algebra_le_normalizedCone
        (Algebra.subset_adjoin (Set.mem_range_self (0,0))))

def cartierPolynomialEquiv : sectionChart[X] ≃ₐ[ℂ] cartierChart :=
  PolynomialFieldChart.polynomialEquiv _ _ _

theorem cartierChart_regular : IsRegularRing cartierChart := by
  let := sectionChart_regular
  exact PolynomialFieldChart.regular _ _ _
theorem cartierChart_normal : IsIntegrallyClosed cartierChart := by
  let := sectionChart_normal
  exact PolynomialFieldChart.normal _ _ _

def cartierExceptionalEquiv :
    (cartierChart ⧸ Ideal.span {cartierParameter}) ≃ₐ[ℂ] sectionChart :=
  PolynomialFieldChart.exceptionalEquiv _ _ _

lemma cartierExceptional_prime : (Ideal.span {cartierParameter}).IsPrime :=
  PolynomialFieldChart.exceptional_prime _ _ _

end ExplicitCone


open Polynomial
open scoped BigOperators
namespace GradedNormalization
variable {k L : Type*} [Field k] [CharZero k] [Field L] [Algebra k L]

def scale (a : k) : L[X] →ₐ[k] L[X] :=
  (Polynomial.aeval (Polynomial.C (algebraMap k L a) * Polynomial.X)).restrictScalars k

omit [CharZero k] in
lemma scale_monomial (a : k) (n : ℕ) (c : L) :
    scale a (monomial n c) = a ^ n • monomial n c := by
  change Polynomial.aeval _ _ = _
  rw [aeval_monomial]
  simp only [Polynomial.algebraMap_apply, mul_pow, Algebra.algebraMap_self, RingHom.id_apply,
    ← C_mul_X_pow_eq_monomial, Algebra.smul_def, map_pow]
  ring

omit [CharZero k] in
lemma scale_eq_sum (a : k) (p : L[X]) :
    scale a p = ∑ i : Fin (p.natDegree + 1), a ^ (i : ℕ) • monomial i (p.coeff i) := by
  conv_lhs => rw [p.as_sum_range]
  rw [map_sum, ← Fin.sum_univ_eq_sum_range]
  simp only [scale_monomial]

lemma monomial_mem_of_scale_mem (U : Submodule k L[X]) (p : L[X])
    (hp : ∀ a : k, scale a p ∈ U) (n : ℕ) : monomial n (p.coeff n) ∈ U := by
  by_cases hn : p.natDegree < n
  · simp [coeff_eq_zero_of_natDegree_lt hn]
  by_contra hmem
  obtain ⟨φ, hφ, hU⟩ := U.exists_le_ker_of_notMem hmem
  have hv : (fun i : Fin (p.natDegree + 1) => φ (monomial i (p.coeff i))) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero
      (f := fun i : Fin (p.natDegree + 1) => (i.val : k))
    · intro i j hij
      exact Fin.ext (Nat.cast_injective hij)
    · intro j
      have hh := hU (hp (j.val : k))
      change φ (scale (j.val : k) p) = 0 at hh
      simpa only [scale_eq_sum, map_sum, map_smul, smul_eq_mul] using hh
  exact hφ (congrFun hv ⟨n, by omega⟩)

/-- Normalization is homogeneous: scaling invariance of the input algebra
forces every homogeneous part of every integral polynomial to be integral. -/
lemma integral_monomial (B : Subalgebra k L[X])
    (hB : ∀ a : k, ∀ p ∈ B, scale a p ∈ B)
    {p : L[X]} (hp : IsIntegral B p) (n : ℕ) :
    IsIntegral B (monomial n (p.coeff n)) := by
  let N := (integralClosure B L[X]).restrictScalars k
  apply monomial_mem_of_scale_mem N.toSubmodule p _ n
  intro a
  let ψ : B →+* B :=
    ((scale a).domRestrict B).codRestrict B (fun p => hB a p p.property) |>.toRingHom
  exact hp.map_of_comp_eq ψ (scale a).toRingHom (by ext p; rfl)

end GradedNormalization


namespace GradedNormalization
open Polynomial
variable {k L : Type} [Field k] [Field L] [Algebra k L]
variable (B : Subalgebra k L[X])

def piece (n : ℕ) : Submodule k L :=
  ((integralClosure B L[X]).restrictScalars k).toSubmodule.comap
    ((Polynomial.monomial n).restrictScalars k)

lemma mem_piece (n : ℕ) (c : L) : c ∈ piece B n ↔ IsIntegral B (monomial n c) := Iff.rfl

instance gradedPiece : SetLike.GradedMonoid (piece B) where
  one_mem := by change IsIntegral B (monomial 0 1); simpa using isIntegral_one (R := B) (B := L[X])
  mul_mem := by
    intro i j x y hx hy
    change IsIntegral B (monomial (i+j) (x*y))
    rw [← monomial_mul_monomial]
    exact hx.mul hy

lemma integral_constant_of_constantCoeffs
    (hB : ∀ p ∈ B, p.coeff 0 ∈ (⊥ : Subalgebra k L)) {c : L}
    (hc : IsIntegral B (C c)) : IsIntegral k c := by
  let ψ : B →ₐ[k] (⊥ : Subalgebra k L) :=
    (((Polynomial.aeval (0 : L)).restrictScalars k).comp B.val).codRestrict ⊥
      (fun p => by
        change Polynomial.aeval (0 : L) p.val ∈ (⊥ : Subalgebra k L)
        rw [← Polynomial.coeff_zero_eq_aeval_zero]
        exact hB p p.property)
  let φ : B →+* k := ((Algebra.botEquiv k L).toAlgHom.comp ψ).toRingHom
  have hcomp : (algebraMap k L).comp φ = (Polynomial.constantCoeff).comp (algebraMap B L[X]) := by
    ext p
    change algebraMap k L ((Algebra.botEquiv k L) (ψ p)) = p.val.coeff 0
    have h := congrArg Subtype.val ((Algebra.botEquiv k L).symm_apply_apply (ψ p))
    change algebraMap k L ((Algebra.botEquiv k L) (ψ p)) =
      Polynomial.aeval (0 : L) p.val at h
    rwa [← Polynomial.coeff_zero_eq_aeval_zero] at h
  simpa using hc.map_of_comp_eq φ Polynomial.constantCoeff hcomp

lemma integral_mem_bot [IsAlgClosed k] {c : L} (hc : IsIntegral k c) :
    c ∈ (⊥ : Subalgebra k L) := by
  obtain ⟨a, ha⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := k) (K := integralClosure k L)).2 ⟨c, hc⟩
  exact ⟨a, congrArg Subtype.val ha⟩

lemma piece_zero [IsAlgClosed k]
    (hB : ∀ p ∈ B, p.coeff 0 ∈ (⊥ : Subalgebra k L)) :
    piece B 0 = LinearMap.range (Algebra.linearMap k L) := by
  ext c
  constructor
  · intro hc
    have hc' : IsIntegral B (C c) := by
      rw [mem_piece] at hc
      simpa only [monomial_zero_left] using hc
    obtain ⟨a, ha⟩ := integral_mem_bot (integral_constant_of_constantCoeffs B hB hc')
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    change IsIntegral B (monomial 0 (algebraMap k L a))
    rw [monomial_zero_left]
    have h : C (algebraMap k L a) = algebraMap B L[X] (algebraMap k B a) := by
      rw [← IsScalarTower.algebraMap_apply k B L[X]]
      rfl
    rw [h]
    exact isIntegral_algebraMap

end GradedNormalization

end

end OAI
