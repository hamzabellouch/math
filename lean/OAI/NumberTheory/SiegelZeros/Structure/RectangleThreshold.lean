import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Intersection.TorusEvalOne
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.NormalizationPresentationLocalEquiv

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets.Geometry

noncomputable def rectangleThreshold (H N : ℝ) (j : Fin 3) : ℝ :=
  32 * H ^ (if j = 0 then (2 / 3 : ℝ) else (-1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)

lemma rectangleThreshold_pos {H N : ℝ} (hH : 0 < H) (hN : 0 < N) (j : Fin 3) :
    0 < rectangleThreshold H N j := by
  unfold rectangleThreshold
  positivity

lemma short_side_lower {H N : ℝ} (hH : 0 < H) (hHN : H ≤ N) :
    N ≤ H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
  have hN : 0 < N := lt_of_lt_of_le hH hHN
  have hp : N ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hN]
    norm_num
  calc
    N = N ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := hp.symm
    _ ≤ H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hH hHN (by norm_num : (-1 / 3 : ℝ) ≤ 0))
        (Real.rpow_nonneg hN.le _)

lemma short_side_le_threshold {H N : ℝ} (hH : 1 ≤ H) (hN : 0 ≤ N) (j : Fin 3) :
    8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) ≤ rectangleThreshold H N j / 4 := by
  have he : H ^ (-1 / 3 : ℝ) ≤
      H ^ (if j = 0 then (2 / 3 : ℝ) else (-1 / 3 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hH
    split_ifs <;> norm_num
  have hm := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hN (4 / 3 : ℝ))
  unfold rectangleThreshold
  linarith

theorem rectangle_floor_product_gt_short_power {H N : ℝ} (hH : 1 ≤ H) (hN : 0 < N)
    (I : Finset (Fin 3)) (hI : I.Nonempty) :
    (8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ)) ^ I.card <
      ∏ j ∈ I, ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1) := by
  have hp := Finset.prod_lt_prod_of_nonempty₀
    (s := I) (f := fun _ ↦ 8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ))
    (g := fun j ↦ ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1))
    (fun _ _ ↦ by have : 0 < H := lt_of_lt_of_le zero_lt_one hH; positivity)
    (fun j _ ↦ (short_side_le_threshold hH hN.le j).trans_lt (Nat.lt_floor_add_one _)) hI
  simpa using hp

lemma rectangleThreshold_product {H N : ℝ} (hH : 0 < H) (hN : 0 < N) :
    (∏ j : Fin 3, rectangleThreshold H N j / 4) = 8 ^ 3 * N ^ 4 := by
  have hhp : H ^ (2 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hH, ← Real.rpow_add hH]
    norm_num
  have hnp : (N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
    rw [← Real.rpow_mul_natCast hN.le]
    norm_num
  rw [Fin.prod_univ_three]
  simp only [rectangleThreshold, ↓reduceIte, Fin.isValue, one_ne_zero, show (2 : Fin 3) ≠ 0 by decide]
  calc
    _ = 8 ^ 3 * (H ^ (2 / 3 : ℝ) * H ^ (-1 / 3 : ℝ) * H ^ (-1 / 3 : ℝ)) *
        (N ^ (4 / 3 : ℝ)) ^ 3 := by ring
    _ = 8 ^ 3 * N ^ 4 := by rw [hhp, hnp]; ring

theorem rectangle_floor_product_gt {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    {h : ℕ} (hh : 1 ≤ h) (hh4 : h ≤ 4) (I : Finset (Fin 3))
    (hI : I.card = min h 3) :
    (4 * N) ^ h < ∏ j ∈ I, ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1) := by
  have hHp : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hNp : 0 < N := lt_of_lt_of_le hHp hHN
  have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hh3 : h ≤ 3
  · have hIc : I.card = h := by omega
    have hprod : (8 * N) ^ h <
        ∏ j ∈ I, ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1) := by
      have hp := rectangle_floor_product_gt_short_power hH hNp I hIne
      rw [hIc] at hp
      have hs : 8 * N ≤ 8 * H ^ (-1 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
        have := short_side_lower hHp hHN
        linarith
      exact (pow_le_pow_left₀ (by positivity) hs h).trans_lt hp
    exact (pow_lt_pow_left₀ (by nlinarith : 4 * N < 8 * N) (by positivity)
      (by omega : h ≠ 0)).trans hprod
  · have heq : h = 4 := by omega
    subst h
    have hIu : I = Finset.univ := I.eq_univ_of_card (by simpa using hI)
    subst I
    have hp := Finset.prod_lt_prod_of_nonempty₀
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun j ↦ rectangleThreshold H N j / 4)
      (g := fun j ↦ ((⌊rectangleThreshold H N j / 4⌋₊ : ℝ) + 1))
      (fun j _ ↦ div_pos (rectangleThreshold_pos hHp hNp j) (by norm_num))
      (fun _ _ ↦ Nat.lt_floor_add_one _) (by simp)
    rw [rectangleThreshold_product hHp hNp] at hp
    have hn4 : 0 < N ^ 4 := pow_pos hNp _
    nlinarith

theorem rectangle_floor_product_gt_nat {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    {h : ℕ} (hh : 1 ≤ h) (hh4 : h ≤ 4) (I : Finset (Fin 3))
    (hI : I.card = min h 3) :
    (4 * N) ^ h < ∏ j ∈ I, (⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1) := by
  have hp := rectangle_floor_product_gt
    (H := (H : ℝ)) (N := (N : ℝ)) (by exact_mod_cast hH) (by exact_mod_cast hHN)
    hh hh4 I hI
  exact_mod_cast hp

theorem rectangle_jet_cutoff {H N : ℝ} (hH : 0 < H) (hN : 0 < N)
    (j : Fin 3) {a b : ℕ} (hb : b ≤ 4)
    (ha : a ≤ b * ⌊rectangleThreshold H N j / 4⌋₊) :
    (a : ℝ) ≤ rectangleThreshold H N j := by
  have ht := rectangleThreshold_pos hH hN j
  have hf := Nat.floor_le (le_of_lt (div_pos ht (by norm_num : (0 : ℝ) < 4)))
  have hab : (a : ℝ) ≤ 4 * (⌊rectangleThreshold H N j / 4⌋₊ : ℝ) := by
    exact_mod_cast ha.trans (Nat.mul_le_mul_right _ hb)
  linarith

theorem rectangle_cutoff_lower {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) (j : Fin 3) :
    8 * N + 1 ≤ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1 := by
  apply Nat.succ_le_succ
  apply Nat.le_floor
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNr : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hs := short_side_lower (lt_of_lt_of_le zero_lt_one hHr) hHNr
  have ht := short_side_le_threshold hHr (Nat.cast_nonneg N) j
  push_cast
  linarith

theorem rectangle_cutoff_ge_nine {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N) (j : Fin 3) :
    9 ≤ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊ + 1 := by
  have := rectangle_cutoff_lower hH hHN j
  have hN : 1 ≤ N := hH.trans hHN
  omega




variable {K : Type*} [Field K]

local notation "PolyRing" => MvPolynomial (Fin 4) K
local notation "torusCoordinateProduct" => (∏ i : Fin 4, (MvPolynomial.X i : PolyRing))
local notation "TorusCoordRing" => Localization.Away torusCoordinateProduct

theorem torus_mixed_derivatives_algebraMap (c : Fin 3 → Fin 4 → K)
    (a : Fin 3 → ℕ) (F : PolyRing) :
    ((localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
      (invariantDerivation (c 0))).toLinearMap ^ a 0)
      (((localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
        (invariantDerivation (c 1))).toLinearMap ^ a 1)
        (((localizeDerivation (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
          (invariantDerivation (c 2))).toLinearMap ^ a 2) (algebraMap PolyRing TorusCoordRing F))) =
      algebraMap PolyRing TorusCoordRing (invariantJet c a F) := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe, invariantJet] using
    mixed_localizeDerivation_algebraMap (T := TorusCoordRing) (Submonoid.powers torusCoordinateProduct)
      (fun j ↦ invariantDerivation (c j)) a F

theorem torus_rectangleJetIdeal_le_identity {H N : ℕ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (c : Fin 3 → Fin 4 → K) (F : PolyRing)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1) (invariantJet c a F) = 0)
    {b : ℕ} (hb : b ≤ 4) :
    rectangleJetIdeal (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F))
      (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊) b ≤
        (torusIdentityPoint (K := K)).asIdeal := by
  change _ ≤ RingHom.ker (torusEvalOne (K := K))
  apply rectangleJetIdeal_le_ker
    (fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F))
    (fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊)
    (torusEvalOne (K := K)) hb
  intro a ha
  rw [torusEvalOne_algebraMap]
  apply hvanish a
  intro j
  exact rectangle_jet_cutoff
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hH))
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hH.trans hHN)))
    j le_rfl (ha j)

theorem torus_rectangle_has_shared_minimal_prime {H N : ℕ}
    (hH : 1 ≤ H) (hHN : H ≤ N) (c : Fin 3 → Fin 4 → K) (F : PolyRing) (hF : F ≠ 0)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1) (invariantJet c a F) = 0) :
    let jet := fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)
    let t := fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊
    ∃ b ≤ 3, ∃ q : Ideal TorusCoordRing, q ≤ (torusIdentityPoint (K := K)).asIdeal ∧
      (rectangleJetIdeal jet t b).IsMinimalPrime q ∧
      (rectangleJetIdeal jet t (b + 1)).IsMinimalPrime q := by
  have hu : torusCoordinateProduct ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ MvPolynomial.X_ne_zero i
  let : IsDomain TorusCoordRing := IsLocalization.isDomain_of_le_nonZeroDivisors TorusCoordRing
    (powers_le_nonZeroDivisors_of_noZeroDivisors hu)
  apply rectangleJets_have_shared_minimal_prime _ _ (torusIdentityPoint (K := K))
  · exact torus_rectangleJetIdeal_le_identity hH hHN c F hvanish le_rfl
  · simpa only [invariantJet, Pi.zero_apply, Function.iterate_zero, id_eq] using
      (torus_polynomial_ne_zero hF)
  · exact four_variable_localization_ringKrullDim_le (Submonoid.powers torusCoordinateProduct)

theorem torus_rectangle_shared_component_data {H N : ℕ}
    (hH : 1 ≤ H) (hHN : H ≤ N) (c : Fin 3 → Fin 4 → K)
    (F : PolyRing) (hF : F ≠ 0)
    (hvanish : ∀ a : Fin 3 → ℕ,
      (∀ j, (a j : ℝ) ≤ rectangleThreshold (H : ℝ) (N : ℝ) j) →
        MvPolynomial.eval (fun _ ↦ 1) (invariantJet c a F) = 0) :
    let jet := fun a ↦ algebraMap PolyRing TorusCoordRing (invariantJet c a F)
    let t := fun j ↦ ⌊rectangleThreshold (H : ℝ) (N : ℝ) j / 4⌋₊
    ∃ b ≤ 3, ∃ q : PrimeSpectrum TorusCoordRing,
      q.asIdeal ≤ (torusIdentityPoint (K := K)).asIdeal ∧
      (rectangleJetIdeal jet t b).IsMinimalPrime q.asIdeal ∧
      (rectangleJetIdeal jet t (b + 1)).IsMinimalPrime q.asIdeal ∧
      1 ≤ Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
        (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ∧
      Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
        (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ≤ 4 := by
  obtain ⟨b, hb, q, hqp, hqb, hqb'⟩ :=
    torus_rectangle_has_shared_minimal_prime hH hHN c F hF hvanish
  have : q.IsPrime := hqb.isPrime
  have hmem : algebraMap PolyRing TorusCoordRing F ∈ q := by
    apply hqb.le
    apply rectangleJetIdeal_mono _ _ (Nat.zero_le b)
    rw [rectangleJetIdeal_zero]
    apply Ideal.subset_span
    simp only [Set.mem_singleton_iff, invariantJet, Pi.zero_apply, Function.iterate_zero, id_eq]
  exact ⟨b, hb, ⟨q, hqb.isPrime⟩, hqp, hqb, hqb',
    localization_component_cotangent_bounds (Submonoid.powers torusCoordinateProduct) q hF hmem⟩


end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def coefficientDerivationLinear (σ : Type*) (D : Derivation ℚ A A) :
    MvPolynomial σ A →ₗ[ℚ] MvPolynomial σ A :=
  (AddMonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap D.toLinearMap ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

theorem coefficientDerivationLinear_monomial (σ : Type*) (D : Derivation ℚ A A)
    (d : σ →₀ ℕ) (a : A) :
    coefficientDerivationLinear σ D (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d (D a) := by
  classical
  ext e
  change D ((MvPolynomial.monomial d a).coeff e) =
    (MvPolynomial.monomial d (D a)).coeff e
  simp [MvPolynomial.coeff_monomial, apply_ite D]

def coefficientDerivation (σ : Type*) (D : Derivation ℚ A A) :
    Derivation ℚ (MvPolynomial σ A) (MvPolynomial σ A) where
  toLinearMap := coefficientDerivationLinear σ D
  map_one_eq_zero' := by
    rw [MvPolynomial.one_def, coefficientDerivationLinear_monomial]
    simp
  leibniz' p q := by
    induction p using MvPolynomial.induction_on' with
    | add p r hp hr =>
        simp only [add_mul, map_add, hp, hr, smul_eq_mul]
        ring
    | monomial d a =>
        induction q using MvPolynomial.induction_on' with
        | add q r hq hr =>
            simp only [mul_add, map_add, hq, hr, smul_eq_mul]
            ring
        | monomial e b =>
            simp only [MvPolynomial.monomial_mul_monomial,
              coefficientDerivationLinear_monomial, Derivation.leibniz, smul_eq_mul,
              map_add, add_comm e d]

@[simp] theorem coefficientDerivation_coeff (σ : Type*) (D : Derivation ℚ A A)
    (p : MvPolynomial σ A) (d : σ →₀ ℕ) :
    (coefficientDerivation σ D p).coeff d = D (p.coeff d) := rfl

@[simp] theorem coefficientDerivation_monomial (σ : Type*) (D : Derivation ℚ A A)
    (d : σ →₀ ℕ) (a : A) :
    coefficientDerivation σ D (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d (D a) :=
  coefficientDerivationLinear_monomial σ D d a

@[simp] theorem coefficientDerivation_C (σ : Type*) (D : Derivation ℚ A A) (a : A) :
    coefficientDerivation σ D (MvPolynomial.C a) = MvPolynomial.C (D a) :=
  coefficientDerivation_monomial σ D 0 a

@[simp] theorem coefficientDerivation_X (σ : Type*) (D : Derivation ℚ A A) (i : σ) :
    coefficientDerivation σ D (MvPolynomial.X i) = 0 := by
  simp [MvPolynomial.X]

theorem derivation_mem_span_of_vanishes (D : Derivation ℚ A A) (s : Set A)
    (h : ∀ a ∈ s, D a = 0) {a : A} (ha : a ∈ Ideal.span s) :
    D a ∈ Ideal.span s := by
  induction ha using Submodule.span_induction with
  | mem a ha => simp [h a ha]
  | zero => simp
  | add a b ha hb hda hdb => simpa using (Ideal.span s).add_mem hda hdb
  | smul r a ha hda =>
      simpa only [Derivation.leibniz, smul_eq_mul] using
        (Ideal.span s).add_mem ((Ideal.span s).mul_mem_left r hda)
          ((Ideal.span s).mul_mem_right (D r) ha)

def quotientDerivation (D : Derivation ℚ A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) : Derivation ℚ (A ⧸ I) (A ⧸ I) :=
  Derivation.liftOfSurjective (f := Ideal.Quotient.mkₐ ℚ I)
    (Ideal.Quotient.mkₐ_surjective ℚ I)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (hI a (Ideal.Quotient.eq_zero_iff_mem.mp ha)))

@[simp] theorem quotientDerivation_mk (D : Derivation ℚ A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) (a : A) :
    quotientDerivation D I hI (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I (D a) := by
  unfold quotientDerivation
  apply Derivation.liftOfSurjective_apply

theorem quotientDerivation_pow_mk (D : Derivation ℚ A A) (I : Ideal A)
    (hI : ∀ a ∈ I, D a ∈ I) (n : ℕ) (a : A) :
    ((quotientDerivation D I hI).toLinearMap ^ n) (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk I ((D.toLinearMap ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, Derivation.coeFn_coe,
        quotientDerivation_mk]

theorem coefficientDerivation_pow_monomial (σ : Type*) (D : Derivation ℚ A A)
    (n : ℕ) (d : σ →₀ ℕ) (a : A) :
    ((coefficientDerivation σ D).toLinearMap ^ n) (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d ((D.toLinearMap ^ n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, Derivation.coeFn_coe,
        coefficientDerivation_monomial]

theorem coefficientDerivation_mem_rectangularIdeal (σ : Type*)
    (k : σ → ℕ) (D : Derivation ℚ A A) {p : MvPolynomial σ A}
    (hp : p ∈ rectangularIdeal k) :
    coefficientDerivation σ D p ∈ rectangularIdeal k := by
  apply derivation_mem_span_of_vanishes _ _ _ hp
  rintro _ ⟨i, rfl⟩
  simp

def rectangularCoefficientDerivation (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) :
    Derivation ℚ (MvPolynomial σ A ⧸ rectangularIdeal k)
      (MvPolynomial σ A ⧸ rectangularIdeal k) :=
  quotientDerivation (coefficientDerivation σ D) (rectangularIdeal k)
    (fun _ hp => coefficientDerivation_mem_rectangularIdeal σ k D hp)

@[simp] theorem rectangularCoefficientDerivation_mk (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (p : MvPolynomial σ A) :
    rectangularCoefficientDerivation σ k D (Ideal.Quotient.mk (rectangularIdeal k) p) =
      Ideal.Quotient.mk (rectangularIdeal k) (coefficientDerivation σ D p) :=
  quotientDerivation_mk _ _ _ p

theorem rectangularCoefficientDerivation_X (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) :
    rectangularCoefficientDerivation σ k D
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i)) = 0 := by
  simp

theorem rectangularCoefficientDerivation_pow_monomial (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (n : ℕ) (d : σ →₀ ℕ) (a : A) :
    ((rectangularCoefficientDerivation σ k D).toLinearMap ^ n)
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d a)) =
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial d ((D.toLinearMap ^ n) a)) := by
  rw [rectangularCoefficientDerivation, quotientDerivation_pow_mk,
    coefficientDerivation_pow_monomial]

theorem rectangularVariable_pow_eq_zero {σ R : Type*} [CommRing R]
    (k : σ → ℕ) (i : σ) :
    (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i : MvPolynomial σ R)) ^ k i =
      0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

variable {σ R S : Type*} [CommRing R] [CommRing S]

def rectangularMap (k : σ → ℕ) (f : R →+* S) :
    (MvPolynomial σ R ⧸ rectangularIdeal k) →+*
      (MvPolynomial σ S ⧸ rectangularIdeal k) := by
  let g := (Ideal.Quotient.mk (rectangularIdeal k)).comp (MvPolynomial.map f)
  apply Ideal.Quotient.lift (rectangularIdeal k) g
  have hg : rectangularIdeal k ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change g ((MvPolynomial.X i) ^ k i) = 0
    simp only [g, RingHom.comp_apply, map_pow, MvPolynomial.map_X]
    exact rectangularVariable_pow_eq_zero k i
  exact fun p hp => hg hp

@[simp] theorem rectangularMap_mk (k : σ → ℕ) (f : R →+* S) (p : MvPolynomial σ R) :
    rectangularMap k f (Ideal.Quotient.mk (rectangularIdeal k) p) =
      Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.map f p) := rfl

theorem rectangularMap_monomial (k : σ → ℕ) (f : R →+* S)
    (d : σ →₀ ℕ) (a : R) :
    rectangularMap k f (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d a)) =
      Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d (f a)) := by
  simp

end



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def nilpotentDerivationExp (D : Derivation ℚ A A)
    (hD : IsNilpotent D.toLinearMap) : A →ₐ[ℚ] A where
  toFun := fun a => (IsNilpotent.exp D.toLinearMap : Module.End ℚ A) a
  map_zero' := (IsNilpotent.exp D.toLinearMap : Module.End ℚ A).map_zero
  map_add' := (IsNilpotent.exp D.toLinearMap : Module.End ℚ A).map_add
  map_one' := by
    simpa using IsNilpotent.exp_smul_eq_sum (a := D.toLinearMap) (m := (1 : A))
      (k := 1) (by simp) hD
  map_mul' := Module.End.exp_mul_of_derivation ℚ A D.toLinearMap
    (fun x y => by simp [smul_eq_mul, mul_comm]) hD
  commutes' r := by
    have hone : IsNilpotent.exp D.toLinearMap (1 : A) = 1 := by
      simpa using IsNilpotent.exp_smul_eq_sum (a := D.toLinearMap) (m := (1 : A))
        (k := 1) (by simp) hD
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hone]

theorem nilpotentDerivationExp_apply (D : Derivation ℚ A A)
    {n : ℕ} (hD : D.toLinearMap ^ n = 0) (a : A) :
    nilpotentDerivationExp D ⟨n, hD⟩ a =
      ∑ i ∈ Finset.range n, (i.factorial : ℚ)⁻¹ • ((D.toLinearMap ^ i) a) := by
  simp [nilpotentDerivationExp, IsNilpotent.exp_eq_sum hD]

theorem scaledDerivation_pow_apply (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) (n : ℕ) (a : A) :
    ((u • D).toLinearMap ^ n) a = u ^ n * (D.toLinearMap ^ n) a := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, Derivation.coeFn_coe,
        Derivation.smul_apply, smul_eq_mul, ih, Derivation.leibniz,
        Derivation.leibniz_pow, hu, smul_zero, mul_zero, add_zero]
      ring

theorem scaledDerivation_pow_eq_zero (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) {n : ℕ} (hn : u ^ n = 0) :
    (u • D).toLinearMap ^ n = 0 := by
  ext a
  change ((u • D).toLinearMap ^ n) a = 0
  rw [scaledDerivation_pow_apply D u hu, hn, zero_mul]

def truncatedTaylor (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) {n : ℕ} (hn : u ^ n = 0) : A →ₐ[ℚ] A :=
  nilpotentDerivationExp (u • D) ⟨n, scaledDerivation_pow_eq_zero D u hu hn⟩

theorem truncatedTaylor_apply (D : Derivation ℚ A A) (u : A)
    (hu : D u = 0) {n : ℕ} (hn : u ^ n = 0) (a : A) :
    truncatedTaylor D u hu hn a =
      ∑ i ∈ Finset.range n, (i.factorial : ℚ)⁻¹ • (u ^ i * (D.toLinearMap ^ i) a) := by
  rw [truncatedTaylor, nilpotentDerivationExp_apply (u • D)
    (scaledDerivation_pow_eq_zero D u hu hn)]
  simp only [scaledDerivation_pow_apply D u hu]

theorem map_truncatedTaylor {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →+* B) (D : Derivation ℚ A A) (u : A) (hu : D u = 0)
    {n : ℕ} (hn : u ^ n = 0) (hnpos : 0 < n) (hfu : f u = 0) (a : A) :
    f (truncatedTaylor D u hu hn a) = f a := by
  rw [truncatedTaylor_apply]
  simp only [map_sum, map_rat_smul, map_mul, map_pow, hfu]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    simp [zero_pow hb0]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hnpos))

end



noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

def rectangularTaylorAlong (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) :
    (MvPolynomial σ A ⧸ rectangularIdeal k) →ₐ[ℚ]
      (MvPolynomial σ A ⧸ rectangularIdeal k) :=
  truncatedTaylor (rectangularCoefficientDerivation σ k D)
    (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i))
    (rectangularCoefficientDerivation_X σ k D i)
    (rectangularVariable_pow_eq_zero k i)

theorem rectangularTaylorAlong_monomial (σ : Type*) (k : σ → ℕ)
    (D : Derivation ℚ A A) (i : σ) (d : σ →₀ ℕ) (a : A) :
    rectangularTaylorAlong σ k D i
      (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.monomial d a)) =
      ∑ n ∈ Finset.range (k i), (n.factorial : ℚ)⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.single i n + d) ((D.toLinearMap ^ n) a)) := by
  rw [rectangularTaylorAlong, truncatedTaylor_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [rectangularCoefficientDerivation_pow_monomial,
    ← map_pow, ← map_mul, ← MvPolynomial.monomial_single_add]

@[simp] theorem rectangularCoefficientDerivation_zero (σ : Type*) (k : σ → ℕ) :
    rectangularCoefficientDerivation σ k (0 : Derivation ℚ A A) = 0 := by
  apply Derivation.ext
  intro p
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
  rw [rectangularCoefficientDerivation_mk]
  have hp : coefficientDerivation σ (0 : Derivation ℚ A A) p = 0 := by
    ext d
    simp
  simp [hp]

@[simp] theorem rectangularTaylorAlong_zero (σ : Type*) (k : σ → ℕ) (i : σ) :
    rectangularTaylorAlong σ k (0 : Derivation ℚ A A) i = AlgHom.id ℚ _ := by
  ext p
  simp [rectangularTaylorAlong, truncatedTaylor, nilpotentDerivationExp]

def rectangularTaylorThree {B : Type*} [CommRing B] (σ : Type*) (k : σ → ℕ)
    (D₁ D₂ D₃ : Derivation ℚ A A) (i₁ i₂ i₃ : σ) (f : A →+* B) :
    A →+* (MvPolynomial σ B ⧸ rectangularIdeal k) :=
  (rectangularMap k f).comp
    ((rectangularTaylorAlong σ k D₁ i₁).toRingHom.comp
      ((rectangularTaylorAlong σ k D₂ i₂).toRingHom.comp
        ((rectangularTaylorAlong σ k D₃ i₃).toRingHom.comp
          ((Ideal.Quotient.mk (rectangularIdeal k)).comp MvPolynomial.C))))

theorem rectangularTaylorThree_apply {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (D₁ D₂ D₃ : Derivation ℚ A A)
    (i₁ i₂ i₃ : σ) (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a =
      ∑ n₃ ∈ Finset.range (k i₃), ∑ n₂ ∈ Finset.range (k i₂),
        ∑ n₁ ∈ Finset.range (k i₁),
          (((n₃.factorial : ℚ)⁻¹ * (n₂.factorial : ℚ)⁻¹) * (n₁.factorial : ℚ)⁻¹) •
            Ideal.Quotient.mk (rectangularIdeal k)
              (MvPolynomial.monomial
                (Finsupp.single i₁ n₁ + (Finsupp.single i₂ n₂ + Finsupp.single i₃ n₃))
                (f ((D₁.toLinearMap ^ n₁) ((D₂.toLinearMap ^ n₂) ((D₃.toLinearMap ^ n₃) a))))) := by
  simp only [rectangularTaylorThree, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, MvPolynomial.C_apply]
  simp only [rectangularTaylorAlong_monomial, map_sum, map_rat_smul,
    rectangularMap_monomial, Finset.smul_sum, smul_smul, add_zero, mul_assoc]

theorem rectangularTaylorThree_two_apply {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (D₁ D₂ : Derivation ℚ A A)
    (i₁ i₂ : σ) (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D₁ D₂ 0 i₁ i₂ i₂ f a =
      ∑ n₂ ∈ Finset.range (k i₂), ∑ n₁ ∈ Finset.range (k i₁),
        ((n₂.factorial : ℚ)⁻¹ * (n₁.factorial : ℚ)⁻¹) •
          Ideal.Quotient.mk (rectangularIdeal k)
            (MvPolynomial.monomial (Finsupp.single i₁ n₁ + Finsupp.single i₂ n₂)
              (f ((D₁.toLinearMap ^ n₁) ((D₂.toLinearMap ^ n₂) a)))) := by
  simp only [rectangularTaylorThree, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, rectangularTaylorAlong_zero, AlgHom.id_apply, MvPolynomial.C_apply]
  simp only [rectangularTaylorAlong_monomial, map_sum, map_rat_smul,
    rectangularMap_monomial, Finset.smul_sum, smul_smul, add_zero]

theorem rectangularTaylorThree_one_apply {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (D : Derivation ℚ A A) (i : σ)
    (f : A →+* B) (a : A) :
    rectangularTaylorThree σ k D 0 0 i i i f a =
      ∑ n ∈ Finset.range (k i), (n.factorial : ℚ)⁻¹ •
        Ideal.Quotient.mk (rectangularIdeal k)
          (MvPolynomial.monomial (Finsupp.single i n) (f ((D.toLinearMap ^ n) a))) := by
  simp only [rectangularTaylorThree, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, rectangularTaylorAlong_zero, AlgHom.id_apply, MvPolynomial.C_apply]
  simp only [rectangularTaylorAlong_monomial, map_sum, map_rat_smul,
    rectangularMap_monomial, add_zero]

theorem rectangularTaylorThree_residue {B : Type*} [CommRing B] [Algebra ℚ B]
    (σ : Type*) (k : σ → ℕ) (hk : ∀ i, k i ≠ 0)
    (D₁ D₂ D₃ : Derivation ℚ A A) (i₁ i₂ i₃ : σ) (f : A →+* B)
    (ε : (MvPolynomial σ B ⧸ rectangularIdeal k) →+* B)
    (hε : ∀ p, ε (Ideal.Quotient.mk (rectangularIdeal k) p) = MvPolynomial.constantCoeff p)
    (a : A) :
    ε (rectangularTaylorThree σ k D₁ D₂ D₃ i₁ i₂ i₃ f a) = f a := by
  let g := ε.comp (rectangularMap k f)
  have hg (i : σ) : g (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.X i)) = 0 := by
    simp [g, hε]
  have hstep (D : Derivation ℚ A A) (i : σ) (p) :
      g (rectangularTaylorAlong σ k D i p) = g p := by
    apply map_truncatedTaylor g _ _ _ _ (Nat.pos_of_ne_zero (hk i)) (hg i)
  change g (rectangularTaylorAlong σ k D₁ i₁
    (rectangularTaylorAlong σ k D₂ i₂
      (rectangularTaylorAlong σ k D₃ i₃
        (Ideal.Quotient.mk (rectangularIdeal k) (MvPolynomial.C a))))) = f a
  rw [hstep, hstep, hstep]
  simp [g, hε]

end

end WeightedTorusJets.Geometry


end SiegelZeros

end OAI
