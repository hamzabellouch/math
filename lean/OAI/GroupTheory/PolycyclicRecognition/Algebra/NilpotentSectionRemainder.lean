import OAI.GroupTheory.PolycyclicRecognition.Analysis.IdealSectionBoxCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ChainProducts

namespace OAI

/-! # Polynomial bounds for the actual ideal section remainder

The remainder of an exponential after removing its pure quotient section
is computed with the finite BCH formula. Its ideal coordinates have a
polynomial bound in the original logarithm. No box comparison is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped BigOperators

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

@[simp] theorem exponentialRescaleBasis_zero {K : Type*}
    (b : Basis K ℝ V) (s : K → ℝ) : exponentialRescaleBasis b s 0 = b := by
  apply Basis.eq_of_apply_eq
  intro j
  simp [exponentialRescaleBasis, Basis.unitsSMul_apply]

/-- Removing all ideal coordinates is a contraction in the adapted norm. -/
theorem quotient_section_coordinate_norm_le (v : V) :
    ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun
      (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v))‖ ≤
    ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun v‖ := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  cases k with
  | inl i =>
    change ‖b.repr (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)) (Sum.inl i)‖ ≤ _
    rw [quotientLinearSection_repr_inl]
    simpa only [norm_zero] using norm_nonneg (b.equivFun v)
  | inr j =>
    have hh := norm_le_pi_norm (b.equivFun v) (Sum.inr j)
    change ‖b.repr v (Sum.inr j)‖ ≤ _ at hh
    change ‖b.repr (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)) (Sum.inr j)‖ ≤ _
    rw [quotientLinearSection_repr_inr]
    rwa [basisWithQuotientLifts_repr_inr] at hh

variable {N Q : Type*} [Group N] [Group Q]
  (ExpN : V → N) (ExpQ : (V ⧸ U.toSubmodule) → Q) (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)

omit [Fintype J] in
include hlift hπ hinjQ hzeroQ hneg hmul in
/-- This is the actual kernel coordinate, not a freely selected small lift. -/
theorem section_remainder_mem_ideal (v : V) :
    finiteDynkinPolynomial coeff
      ![v, -quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)] ∈ U := by
  let w := quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)
  have hproj : π (ExpN w) = π (ExpN v) := by
    rw [hπ, hπ, quotientLinearSection_rightInverse U bQ lift hlift]
  apply (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp
  apply hinjQ
  change ExpQ (U.toSubmodule.mkQ (finiteDynkinPolynomial coeff ![v, -w])) = ExpQ 0
  rw [hzeroQ, ← hπ, hmul, hneg, map_mul, map_inv]
  change π (ExpN v) * (π (ExpN w))⁻¹ = 1
  rw [hproj, mul_inv_cancel]

/-- The product constant depends on dimension, nilpotence degree, and a
uniform bracket bound, rather than on the chosen basis. -/
def sectionDynkinConstant (d c : ℕ) (C : ℝ) : ℝ :=
  (c : ℝ) * 2 ^ c * (1 + (d : ℝ) ^ 2 * C) ^ c * (3 : ℝ) ^ c

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- The same fixed polynomial controls the ideal remainder of every log. -/
theorem section_remainder_polynomial_bound (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule bI bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule bI bQ lift hlift j⁆ k| ≤ C) :
    ∀ R : ℝ, 0 ≤ R → ∀ v : V,
      ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun v‖ ≤ R →
      ∃ u : U,
        ExpN (u : V) = ExpN v *
          (ExpN (quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)))⁻¹ ∧
        ‖bI.equivFun u‖ ≤ sectionDynkinConstant (Fintype.card (I ⊕ J)) c C * (1 + R) ^ c := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  let K := sectionDynkinConstant (Fintype.card (I ⊕ J)) c C
  have hK : 0 ≤ K := by dsimp [K, sectionDynkinConstant]; positivity
  intro R hR v hv
  let w := quotientLinearSection U bQ lift (U.toSubmodule.mkQ v)
  let z := finiteDynkinPolynomial coeff ![v, -w]
  have hz : z ∈ U := section_remainder_mem_ideal U bQ lift hlift ExpN ExpQ π
    hπ hinjQ hzeroQ hneg coeff hmul v
  let u : U := ⟨z, hz⟩
  have hw : ‖b.equivFun w‖ ≤ R :=
    (quotient_section_coordinate_norm_le U bI bQ lift hlift v).trans hv
  have hvec : ∀ k : Fin 2, ‖b.equivFun (![v, -w] k)‖ ≤ R := by
    intro k
    fin_cases k
    · exact hv
    · change ‖b.equivFun (-w)‖ ≤ R
      simpa only [map_neg, norm_neg] using hw
  have hb := norm_finiteDynkinPolynomial_le b coeff hcoeff ![v, -w] hC hR hbr hvec
  have hbound : ‖b.equivFun z‖ ≤ K * (1 + R) ^ c := by
    exact hb.trans_eq (by dsimp [K, sectionDynkinConstant]; norm_num; ring)
  refine ⟨u, ?_, ?_⟩
  · change ExpN z = _
    rw [hmul, hneg]
  · have hh := (ideal_scaled_coordinates_le_iff U bI bQ lift hlift (fun _ => 0)
        0 (K * (1 + R) ^ c) (mul_nonneg hK (pow_nonneg (by linarith) _)) u).mp
    simpa only [exponentialRescaleBasis_zero] using
      hh (by simpa only [exponentialRescaleBasis_zero] using hbound)

include hπ hinjQ hzeroQ hneg hcoeff hmul in
/-- Factor a pure section followed by an arbitrary small logarithmic error.
Both new coordinates have polynomial bounds, even when the new quotient
coordinate leaves a subexponential ball. -/
theorem section_error_factorization_bound (C : ℝ) (hC : 0 ≤ C)
    (hbr : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule bI bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule bI bQ lift hlift j⁆ k| ≤ C) :
    ∀ R : ℝ, 0 ≤ R →
      ∀ (q : V ⧸ U.toSubmodule) (e : V),
        ‖bQ.equivFun q‖ ≤ R →
        ‖(basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).equivFun e‖ ≤ R →
        ∃ (u : U) (q' : V ⧸ U.toSubmodule),
          ExpN (quotientLinearSection U bQ lift q) * ExpN e =
            ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q') ∧
          ‖bI.equivFun u‖ ≤
            (sectionDynkinConstant (Fintype.card (I ⊕ J)) c C *
              (1 + sectionDynkinConstant (Fintype.card (I ⊕ J)) c C) ^ c) *
                (1 + R) ^ (c * c) := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  let K₀ := sectionDynkinConstant (Fintype.card (I ⊕ J)) c C
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀, sectionDynkinConstant]; positivity
  have hrem := section_remainder_polynomial_bound
    U bI bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ hneg coeff hcoeff hmul C hC hbr
  intro R hR q e hq he
  let v := finiteDynkinPolynomial coeff ![quotientLinearSection U bQ lift q, e]
  have hs : ‖b.equivFun (quotientLinearSection U bQ lift q)‖ ≤ R := by
    simpa only [exponentialRescaleBasis_zero] using
      section_scaled_coordinates_le U bI bQ lift hlift (fun _ => 0) 0 R hR q hq
  have hv : ‖b.equivFun v‖ ≤ K₀ * (1 + R) ^ c := by
    have hvec : ∀ k : Fin 2,
        ‖b.equivFun (![quotientLinearSection U bQ lift q, e] k)‖ ≤ R := by
      intro k
      fin_cases k
      · exact hs
      · exact he
    exact (norm_finiteDynkinPolynomial_le b coeff hcoeff _ hC hR hbr hvec).trans_eq
      (by dsimp [K₀, sectionDynkinConstant]; norm_num; ring)
  obtain ⟨u, hu, hbound⟩ := hrem (K₀ * (1 + R) ^ c)
    (mul_nonneg hK₀ (pow_nonneg (by linarith) _)) v hv
  refine ⟨u, U.toSubmodule.mkQ v, ?_, ?_⟩
  · rw [hu]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    exact (hmul _ _).symm
  · have hbase : 1 + K₀ * (1 + R) ^ c ≤ (1 + K₀) * (1 + R) ^ c := by
      have hp : 1 ≤ (1 + R) ^ c := one_le_pow₀ (by linarith)
      nlinarith
    calc
      _ ≤ K₀ * (1 + K₀ * (1 + R) ^ c) ^ c := hbound
      _ ≤ K₀ * ((1 + K₀) * (1 + R) ^ c) ^ c := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]; ring

end PolycyclicRecognition

end

end OAI
