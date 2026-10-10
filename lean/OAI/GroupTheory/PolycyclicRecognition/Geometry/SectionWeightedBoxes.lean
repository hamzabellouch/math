import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentSectionRemainder

namespace OAI

/-! # Uniform weighted-box comparison in ideal section coordinates -/

noncomputable section
namespace PolycyclicRecognition

open Module Set

theorem exponentialRescaleBasis_reindex {V I J : Type*} [LieRing V] [LieAlgebra ℝ V]
    (b : Basis I ℝ V) (cost : I → ℝ) (e : I ≃ J) (r : ℝ) :
    exponentialRescaleBasis (b.reindex e) (fun j => cost (e.symm j)) r =
      (exponentialRescaleBasis b cost r).reindex e := by
  apply Basis.eq_of_apply_eq
  intro j
  simp only [exponentialRescaleBasis, Basis.unitsSMul_apply, Basis.reindex_apply]

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V] [Fintype I] [Fintype J]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

omit [Fintype I] [Fintype J] in
/-- Only ideal coordinates are rescaled; the quotient lifts have zero width. -/
theorem basisWithQuotientLifts_rescale (cost : I → ℝ) (r : ℝ) :
    basisWithQuotientLifts U.toSubmodule (exponentialRescaleBasis bI cost r) bQ lift hlift =
      exponentialRescaleBasis (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
        (Sum.elim cost (fun _ => 0)) r := by
  apply Basis.eq_of_apply_eq
  intro k
  cases k with
  | inl i =>
    simp only [basisWithQuotientLifts_inl, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, Sum.elim_inl, SetLike.val_smul]
  | inr j =>
    simp only [basisWithQuotientLifts_inr, exponentialRescaleBasis, Basis.unitsSMul_apply,
      Units.smul_def, Units.val_mk0, Sum.elim_inr, mul_zero, Real.exp_zero, one_smul]

variable {N Q : Type*} [Group N] [Group Q]
  (ExpN : V → N) (ExpQ : (V ⧸ U.toSubmodule) → Q) (π : N →* Q)
  (hπ : ∀ v, π (ExpN v) = ExpQ (U.toSubmodule.mkQ v))
  (hinjQ : Function.Injective ExpQ) (hzeroQ : ExpQ 0 = 1)
  (hneg : ∀ v, ExpN (-v) = (ExpN v)⁻¹)
  {c : ℕ} (coeff : DynkinCoefficients c 2)
  (hcoeff : ∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c)
  (hmul : ∀ v w, ExpN (finiteDynkinPolynomial coeff ![v, w]) = ExpN v * ExpN w)
  (cost : I → ℝ) (C : ℝ) (hC : 0 ≤ C)

local notation "B" => basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
local notation "Br" => (fun r : ℝ => exponentialRescaleBasis B (Sum.elim cost (fun _ => 0)) r)
local notation "K" => sectionDynkinConstant (Fintype.card (I ⊕ J)) c C

include hπ hinjQ hzeroQ hneg hcoeff hmul hC in
/-- A full weighted box has bounded quotient logarithm and polynomially
bounded ideal coordinate, with a constant uniform in the height scale. -/
theorem weighted_section_box_factorization
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k, |(Br r).repr ⁅Br r i, Br r j⁆ k| ≤ C)
    (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R) {n : N}
    (hn : n ∈ exponentialCoordinateBox ExpN (Br r) R) :
    ∃ (u : U) (q : V ⧸ U.toSubmodule),
      n = ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∧
      ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ K * (1 + R) ^ c ∧
      ‖bQ.equivFun q‖ ≤ R := by
  obtain ⟨v, rfl, hv⟩ := hn
  have hb : ∀ i j k, |(basisWithQuotientLifts U.toSubmodule
      (exponentialRescaleBasis bI cost r) bQ lift hlift).repr
      ⁅basisWithQuotientLifts U.toSubmodule (exponentialRescaleBasis bI cost r) bQ lift hlift i,
        basisWithQuotientLifts U.toSubmodule (exponentialRescaleBasis bI cost r) bQ lift hlift j⁆ k| ≤ C := by
    simpa only [basisWithQuotientLifts_rescale] using hbr r hr
  obtain ⟨u, hu, hbound⟩ := section_remainder_polynomial_bound U
    (exponentialRescaleBasis bI cost r) bQ lift hlift ExpN ExpQ π hπ hinjQ hzeroQ
    hneg coeff hcoeff hmul C hC hb R hR v
    (by simpa only [basisWithQuotientLifts_rescale] using hv)
  refine ⟨u, U.toSubmodule.mkQ v, ?_, hbound, ?_⟩
  · rw [hu]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  · exact quotient_scaled_coordinates_le U bI bQ lift hlift cost r R hR v hv

include hcoeff hmul hC in
/-- Conversely, the product of a weighted ideal box and a bounded pure
quotient section lies in the full box with one uniform polynomial loss. -/
theorem weighted_section_box_product
    (hbr : ∀ r : ℝ, 0 ≤ r → ∀ i j k, |(Br r).repr ⁅Br r i, Br r j⁆ k| ≤ C)
    (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (u : U) (q : V ⧸ U.toSubmodule)
    (hu : ‖(exponentialRescaleBasis bI cost r).equivFun u‖ ≤ R)
    (hq : ‖bQ.equivFun q‖ ≤ R) :
    ExpN (u : V) * ExpN (quotientLinearSection U bQ lift q) ∈
      exponentialCoordinateBox ExpN (Br r) (K * (1 + R) ^ c) := by
  let v := finiteDynkinPolynomial coeff ![(u : V), quotientLinearSection U bQ lift q]
  refine ⟨v, hmul _ _, ?_⟩
  have hi := (ideal_scaled_coordinates_le_iff U bI bQ lift hlift cost r R hR u).mpr hu
  have hs := section_scaled_coordinates_le U bI bQ lift hlift cost r R hR q hq
  have hvec : ∀ k : Fin 2,
      ‖(Br r).equivFun (![(u : V), quotientLinearSection U bQ lift q] k)‖ ≤ R := by
    intro k
    fin_cases k
    · exact hi
    · exact hs
  exact (norm_finiteDynkinPolynomial_le (Br r) coeff hcoeff _ hC hR (hbr r hr) hvec).trans_eq
    (by dsimp [sectionDynkinConstant]; norm_num; ring)

end PolycyclicRecognition

end

end OAI
