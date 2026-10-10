import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisQuotientLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes

namespace OAI

/-! # Exact linear coordinates for an ideal and its quotient

Pure quotient lifts have weight zero. In the adapted basis, projection
retains exactly those coordinates, and inclusion of the ideal retains
exactly the weighted ideal coordinates. This is the linear part of the
section-coordinate box comparison.
-/

noncomputable section
namespace PolycyclicRecognition

open Module

variable {V I J : Type*} [LieRing V] [LieAlgebra ℝ V]
  (U : LieIdeal ℝ V) (bI : Basis I ℝ U) (bQ : Basis J ℝ (V ⧸ U.toSubmodule))
  (lift : J → V) (hlift : ∀ j, U.toSubmodule.mkQ (lift j) = bQ j)

def quotientLinearSection : (V ⧸ U.toSubmodule) →ₗ[ℝ] V := bQ.constr ℝ lift

include hlift in
theorem quotientLinearSection_rightInverse (q : V ⧸ U.toSubmodule) :
    U.toSubmodule.mkQ (quotientLinearSection U bQ lift q) = q := by
  have he : U.toSubmodule.mkQ.comp (quotientLinearSection U bQ lift) = LinearMap.id := by
    apply bQ.ext
    intro j
    simpa only [LinearMap.comp_apply, quotientLinearSection, Basis.constr_basis,
      LinearMap.id_apply] using hlift j
  exact congrArg (fun f : (V ⧸ U.toSubmodule) →ₗ[ℝ] (V ⧸ U.toSubmodule) => f q) he

theorem quotientLinearSection_repr_inl (q : V ⧸ U.toSubmodule) (i : I) :
    (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      (quotientLinearSection U bQ lift q) (Sum.inl i) = 0 := by
  let b := basisWithQuotientLifts U.toSubmodule bI bQ lift hlift
  have he : (b.coord (Sum.inl i)).comp (quotientLinearSection U bQ lift) = 0 := by
    apply bQ.ext
    intro j
    simp only [LinearMap.comp_apply, quotientLinearSection, Basis.constr_basis,
      LinearMap.zero_apply]
    change b.repr (lift j) (Sum.inl i) = 0
    have hj : lift j = b (Sum.inr j) :=
      (basisWithQuotientLifts_inr U.toSubmodule bI bQ lift hlift j).symm
    rw [hj, Basis.repr_self]
    simp
  exact congrArg (fun f : (V ⧸ U.toSubmodule) →ₗ[ℝ] ℝ => f q) he

theorem quotientLinearSection_repr_inr (q : V ⧸ U.toSubmodule) (j : J) :
    (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift).repr
      (quotientLinearSection U bQ lift q) (Sum.inr j) = bQ.repr q j := by
  rw [basisWithQuotientLifts_repr_inr, quotientLinearSection_rightInverse U bQ lift hlift]

variable [Fintype I] [Fintype J]

/-- Inclusion of the ideal is an isometry for the weighted coordinate norms. -/
theorem ideal_scaled_coordinates_le_iff (s : I → ℝ) (r R : ℝ) (hR : 0 ≤ R) (u : U) :
    ‖(exponentialRescaleBasis
      (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
      (Sum.elim s (fun _ => 0)) r).equivFun (u : V)‖ ≤ R ↔
    ‖(exponentialRescaleBasis bI s r).equivFun u‖ ≤ R := by
  rw [pi_norm_le_iff_of_nonneg hR, pi_norm_le_iff_of_nonneg hR]
  constructor
  · intro h i
    have hi := h (Sum.inl i)
    simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
      Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inl,
      basisWithQuotientLifts_repr_inl] using hi
  · intro h k
    cases k with
    | inl i =>
      simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
        Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inl,
        basisWithQuotientLifts_repr_inl] using h i
    | inr j =>
      have hz : U.toSubmodule.mkQ (u : V) = 0 :=
        (Submodule.Quotient.mk_eq_zero U.toSubmodule).mpr u.property
      simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
        Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inr,
        basisWithQuotientLifts_repr_inr, hz, map_zero, Finsupp.zero_apply,
        smul_zero, norm_zero] using hR

/-- Projection to the quotient never enlarges the adapted coordinate bound. -/
theorem quotient_scaled_coordinates_le (s : I → ℝ) (r R : ℝ) (hR : 0 ≤ R)
    (v : V) (hv : ‖(exponentialRescaleBasis
      (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
      (Sum.elim s (fun _ => 0)) r).equivFun v‖ ≤ R) :
    ‖bQ.equivFun (U.toSubmodule.mkQ v)‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  have hj := (pi_norm_le_iff_of_nonneg hR).mp hv (Sum.inr j)
  simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
    Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inr,
    mul_zero, Real.exp_zero, inv_one, one_smul, basisWithQuotientLifts_repr_inr] using hj

/-- A quotient log ball lifts into the zero-width part of every adapted box. -/
theorem section_scaled_coordinates_le (s : I → ℝ) (r R : ℝ) (hR : 0 ≤ R)
    (q : V ⧸ U.toSubmodule) (hq : ‖bQ.equivFun q‖ ≤ R) :
    ‖(exponentialRescaleBasis
      (basisWithQuotientLifts U.toSubmodule bI bQ lift hlift)
      (Sum.elim s (fun _ => 0)) r).equivFun (quotientLinearSection U bQ lift q)‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro k
  cases k with
  | inl i =>
    simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
      Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inl,
      quotientLinearSection_repr_inl, smul_zero, norm_zero] using hR
  | inr j =>
    have hj := (pi_norm_le_iff_of_nonneg hR).mp hq j
    simpa only [Basis.equivFun_apply, exponentialRescaleBasis, Basis.repr_unitsSMul,
      Units.smul_def, Units.val_inv_eq_inv_val, Units.val_mk0, Sum.elim_inr,
      mul_zero, Real.exp_zero, inv_one, one_smul, quotientLinearSection_repr_inr] using hj

end PolycyclicRecognition

end

end OAI
