import OAI.Analysis.IrrationalRotation.Analysis.OrbitInvariance
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

noncomputable section
namespace Invariant233.OrbitInvariance
open WeightedShift

private abbrev shiftMap (n : ℤ) : Hilbert →L[ℂ] Hilbert :=
  (shift n).toLinearIsometry.toContinuousLinearMap

private theorem shiftMap_mul_neg (n : ℤ) :
    shiftMap n * shiftMap (-n) = 1 := by
  ext ξ k
  simp [shiftMap, shift_apply]

private def shiftUnit (n : ℤ) : (Hilbert →L[ℂ] Hilbert)ˣ where
  val := shiftMap n
  inv := shiftMap (-n)
  val_inv := shiftMap_mul_neg n
  inv_val := by simpa using shiftMap_mul_neg (-n)

theorem weighted_shift_orbit_inclusion (w : Weight) {p : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hT : (1 - p) * operator w * p = 0) (n : ℕ) :
    (1 - (shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * p *
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) *
      diagonal (orbitProduct w n) * p = 0 := by
  exact orbit_inclusion_pow hp hT n (shiftUnit n) (diagonal (orbitProduct w n))
    (operator_pow_eq_shift_diagonal w n)

theorem diagonal_smul (c : ℂ) (w : Weight) :
    diagonal (c • w) = c • diagonal w := by
  ext ξ k
  simp [diagonal_apply, mul_assoc]

theorem weighted_shift_orbit_normalized (w : Weight) {p : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hT : (1 - p) * operator w * p = 0)
    (n : ℕ) (c : ℂ) :
    (1 - (shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * p *
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) *
      diagonal (c⁻¹ • orbitProduct w n) * p = 0 := by
  rw [diagonal_smul, mul_smul_comm, smul_mul_assoc,
    weighted_shift_orbit_inclusion w hp hT n, smul_zero]

theorem weighted_shift_endpoint_identity (w r : Weight)
    {p q : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hT : (1 - p) * operator w * p = 0)
    (n : ℕ) (c : ℂ)
    (hq : q = (shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * p *
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap)
    (hr : ∀ k : ℤ, r k = orbitProduct w n k / c) :
    (1 - q) * diagonal r * p = 0 := by
  have hr' : r = c⁻¹ • orbitProduct w n := by
    ext k
    simp [hr, div_eq_mul_inv, mul_comm]
  rw [hq, hr']
  exact weighted_shift_orbit_normalized w hp hT n c

theorem endpoint_orthogonality (D : Hilbert →L[ℂ] Hilbert)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsSelfAdjoint q)
    (h : (1 - q) * D * p = 0) (ξ η : Hilbert) :
    inner ℂ (D (p ξ)) ((1 - q) η) = 0 := by
  have hq' : ((1 - q : Hilbert →L[ℂ] Hilbert) : Hilbert →ₗ[ℂ] Hilbert).IsSymmetric :=
    LinearMap.IsSymmetric.id.sub hq.isSymmetric
  have hv : (1 - q) (D (p ξ)) = 0 :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A ξ) h
  calc
    inner ℂ (D (p ξ)) ((1 - q) η) =
        inner ℂ ((1 - q) (D (p ξ))) η :=
      (hq' _ _).symm
    _ = 0 := by rw [hv, inner_zero_left]

theorem diagonal_endpoint_orthogonality (r : Weight)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsSelfAdjoint q)
    (h : (1 - q) * diagonal r * p = 0) (ξ η : Hilbert) :
    inner ℂ (diagonal r (p ξ)) ((1 - q) η) = 0 :=
  endpoint_orthogonality (diagonal r) hq h ξ η

theorem summable_endpoint_coefficients (r : Weight)
    (p q : Hilbert →L[ℂ] Hilbert) (ξ η : Hilbert) :
    Summable (fun k : ℤ => star (r k * p ξ k) * ((1 - q) η k)) := by
  simpa only [RCLike.inner_apply', diagonal_apply, starRingEnd_apply] using
    lp.summable_inner (𝕜 := ℂ) (diagonal r (p ξ)) ((1 - q) η)

theorem tsum_endpoint_coefficients_eq_zero (r : Weight)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsSelfAdjoint q)
    (h : (1 - q) * diagonal r * p = 0) (ξ η : Hilbert) :
    (∑' k : ℤ, star (r k * p ξ k) * ((1 - q) η k)) = 0 := by
  simpa only [lp.inner_eq_tsum, RCLike.inner_apply', diagonal_apply, starRingEnd_apply] using
    diagonal_endpoint_orthogonality r hq h ξ η

theorem weighted_shift_convolution_hasSum (w r : Weight)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert) :
    HasSum (fun v : ℤ =>
      (orbitProduct w n v * r v * p ξ v) * star ((1 - q) η (v + n))) 0 := by
  have hpow : (1 - q) * ((operator w)^n * diagonal r) * p = 0 := by
    simpa only [mul_assoc] using endpoint_inclusion_pow hq.isIdempotentElem hT hpair n
  have horth : inner ℂ ((1 - q) η) (((operator w)^n) (diagonal r (p ξ))) = 0 :=
    inner_eq_zero_symm.mp (endpoint_orthogonality ((operator w)^n * diagonal r)
      hq.isSelfAdjoint hpow ξ η)
  have hs := lp.hasSum_inner (𝕜 := ℂ) ((1 - q) η)
    (((operator w)^n) (diagonal r (p ξ)))
  rw [horth] at hs
  have hs' := (Equiv.addRight (n : ℤ)).hasSum_iff.mpr hs
  change HasSum (fun v : ℤ => inner ℂ (((1 - q) η) (v + n))
    ((((operator w)^n) (diagonal r (p ξ))) (v + n))) 0 at hs'
  simpa only [RCLike.inner_apply,
    starRingEnd_apply, operator_pow_apply_add, diagonal_apply,
    orbitProduct_apply, mul_assoc] using hs'

theorem cocycle_coefficients_hasSum (w r : Weight) (Fx Fy : ℤ → ℝ)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert)
    (hratio : ∀ v : ℤ, orbitProduct w n v * r v =
      (Fy (v + n) : ℂ) / (Fx v : ℂ)) :
    let A : ℤ → ℂ := fun v => p ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star ((1 - q) η (-v))
    HasSum (fun v : ℤ => A v * B (-(n : ℤ) - v)) 0 := by
  dsimp only
  apply (weighted_shift_convolution_hasSum w r hq hT hpair n ξ η).congr_fun
  intro v
  have hindex : -(-(n : ℤ) - v) = v + n := by omega
  rw [hindex, hratio v]
  simp only [div_eq_mul_inv]
  ring

theorem cocycle_coefficients_absolute_and_zero (w r : Weight) (Fx Fy : ℤ → ℝ)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert)
    (hratio : ∀ v : ℤ, orbitProduct w n v * r v =
      (Fy (v + n) : ℂ) / (Fx v : ℂ)) :
    let A : ℤ → ℂ := fun v => p ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star ((1 - q) η (-v))
    (Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖)) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  have hs := cocycle_coefficients_hasSum w r Fx Fy hq hT hpair n ξ η hratio
  exact ⟨hs.summable.norm, hs.tsum_eq⟩

end Invariant233.OrbitInvariance

end

end OAI
