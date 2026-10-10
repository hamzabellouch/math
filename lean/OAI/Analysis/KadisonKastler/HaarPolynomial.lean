import OAI.Analysis.KadisonKastler.FreeHaar
import OAI.Analysis.KadisonKastler.HaarTail

namespace OAI

/-! # Normalization of the polynomial in a Haar unitary

Only the individual integer moments of the unitary enter these proofs.
Freeness from another algebra is unnecessary here.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

/-- The first `N` positive powers of a unitary. -/
def unitaryHaarSum (N : ℕ) (v : unitary B) : B :=
  ∑ r : Fin N, (v : B) ^ (r.val + 1)

/-- The scalar-recovery polynomial, normalized by the square root of `N`. -/
def unitaryHaarPolynomial (N : ℕ) (v : unitary B) : B :=
  (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) • unitaryHaarSum N v

theorem unitaryHaarPolynomial_eq_real_smul (N : ℕ) (v : unitary B) :
    unitaryHaarPolynomial N v = (Real.sqrt (N : ℝ))⁻¹ • unitaryHaarSum N v := by
  exact Complex.coe_smul _ _

/-- Distinct integer powers are orthogonal for the Haar trace. -/
theorem trace_haarPower_pair (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    (k l : ℤ) :
    τ.toLinearMap (star (haarPower v k) * haarPower v l) =
      if k = l then 1 else 0 := by
  rw [← haarPower_neg, ← haarPower_add]
  by_cases hkl : k = l
  · subst l
    simp [τ.map_one]
  · rw [ite_eq_right hkl]
    apply hhaar
    omega

theorem trace_unitaryHaarSum_square (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0) (N : ℕ) :
    τ.toLinearMap (star (unitaryHaarSum N v) * unitaryHaarSum N v) = (N : ℂ) := by
  classical
  have hpair (r s : Fin N) :
      τ.toLinearMap (star ((v : B) ^ (r.val + 1)) * (v : B) ^ (s.val + 1)) =
        if r = s then 1 else 0 := by
    have h := trace_haarPower_pair τ v hhaar ((r.val + 1 : ℕ) : ℤ) ((s.val + 1 : ℕ) : ℤ)
    simpa only [haarPower_natCast,
      Nat.cast_inj, Nat.add_right_cancel_iff, Fin.val_inj] using h
  simp only [unitaryHaarSum, star_sum, Finset.sum_mul, Finset.mul_sum, map_sum]
  simp_rw [hpair]
  simp

theorem trace_unitaryHaarPolynomial (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0) (N : ℕ) :
    τ.toLinearMap (unitaryHaarPolynomial N v) = 0 := by
  have hm (r : Fin N) : τ.toLinearMap ((v : B) ^ (r.val + 1)) = 0 := by
    simpa only [haarPower_natCast] using
      hhaar ((r.val + 1 : ℕ) : ℤ) (by omega)
  simp only [unitaryHaarPolynomial, unitaryHaarSum, map_smul, map_sum]
  simp_rw [hm]
  simp

/-- Unit Haar second moment of the normalized polynomial. -/
theorem trace_unitaryHaarPolynomial_square (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    {N : ℕ} (hN : 0 < N) :
    τ.toLinearMap (star (unitaryHaarPolynomial N v) * unitaryHaarPolynomial N v) = 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  simp only [unitaryHaarPolynomial, star_smul, Complex.star_def,
    Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm, smul_smul, map_smul,
    smul_eq_mul, trace_unitaryHaarSum_square τ v hhaar]
  have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have heq : (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) = 1 := by
    calc
      _ = ((Real.sqrt (N : ℝ)) ^ 2)⁻¹ * (N : ℝ) := by ring
      _ = 1 := by rw [hsq, inv_mul_cancel₀ hNr.ne']
  exact_mod_cast heq

/-- The triangle inequality gives the uniform polynomial norm bound. -/
theorem norm_unitaryHaarSum_le (N : ℕ) (v : unitary B) :
    ‖unitaryHaarSum N v‖ ≤ (N : ℝ) := by
  rcases subsingleton_or_nontrivial B with h | h
  · have hz : unitaryHaarSum N v = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]
    positivity
  · let : Nontrivial B := h
    have hr (r : Fin N) : ‖(v : B) ^ (r.val + 1)‖ = 1 := by
      change ‖((v ^ (r.val + 1) : unitary B) : B)‖ = 1
      exact CStarRing.norm_coe_unitary _
    unfold unitaryHaarSum
    calc
      _ ≤ ∑ r : Fin N, ‖(v : B) ^ (r.val + 1)‖ := norm_sum_le _ _
      _ = _ := by simp_rw [hr]; simp

theorem norm_unitaryHaarPolynomial_le_sqrt (v : unitary B) {N : ℕ} (hN : 0 < N) :
    ‖unitaryHaarPolynomial N v‖ ≤ Real.sqrt (N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs := Real.sqrt_pos.2 hNr
  rw [unitaryHaarPolynomial_eq_real_smul, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹ * (N : ℝ) :=
      mul_le_mul_of_nonneg_left (norm_unitaryHaarSum_le N v) (inv_nonneg.2 hs.le)
    _ = (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by
      rw [Real.mul_self_sqrt hNr.le]
    _ = _ := inv_mul_cancel_left₀ hs.ne' _

theorem norm_unitaryHaarPolynomial_mul_self_le (v : unitary B) {N : ℕ} (hN : 0 < N) :
    ‖unitaryHaarPolynomial N v * unitaryHaarPolynomial N v‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ‖unitaryHaarPolynomial N v‖ * ‖unitaryHaarPolynomial N v‖ := norm_mul_le _ _
    _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
      mul_le_mul (norm_unitaryHaarPolynomial_le_sqrt v hN)
        (norm_unitaryHaarPolynomial_le_sqrt v hN) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (by positivity)

theorem FreeHaarMoments.trace_unitaryHaarPolynomial_square
    {τ : FaithfulTracialState B} {A : StarSubalgebra ℂ B} {v : unitary B}
    (h : FreeHaarMoments τ A v) {N : ℕ} (hN : 0 < N) :
    τ.toLinearMap (star (unitaryHaarPolynomial N v) * unitaryHaarPolynomial N v) = 1 :=
  KadisonKastler.trace_unitaryHaarPolynomial_square τ v h.haar_moment hN

/-- Evaluation at a circle character recovers the scalar polynomial used
in the angular Haar-tail calculation. -/
theorem map_unitaryHaarPolynomial_character (φ : B →⋆ₐ[ℂ] ℂ) (N : ℕ)
    (v : unitary B) (t : ℝ) (hv : φ (v : B) = Complex.exp (Complex.I * (t : ℂ))) :
    φ (unitaryHaarPolynomial N v) = haarPolynomial N t := by
  simp only [unitaryHaarPolynomial, unitaryHaarSum, map_smul, map_sum, map_pow, hv]
  rw [haarPolynomial, haarGeometricSum, ← Fin.sum_univ_eq_sum_range]
  simp

end

end KadisonKastler

end OAI
