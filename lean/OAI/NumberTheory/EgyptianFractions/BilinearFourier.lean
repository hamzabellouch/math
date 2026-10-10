import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The positive-sign discrete Fourier transform, convenient for residue products. -/
def residueFourier {q : ℕ} [NeZero q] (β : ZMod q → ℂ) (x : ZMod q) : ℂ :=
  ∑ y, β y * ZMod.stdAddChar (x * y)

lemma residue_character_orthogonality {q : ℕ} [NeZero q] (y z : ZMod q) :
    (∑ x : ZMod q, ZMod.stdAddChar (x * y) *
      (starRingEnd ℂ) (ZMod.stdAddChar (x * z))) =
      if y = z then (q : ℂ) else 0 := by
  simp_rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [add_neg_eq_zero, ZMod.card]
  split_ifs <;> simp

/-- Parseval's identity for the positive-sign transform on all residue classes. -/
theorem residueFourier_parseval {q : ℕ} [NeZero q] (β : ZMod q → ℂ) :
    (∑ x : ZMod q, ‖residueFourier β x‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  have hc : (∑ x : ZMod q, residueFourier β x *
      (starRingEnd ℂ) (residueFourier β x)) =
      (q : ℂ) * ∑ y : ZMod q, β y * (starRingEnd ℂ) (β y) := by
    simp only [residueFourier, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    calc
      _ = ∑ z : ZMod q, (β z * (starRingEnd ℂ) (β y)) *
          ∑ x : ZMod q, ZMod.stdAddChar (x * z) *
            (starRingEnd ℂ) (ZMod.stdAddChar (x * y)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = (q : ℂ) * (β y * (starRingEnd ℂ) (β y)) := by
        simp_rw [residue_character_orthogonality]
        simp [mul_comm]
  simpa only [Complex.mul_conj, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    ← Complex.ofReal_natCast, Complex.ofReal_inj, Complex.normSq_eq_norm_sq] using hc

/-- A unit frequency preserves the Parseval identity, also for composite moduli. -/
theorem residueFourier_parseval_unit {q : ℕ} [NeZero q]
    (β : ZMod q → ℂ) (c : (ZMod q)ˣ) :
    (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  rw [show (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) =
      ∑ x : ZMod q, ‖residueFourier β x‖ ^ 2 from
    Equiv.sum_comp c.mulLeft (fun x => ‖residueFourier β x‖ ^ 2)]
  exact residueFourier_parseval β

/-- The bilinear additive-character bound used for random prime products.
No primality hypothesis on the modulus is needed; the frequency is a unit. -/
theorem residue_bilinear_bound {q : ℕ} [NeZero q]
    (α β : ZMod q → ℂ) (c : (ZMod q)ˣ) :
    ‖∑ x : ZMod q, ∑ y : ZMod q,
      α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt (q : ℝ) * Real.sqrt (∑ x : ZMod q, ‖α x‖ ^ 2) *
        Real.sqrt (∑ y : ZMod q, ‖β y‖ ^ 2) := by
  have hsum : (∑ x : ZMod q, ∑ y : ZMod q,
      α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ x : ZMod q, α x * residueFourier β ((c : ZMod q) * x) := by
    simp only [residueFourier, Finset.mul_sum, mul_assoc]
  rw [hsum]
  calc
    _ ≤ ∑ x : ZMod q, ‖α x * residueFourier β ((c : ZMod q) * x)‖ :=
      norm_sum_le _ _
    _ = ∑ x : ZMod q, ‖α x‖ * ‖residueFourier β ((c : ZMod q) * x)‖ := by
      simp only [norm_mul]
    _ ≤ Real.sqrt (∑ x : ZMod q, ‖α x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod q, ‖residueFourier β ((c : ZMod q) * x)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [residueFourier_parseval_unit, Real.sqrt_mul (by positivity)]
      ring

/-- Equal finite sets give the classical `sqrt(q) * |H|` bilinear estimate. -/
theorem residue_bilinear_finset_bound {q : ℕ} [NeZero q]
    (H : Finset (ZMod q)) (c : (ZMod q)ˣ) :
    ‖∑ x ∈ H, ∑ y ∈ H, ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt (q : ℝ) * (H.card : ℝ) := by
  classical
  let w : ZMod q → ℂ := fun x => if x ∈ H then 1 else 0
  have hw : (∑ x : ZMod q, ‖w x‖ ^ 2) = (H.card : ℝ) := by
    simp [w, apply_ite]
  have h := residue_bilinear_bound w w c
  have hs : (∑ x : ZMod q, ∑ y : ZMod q,
      w x * w y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ x ∈ H, ∑ y ∈ H, ZMod.stdAddChar ((c : ZMod q) * x * y) := by
    simp [w, Finset.sum_ite_mem]
  rw [hs, hw] at h
  simpa only [mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg H.card)] using h

/-- A probability vector bounded by `A` has squared ℓ² norm at most `A`. -/
lemma probability_sum_sq_le {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (A : ℝ) (hα : ∀ x, 0 ≤ α x)
    (hA : ∀ x, α x ≤ A) (hsum : ∑ x, α x = 1) :
    ∑ x, α x ^ 2 ≤ A := by
  calc
    _ ≤ ∑ x, α x * A := Finset.sum_le_sum fun x _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (hA x) (hα x)
    _ = A := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The version for probability vectors used after controlling atom sizes in
random products. -/
theorem residue_bilinear_probability_bound {q : ℕ} [NeZero q]
    (α β : ZMod q → ℝ) (A B : ℝ) (c : (ZMod q)ˣ)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (hA : ∀ x, α x ≤ A) (hB : ∀ y, β y ≤ B)
    (hsα : ∑ x, α x = 1) (hsβ : ∑ y, β y = 1) :
    ‖∑ x : ZMod q, ∑ y : ZMod q,
      (α x : ℂ) * (β y : ℂ) * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt (q : ℝ) * Real.sqrt A * Real.sqrt B := by
  have h := residue_bilinear_bound (fun x => (α x : ℂ)) (fun y => (β y : ℂ)) c
  have hαnorm : (∑ x : ZMod q, ‖(α x : ℂ)‖ ^ 2) = ∑ x, α x ^ 2 := by
    apply Finset.sum_congr rfl
    intro x _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hα x)]
  have hβnorm : (∑ y : ZMod q, ‖(β y : ℂ)‖ ^ 2) = ∑ y, β y ^ 2 := by
    apply Finset.sum_congr rfl
    intro y _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hβ y)]
  rw [hαnorm, hβnorm] at h
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (probability_sum_sq_le α A hα hA hsα)) (Real.sqrt_nonneg _))
    (Real.sqrt_le_sqrt (probability_sum_sq_le β B hβ hB hsβ))
    (Real.sqrt_nonneg _) (by positivity))

end Problem337

end

end OAI
