import OAI.Geometry.EinsteinFour.JacobiScheme
import OAI.Geometry.EinsteinFour.JacobiNearZero

namespace OAI

/-! Uniform error bounds for the concrete noncommuting Jacobi recurrence. -/

namespace PositiveEinsteinFour.Jacobi

noncomputable section

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]

theorem discreteJacobi_error {R J V : ℝ → E} {t h K Lx Lv F : ℝ} {n : ℕ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hnh : (n : ℝ) * h ≤ t)
    (hK : 0 ≤ K) (hLx : 0 ≤ Lx) (hLv : 0 ≤ Lv) (hF : 0 ≤ F)
    (hJ0 : J 0 = 0) (hV0 : V 0 = 1)
    (hR : ∀ s ∈ Set.Icc 0 t, ‖R s‖ ≤ K)
    (hJ : ∀ s ∈ Set.Icc 0 t, HasDerivAt J (V s) s)
    (hV : ∀ s ∈ Set.Icc 0 t, HasDerivAt V (-(R s * J s)) s)
    (hvelocity : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
      ‖V s - V r‖ ≤ Lx * |s - r|)
    (hacceleration : ∀ s ∈ Set.Icc 0 t, ∀ r ∈ Set.Icc 0 t,
      ‖-(R s * J s) - -(R r * J r)‖ ≤ Lv * |s - r|)
    (hforce : ∀ s ∈ Set.Icc 0 t, ‖R s * J s‖ ≤ F) :
    ‖discretePosition (fun i => R (i * h)) h n - J (n * h)‖ +
      ‖discreteVelocity (fun i => R (i * h)) h n - V (n * h)‖ ≤
        (Lx + Lv + F) * n * h ^ 2 * Real.exp ((1 + 2 * K) * n * h) := by
  let A : ℕ → E := fun i => R (i * h)
  let C : ℕ → E →L[ℝ] E := fun i => ContinuousLinearMap.mul ℝ E (A i)
  have hmem (i : ℕ) (hi : i ≤ n) : (i : ℝ) * h ∈ Set.Icc 0 t := by
    constructor
    · positivity
    · exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hh).trans hnh
  apply kick_drift_global_error (R := C)
    (x := discretePosition A h) (v := discreteVelocity A h)
    (X := fun i => J (i * h)) (V := fun i => V (i * h))
    hh hh1 hK (by positivity)
  · intro i hi
    exact (ContinuousLinearMap.opNorm_mul_apply_le ℝ E (A i)).trans (hR _ (hmem i hi.le))
  · simpa using hJ0.symm
  · simpa using hV0.symm
  · intro i _
    exact discretePosition_succ A h i
  · intro i _
    exact discreteVelocity_succ A h i
  · intro i hi
    have hsub (s : ℝ) (hs : s ∈ Set.Icc (i * h) (i * h + h)) : s ∈ Set.Icc 0 t := by
      constructor
      · exact (hmem i hi.le).1.trans hs.1
      · have hs' : s ≤ ((i + 1 : ℕ) : ℝ) * h := by
          simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hs.2
        exact hs'.trans (hmem (i + 1) hi).2
    have hc := kick_drift_consistency (R := fun s => ContinuousLinearMap.mul ℝ E (R s))
      (X := J) (V := V) (a := i * h) hh hLx hLv
      (fun s hs => hJ s (hsub s hs)) (fun s hs => hV s (hsub s hs))
      (fun s hs => by
        simpa only [abs_of_nonneg (sub_nonneg.mpr hs.1)] using
          hvelocity s (hsub s hs) (i * h) (hmem i hi.le))
      (fun s hs => by
        simpa only [ContinuousLinearMap.mul_apply',
          abs_of_nonneg (sub_nonneg.mpr hs.1)] using
          hacceleration s (hsub s hs) (i * h) (hmem i hi.le))
      (hforce _ (hmem i hi.le))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hc

end

end PositiveEinsteinFour.Jacobi

end OAI
