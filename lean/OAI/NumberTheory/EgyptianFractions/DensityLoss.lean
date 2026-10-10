import OAI.NumberTheory.EgyptianFractions.BadPredecessorCount
import OAI.NumberTheory.EgyptianFractions.DescentHolder

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The bad-predecessor bound permits a polynomial loss in the lower degree;
indexed multiplicities and the actual truncated divisor fibers are retained. -/
theorem descent_bad_predecessor_divisor_count_loss
    {ι : Type*} [DecidableEq ι]
    (H Hnext E : Finset ℕ) (I : Finset ι) (X Y ρ P : ℝ)
    (res : ι → ℕ → ℕ) (N : ι → ℕ)
    (hρ : 0 < ρ) (hP : 0 < P) (hI : I.Nonempty)
    (hX : ∀ u ∈ H, (u : ℝ) ≤ X)
    (hN : ∀ i ∈ I, 0 < N i)
    (hdiv : ∀ i ∈ I, ∀ u ∈ H, u ∣ N i + res i u)
    (hinherit : ∀ u ∈ H, (u : ℝ) ≤ Y → u ∈ Hnext)
    (hleft : ∀ u ∈ H, u ∉ E → Y < (u : ℝ) →
      ρ * (I.card : ℝ) / P ≤ ((I.filter (fun i => res i u ∈ Hnext)).card : ℝ)) :
    (H.card : ℝ) ≤ (E.card : ℝ) + (Hnext.card : ℝ) +
      (P / (ρ * (I.card : ℝ))) *
        (∑ i ∈ I, ∑ h ∈ Hnext,
          (((N i + h).divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card : ℝ)) := by
  have hJ : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.mpr hI
  have h := descent_bad_predecessor_divisor_count H Hnext E I X Y (2 * ρ / P)
    res N (by positivity) hI hX hN hdiv hinherit (by
      intro u hu huE huY
      convert hleft u hu huE huY using 1
      ring)
  have hfac : 2 / ((2 * ρ / P) * (I.card : ℝ)) = P / (ρ * (I.card : ℝ)) := by
    field_simp
  simpa only [hfac] using h

/-- Moment normalization with a general loss factor. A polynomial loss can
be absorbed by the separately proved exponential coefficient estimate. -/
theorem descent_recurrence_of_pair_and_moment_loss
    (a B T X Y ρ ε E r J P : ℝ) (hX : 0 < X) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hJ : 0 < J) (hP : 0 ≤ P) (hY : Y = ρ * X)
    (hB0 : 0 ≤ B) (hBY : B ≤ Y) (hr : 1 < r)
    (hcoeff : 1 + P * Real.exp (E / r) ≤ Real.exp (2 * E))
    (hpair : a ≤ X * ε + B + (P / (ρ * J)) * T)
    (hsum : T ≤ J * (Y * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r))) :
    a / X ≤ ε + Real.exp (2 * E) * (B / Y) ^ (1 - 1 / r) := by
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hδ0 : 0 ≤ B / Y := div_nonneg hB0 hY0.le
  have hδ1 : B / Y ≤ 1 := (div_le_one hY0).mpr hBY
  have hinv : 0 ≤ 1 / r := by positivity
  have hδ : B / Y ≤ (B / Y) ^ (1 - 1 / r) :=
    Real.self_le_rpow_of_le_one hδ0 hδ1 (by linarith)
  have hρδ : ρ * (B / Y) ≤ B / Y := by nlinarith
  have hpow : 0 ≤ (B / Y) ^ (1 - 1 / r) := Real.rpow_nonneg hδ0 _
  have hbound : a ≤ X * ε + B + (P / (ρ * J)) *
      (J * (Y * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r))) := by
    exact hpair.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by positivity)))
  have hnorm : a / X ≤ ε + ρ * (B / Y) +
      P * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r) := by
    apply (div_le_iff₀ hX).mpr
    apply hbound.trans
    apply le_of_eq
    subst Y
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hcoeff hpow
  nlinarith

end Problem337

end

end OAI
