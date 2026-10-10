import OAI.GroupTheory.Thompson.HilbertAverage
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Displacement forces a lower bound for the finite mean energy

The recursive identities concern the individual vectors, not the image of
their mean under the Lipschitz map. Squared-norm convexity is applied to the
mean of the differences of the images.
-/

open scoped BigOperators

universe uE

namespace ThompsonNonamenability

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The pointwise inequality obtained from the actual recursive colors. -/
theorem displacement_le_mean_energy {D : ℕ} (hD : 0 < D)
    (f : UnitBall E → UnitBall E) (L δ : ℝ)
    (_hL : 0 < L) (hδ : 0 < δ)
    (hLip : ∀ u v, ‖(f u : E) - f v‖ ≤ L * ‖(u : E) - v‖)
    (hDisp : ∀ u, δ ≤ ‖(f u : E) - u‖)
    (x z : Fin D → UnitBall E) (hrec : ∀ i, x i = f (z i)) :
    δ ^ 2 ≤ L ^ 2 * (D : ℝ)⁻¹ *
      ∑ i, ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 := by
  have hxmean : finMean (fun i => (f (z i) : E)) = (ballMean hD x : E) := by
    rw [coe_ballMean]
    apply congrArg finMean
    funext i
    exact congrArg Subtype.val (hrec i).symm
  have hmean : finMean (fun i => (f (z i) : E) - (f (ballMean hD x) : E)) =
      (ballMean hD x : E) - (f (ballMean hD x) : E) := by
    rw [finMean_sub, finMean_const hD, hxmean]
  have hdis : δ ≤ ‖(ballMean hD x : E) - (f (ballMean hD x) : E)‖ := by
    calc
      δ ≤ ‖(f (ballMean hD x) : E) - (ballMean hD x : E)‖ := hDisp _
      _ = ‖(ballMean hD x : E) - (f (ballMean hD x) : E)‖ := norm_sub_rev _ _
  have hlip_sq (i : Fin D) :
      ‖(f (z i) : E) - (f (ballMean hD x) : E)‖ ^ 2 ≤
        L ^ 2 * ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 := by
    calc
      _ ≤ (L * ‖(z i : E) - (ballMean hD x : E)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hLip (z i) (ballMean hD x)) 2
      _ = _ := mul_pow _ _ _
  have hjensen := norm_finMean_sq_le hD
    (fun i => (f (z i) : E) - (f (ballMean hD x) : E))
  rw [hmean] at hjensen
  calc
    δ ^ 2 ≤ ‖(ballMean hD x : E) - (f (ballMean hD x) : E)‖ ^ 2 :=
      pow_le_pow_left₀ hδ.le hdis 2
    _ ≤ (D : ℝ)⁻¹ * ∑ i,
        ‖(f (z i) : E) - (f (ballMean hD x) : E)‖ ^ 2 := hjensen
    _ ≤ (D : ℝ)⁻¹ * ∑ i,
        L ^ 2 * ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlip_sq i))
        (inv_nonneg.mpr (Nat.cast_nonneg D))
    _ = L ^ 2 * (D : ℝ)⁻¹ *
        ∑ i, ‖(z i : E) - (ballMean hD x : E)‖ ^ 2 := by
      rw [← Finset.mul_sum]
      ring

end ThompsonNonamenability

end OAI
