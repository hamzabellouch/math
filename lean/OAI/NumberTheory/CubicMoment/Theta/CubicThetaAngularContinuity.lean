import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularConvergence

namespace OAI

/-! Locally uniform convergence for the fixed-angular theta expansion. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngular_continuousOn_strip {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hb : 0 < b) :
    ContinuousOn (cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ))
      {p : ℂ × ℝ | b < p.2} := by
  let K := C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ ℓ.natAbs+3)).le) (by positivity))
      (by positivity)
  have hp : (4/3:ℝ)-2*((ℓ.natAbs:ℝ)+3) ≤ 0 := by
    have hk : (0:ℝ) ≤ ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have hs := (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (K*b^(4/3-2*((ℓ.natAbs:ℝ)+3)))
  apply continuousOn_tsum
    (fun n p h => (cubicThetaSeriesTerm_continuousAt _ n (hb.trans h)).continuousWithinAt) hs
  intro n p h
  change b < p.2 at h
  have hpower : p.2^(4/3-2*((ℓ.natAbs:ℝ)+3)) ≤ b^(4/3-2*((ℓ.natAbs:ℝ)+3)) :=
    Real.rpow_le_rpow_of_nonpos hb h.le hp
  calc
    _ ≤ (K*p.2^(4/3-2*((ℓ.natAbs:ℝ)+3)))*norm n^(-4/3:ℝ) :=
      cubicThetaAngular_term_bound hC ha ℓ (hb.trans h) p.1 n
    _ ≤ _ := by
      simpa only [neg_div] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hK)
          (Real.rpow_nonneg (norm_nonneg n) (-4/3:ℝ))

/-- The fixed signed angular Fourier expansion is a continuous function
at every point of the upper half-space. -/
theorem cubicThetaAngular_continuousAt {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) {p : ℂ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ)) p := by
  have hs := cubicThetaAngular_continuousOn_strip hC ha ℓ
    (show 0 < p.2/2 by positivity)
  have ho : IsOpen {q : ℂ × ℝ | p.2/2 < q.2} := isOpen_lt continuous_const continuous_snd
  exact hs.continuousAt (ho.mem_nhds (by change p.2/2 < p.2; linarith))

end CubicFirstMoment

end

end OAI
