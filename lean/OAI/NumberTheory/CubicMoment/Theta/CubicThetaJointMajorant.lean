import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJointTermDerivative

namespace OAI

/-! Summable bounds for the actual full differential on positive strips. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngular_uniform_terms {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hb : 0<b) :
    ∃ u : Eisenstein → ℝ, Summable u ∧ ∀ (n : Eisenstein) (p : ℂ × ℝ), b<p.2 →
      ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) p.1 p.2 n‖≤u n := by
  let K := C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)
  let e : ℝ := 4/3-2*((ℓ.natAbs:ℝ)+3)
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerPowerConstant_pos (by omega : 1≤ℓ.natAbs+3)).le)
      (by positivity)) (by positivity)
  have he : e≤0 := by
    dsimp [e]
    have h : (0:ℝ)≤ℓ.natAbs := Nat.cast_nonneg _
    linarith
  refine ⟨fun n => (K*b^e)*norm n^(-4/3:ℝ),?_,?_⟩
  · simpa only [neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ)<4/3)).mul_left (K*b^e)
  · intro n p hp
    exact (cubicThetaAngular_term_bound hC ha ℓ (hb.trans hp) p.1 n).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb hp.le he) hK)
        (Real.rpow_nonneg (norm_nonneg n) _))

lemma cubicThetaAngular_uniform_vertical_terms {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hb : 0<b) :
    ∃ u : Eisenstein → ℝ, Summable u ∧ ∀ (n : Eisenstein) (p : ℂ × ℝ), b<p.2 →
      ‖cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) p.1 p.2 n‖≤u n := by
  let K := C*cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)
  let e : ℝ := 1/3-2*((ℓ.natAbs:ℝ)+3)
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerDerivativePowerConstant_pos (by omega : 1≤ℓ.natAbs+3)).le)
      (by positivity)) (by positivity)
  have he : e≤0 := by
    dsimp [e]
    have h : (0:ℝ)≤ℓ.natAbs := Nat.cast_nonneg _
    linarith
  refine ⟨fun n => (K*b^e)*norm n^(-4/3:ℝ),?_,?_⟩
  · simpa only [neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ)<4/3)).mul_left (K*b^e)
  · intro n p hp
    exact (cubicThetaAngular_vertical_term_bound hC ha ℓ (hb.trans hp) p.1 n).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hb hp.le he) hK)
        (Real.rpow_nonneg (norm_nonneg n) _))

theorem cubicThetaAngular_uniform_differentials {a : Eisenstein → ℂ} {C b : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hb : 0<b) :
    ∃ u : Eisenstein → ℝ, Summable u ∧ ∀ (n : Eisenstein) (p : ℂ × ℝ), b<p.2 →
      ‖cubicThetaSeriesTermFDeriv (cubicThetaAngularCoefficient a ℓ) p n‖≤u n := by
  obtain ⟨u,hu,hbu⟩ := cubicThetaAngular_uniform_terms hC ha ((ℓ.natAbs+1:ℕ):ℤ) hb
  obtain ⟨w,hw,hbw⟩ := cubicThetaAngular_uniform_vertical_terms hC ha ℓ hb
  refine ⟨fun n => 4*Real.pi*u n+w n,(hu.mul_left _).add hw,?_⟩
  intro n p hp
  calc
    _ ≤ 4*Real.pi*‖cubicThetaFrequency n‖*
        ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) p.1 p.2 n‖+
        ‖cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) p.1 p.2 n‖ :=
      cubicThetaSeriesTermFDeriv_norm_le _ p n
    _ = 4*Real.pi*
        ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ((ℓ.natAbs+1:ℕ):ℤ)) p.1 p.2 n‖+
        ‖cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) p.1 p.2 n‖ := by
      rw [←cubicThetaAngular_term_next_norm]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hbu n p hp) (by positivity)) (hbw n p hp)

end CubicFirstMoment

end

end OAI
