import OAI.NumberTheory.CubicMoment.Estimates.OuterPowerScale

namespace OAI

/-! Recover the three primal powers from the exact summed Poisson bound.
The epsilon loss does not multiply the separate unit zero-frequency term. -/
noncomputable section
namespace CubicFirstMoment

lemma outer_poisson_power_common {Z N R : ℝ} (hZ : 0 < Z) (hN : 0 < N)
    (hR : 0 < R) (ε α β : ℝ) :
    (Z/N)*(4*R*N)^ε*(R*N)^β*(Z/(27*N^2))^(-(ε+α)) =
      (4*R)^ε*R^β*27^(ε+α)*(N^3/Z)^ε*Z^(1-α)*N^(β+2*α-1) := by
  rw [outer_poisson_power_scale hZ hN hR]
  have hp : (N^3/Z)^ε = N^(3*ε)/Z^ε := by
    rw [Real.div_rpow (by positivity) hZ.le,← Real.rpow_natCast N 3,
      ← Real.rpow_mul hN.le]
    norm_num
  have hz : Z^(1-(ε+α)) = Z^(1-α)/Z^ε := by
    rw [show 1-(ε+α) = (1-α)-ε by ring,Real.rpow_sub hZ]
  have hn : N^(ε+β+2*(ε+α)-1) = N^(3*ε)*N^(β+2*α-1) := by
    rw [show ε+β+2*(ε+α)-1 = 3*ε+(β+2*α-1) by ring,Real.rpow_add hN]
  rw [hp,hz,hn]
  ring

def outerPowerConstant (ε R : ℝ) : ℝ :=
  2*(4*R)^ε*(SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*27^(ε+1) +
    R^(2/3:ℝ)*SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*27^(ε+2/3) +
    R*SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*27^(ε+1/3))

lemma outerPowerConstant_pos {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 < R) : 0 < outerPowerConstant ε R := by
  have h1 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1) (by linarith) (by linarith)
  have h2 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+2/3) (by linarith) (by linarith)
  have h3 := SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1/3) (by linarith) (by linarith)
  unfold outerPowerConstant
  positivity

lemma outer_primal_scale_bound {Z N R C ε : ℝ} (hZ : 0 < Z) (hN : 0 < N)
    (hR : 0 < R) (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2)) ≤
      C*outerPowerConstant ε R*(N^3/Z)^ε*
        (N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)) := by
  let d₁ := SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*27^(ε+1)
  let d₂ := R^(2/3:ℝ)*SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*27^(ε+2/3)
  let d₃ := R*SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*27^(ε+1/3)
  have hd₁ : 0 ≤ d₁ := mul_nonneg
    (SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1) (by linarith) (by linarith)).le
    (by positivity)
  have hd₂ : 0 ≤ d₂ := mul_nonneg (mul_nonneg (by positivity)
    (SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+2/3) (by linarith) (by linarith)).le)
    (by positivity)
  have hd₃ : 0 ≤ d₃ := mul_nonneg (mul_nonneg hR.le
    (SevenEighths.CubicDyadicDecay.decayConstant_pos (ε+1/3) (by linarith) (by linarith)).le)
    (by positivity)
  have h1 := outer_poisson_power_common hZ hN hR ε 1 0
  have h2 := outer_poisson_power_common hZ hN hR ε (2/3) (2/3)
  have h3 := outer_poisson_power_common hZ hN hR ε (1/3) 1
  norm_num at h1 h2 h3
  have heq : (2*C*(Z/N)*(4*(R*N))^ε)*outerDyadicBound ε (R*N) (Z/(27*N^2)) =
      2*C*(4*R)^ε*(N^3/Z)^ε*
        (d₁*N+d₂*(Z^(1/3:ℝ)*N)+d₃*(Z^(2/3:ℝ)*N^(2/3:ℝ))) := by
    unfold outerDyadicBound
    rw [show 4*(R*N) = 4*R*N by ring]
    calc
      _ = 2*C*(SevenEighths.CubicDyadicDecay.decayConstant (ε+1)*
          ((Z/N)*(4*R*N)^ε*(Z/(27*N^2))^(-(ε+1))) +
        SevenEighths.CubicDyadicDecay.decayConstant (ε+2/3)*
          ((Z/N)*(4*R*N)^ε*(R*N)^(2/3:ℝ)*(Z/(27*N^2))^(-(ε+2/3))) +
        SevenEighths.CubicDyadicDecay.decayConstant (ε+1/3)*
          ((Z/N)*(4*R*N)^ε*(R*N)*(Z/(27*N^2))^(-(ε+1/3)))) := by ring
      _ = _ := by simp only [neg_add_rev]; rw [h1,h2,h3]; dsimp [d₁,d₂,d₃]; ring
  rw [heq]
  have hb : d₁*N+d₂*(Z^(1/3:ℝ)*N)+d₃*(Z^(2/3:ℝ)*N^(2/3:ℝ)) ≤
      (d₁+d₂+d₃)*(N+Z^(1/3:ℝ)*N+Z^(2/3:ℝ)*N^(2/3:ℝ)) := by
    calc
      _ ≤ (d₁+d₂+d₃)*N+(d₁+d₂+d₃)*(Z^(1/3:ℝ)*N)+
          (d₁+d₂+d₃)*(Z^(2/3:ℝ)*N^(2/3:ℝ)) := by
        apply add_le_add
        · apply add_le_add <;> apply mul_le_mul_of_nonneg_right <;> first | positivity | linarith
        · apply mul_le_mul_of_nonneg_right <;> first | positivity | linarith
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by
    dsimp [outerPowerConstant,d₁,d₂,d₃]; ring)

end CubicFirstMoment

end

end OAI
