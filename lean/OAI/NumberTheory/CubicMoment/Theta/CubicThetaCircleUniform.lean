import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCircleActual

namespace OAI

/-! Uniform small-circle extraction above a fixed positive height. -/
noncomputable section
namespace CubicFirstMoment

local instance : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

theorem cubicThetaCircleActual_uniform {a : Eisenstein→ℂ} {C b M : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (hb : 0<b) (hM : 0≤M) (rev : Bool) (k : ℕ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (z d : ℂ) (v r : ℝ), b<v → ‖d‖≤M → 0<r →
      ‖fourierCoeff (fun t => cubicThetaNonconstant a (z+cubicThetaSignedCircle rev d r t,v))
          (k:ℤ)/(r:ℂ)^k-
        ((2*Real.pi*Complex.I)^k/(k.factorial:ℂ))*(cubicThetaCircleMultiplier rev d)^k*
          cubicThetaNonconstant (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev k)) (z,v)‖≤K*r := by
  obtain ⟨u,hu,hbu⟩ := cubicThetaAngular_uniform_terms hC ha (cubicThetaCircleOrder rev (k+1)) hb
  have hu0 (n : Eisenstein) : 0≤u n := (_root_.norm_nonneg
    (cubicThetaSeriesTerm (cubicThetaAngularCoefficient a
      (cubicThetaCircleOrder rev (k+1))) 0 (b+1) n)).trans (hbu n (0,b+1) (by linarith))
  let B : ℝ := (4*Real.pi)^(k+1)/(k.factorial:ℝ)
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨B*M^(k+1)*(∑' n, u n),
    mul_nonneg (mul_nonneg hB (pow_nonneg hM _)) (tsum_nonneg hu0),?_⟩
  intro z d v r hv hd hr
  have hv0 := hb.trans hv
  have hs := (cubicThetaAngular_summable hC ha (cubicThetaCircleOrder rev (k+1)) hv0 z).norm
  have hsum : (∑' n, ‖cubicThetaSeriesTerm
      (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖)≤∑' n, u n :=
    Summable.tsum_le_tsum (fun n => hbu n (z,v) hv) hs hu
  calc
    _ ≤ (B*‖d‖^(k+1)*∑' n, ‖cubicThetaSeriesTerm
        (cubicThetaAngularCoefficient a (cubicThetaCircleOrder rev (k+1))) z v n‖)*r :=
      cubicThetaCircleActual_remainder hC ha z d hv0 rev k hr
    _ ≤ _ := by gcongr

end CubicFirstMoment

end

end OAI
