import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedResidualScale

namespace OAI

/-! Residual estimates for the exact half-cell boundaries of the centered
nuclear grid. The dimensions may vary over a factor-two interval. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem slabUniformBound_box {rho T H S : ℝ} (hrho : 0 ≤ rho) (hT : 1 ≤ T)
    (hH0 : 0 ≤ H) (hS0 : 0 ≤ S) (hH : H ≤ 2*T^10) (hS : S ≤ 2*T) :
    slabUniformBound rho H S ≤ 8*slabUniformBound rho (T^10) T := by
  rw [slabUniformBound,slabUniformBound,slabDomain_volume hH0 hS0,
    slabDomain_volume (by positivity) (by linarith)]
  have hm : 0 ≤ rho*NeutralAtom.kernelBallMass 1 :=
    mul_nonneg hrho (NeutralAtom.kernelBallMass_nonneg 1)
  have hv : 8*H^2*S*rho ≤ 8*(2*T^10)^2*(2*T)*rho := by gcongr
  nlinarith only [hm,hv]

private theorem squared_eight {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ≤ 8*b) : a^2 ≤ 64*b^2 := by
  have hs := (sq_le_sq₀ ha (by positivity : 0 ≤ 8*b)).mpr h
  nlinarith only [hs]

theorem slabSeventySecondTail_box_bound {rho T H S freq : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T)
    (hHlo : T^10 ≤ H) (hHhi : H ≤ 2*T^10)
    (hSlo : T ≤ S) (hShi : S ≤ 2*T) (u : PlanarPosition) :
    2*(6*Real.pi*rho*S^3/H)^2+
      2*(64*rho*S/H)^2*localizedDensityMoment freq u 4+
      2*(2*slabUniformBound rho H S)^2*(localizedDensityMoment freq u 72/T^72)+
      2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) ≤
      64*slabResidualSeventySecondBound rho freq u/T^14 := by
  have hT0 : 0 < T := by linarith
  have hH0 : 0 < H := (pow_pos hT0 10).trans_le hHlo
  have hS0 : 0 ≤ S := hT0.le.trans hSlo
  have hr1 : 6*Real.pi*rho*S^3/H ≤ 8*(6*Real.pi*rho*T^3/T^10) := by
    calc
      _ ≤ 6*Real.pi*rho*(2*T)^3/T^10 := by gcongr
      _ = _ := by ring
  have hr2 : 64*rho*S/H ≤ 8*(64*rho*T/T^10) := by
    calc
      _ ≤ 64*rho*(2*T)/T^10 := by gcongr
      _ = 2*(64*rho*T/T^10) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hb0 : 0 ≤ slabUniformBound rho H S :=
    (abs_nonneg _).trans (slabPotential_abs_bound hrho hH0.le hS0 (0 : Position))
  have hb1 : 0 ≤ slabUniformBound rho (T^10) T :=
    (abs_nonneg _).trans (slabPotential_abs_bound hrho (by positivity) hT0.le (0 : Position))
  have h1 := squared_eight (by positivity) (by positivity) hr1
  have h2 := squared_eight (by positivity) (by positivity) hr2
  have h3 := squared_eight hb0 hb1
    (slabUniformBound_box hrho (by linarith) hH0.le hS0 hHhi hShi)
  have hm4 := localizedDensityMoment_nonnegative freq u 4
  have hm72 := localizedDensityMoment_nonnegative freq u 72
  have h2' := mul_le_mul_of_nonneg_right h2 hm4
  have h3' := mul_le_mul_of_nonneg_right h3
    (show 0 ≤ localizedDensityMoment freq u 72/T^72 by positivity)
  have h4 : 0 ≤ 2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68) := by positivity
  calc
    _ ≤ 64*(2*(6*Real.pi*rho*T^3/T^10)^2+
        2*(64*rho*T/T^10)^2*localizedDensityMoment freq u 4+
        2*(2*slabUniformBound rho (T^10) T)^2*(localizedDensityMoment freq u 72/T^72)+
        2*(2*Real.pi*rho)^2*(localizedDensityMoment freq u 72/T^68)) := by
      nlinarith only [h1,h2',h3',h4]
    _ ≤ 64*(slabResidualSeventySecondBound rho freq u/T^14) :=
      mul_le_mul_of_nonneg_left (slabSeventySecondTail_tenthPower_bound hrho hT u) (by norm_num)
    _ = _ := by ring

theorem manufacturedOrbitalSquaredError_box {rho T H S freq δ D : ℝ}
    (hrho : 0 ≤ rho) (hT : 2 ≤ T)
    (hHlo : T^10 ≤ H) (hHhi : H ≤ 2*T^10)
    (hSlo : T ≤ S) (hShi : S ≤ 2*T)
    {m : ℕ} (u : Fin m → PlanarPosition) (j : Fin m) :
    manufacturedOrbitalSquaredError rho H S freq δ D T u j ≤
      3*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*Real.exp (-(19/10:ℝ)*D)+
        64*slabResidualSeventySecondBound rho freq (u j)/T^14+
        ((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
        256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*localizedDensityMoment freq (u j) 8/T^8) := by
  have hT0 : 0 < T := by linarith
  have hm := localizedDensityMoment_nonnegative freq (u j) 8
  have htail := slabSeventySecondTail_box_bound (freq := freq) hrho hT hHlo hHhi hSlo hShi (u j)
  have hw : ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
      (localizedDensityMoment freq (u j) 8/(S/2)^8) ≤
      256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*localizedDensityMoment freq (u j) 8/T^8 := by
    calc
      _ ≤ ((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*
          (localizedDensityMoment freq (u j) 8/(T/2)^8) := by gcongr
      _ = _ := by field_simp [ne_of_gt hT0]; ring
  unfold manufacturedOrbitalSquaredError
  linarith

end ContinuumCoulomb

end

end OAI
