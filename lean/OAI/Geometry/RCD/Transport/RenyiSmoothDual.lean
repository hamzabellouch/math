import OAI.Geometry.RCD.Transport.RenyiPathPrimitive

namespace OAI

/-! # A smooth Sobolev primitive for localized power variations

The derivative is frozen below the positive density level. The primitive
vanishes at zero, so it defines an actual Sobolev function even when the
reference measure has infinite mass.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

def renyiSmoothSlope (ε q r : ℝ) : ℝ := (q-1)*(max r ε)^(q-1)

def renyiSmoothDual (ε q r : ℝ) : ℝ := ∫ s in 0..r, renyiSmoothSlope ε q s

theorem renyiSmoothSlope_continuous {ε : ℝ} (hε : 0<ε) (q : ℝ) :
    Continuous (renyiSmoothSlope ε q) := by
  apply Continuous.const_mul
  apply Continuous.rpow_const (by fun_prop)
  intro r
  exact Or.inl (ne_of_gt (hε.trans_le (le_max_right r ε)))

theorem renyiSmoothSlope_bound {ε q : ℝ} (hε : 0<ε) (hq : q≤1) (r : ℝ) :
    |renyiSmoothSlope ε q r|≤|q-1| * ε^(q-1) := by
  rw [renyiSmoothSlope,abs_mul,abs_of_nonneg (Real.rpow_nonneg
    (hε.le.trans (le_max_right r ε)) _)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hε (le_max_right r ε) (by linarith)) (abs_nonneg _)

theorem renyiSmoothDual_hasDerivAt {ε : ℝ} (hε : 0<ε) (q r : ℝ) :
    HasDerivAt (renyiSmoothDual ε q) (renyiSmoothSlope ε q r) r :=
  intervalIntegral.integral_hasDerivAt_right
    ((renyiSmoothSlope_continuous hε q).intervalIntegrable _ _)
    ((renyiSmoothSlope_continuous hε q).stronglyMeasurableAtFilter volume (𝓝 r))
    (renyiSmoothSlope_continuous hε q).continuousAt

theorem renyiSmoothDual_lipschitz {ε q : ℝ} (hε : 0<ε) (hq : q≤1) :
    LipschitzWith ⟨|q-1| * ε^(q-1),by positivity⟩ (renyiSmoothDual ε q) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun r => (renyiSmoothDual_hasDerivAt hε q r).differentiableAt)
  intro r
  rw [(renyiSmoothDual_hasDerivAt hε q r).deriv]
  exact_mod_cast renyiSmoothSlope_bound hε hq r

theorem renyiSmoothDual_zero (ε q : ℝ) : renyiSmoothDual ε q 0=0 := by
  simp [renyiSmoothDual]

theorem renyiSmoothDual_formula {ε q r : ℝ} (hε : 0<ε) (hq : q≠0) (hr : ε≤r) :
    renyiSmoothDual ε q r=renyiDualPower q r-
      (renyiDualPower q ε-renyiSmoothDual ε q ε) := by
  have hd (s : ℝ) (hs : s∈uIcc ε r) :
      HasDerivAt (renyiDualPower q) (renyiSmoothSlope ε q s) s := by
    rw [uIcc_of_le hr] at hs
    simpa only [renyiSmoothSlope,max_eq_left hs.1] using
      renyiDualPower_hasDerivAt hq (hε.trans_le hs.1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((renyiSmoothSlope_continuous hε q).intervalIntegrable ε r)
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((renyiSmoothSlope_continuous hε q).intervalIntegrable 0 ε)
    ((renyiSmoothSlope_continuous hε q).intervalIntegrable ε r)
  change renyiSmoothDual ε q ε + _=renyiSmoothDual ε q r at ha
  rw [he] at ha
  linarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def SobolevSpace.renyiSmooth (ρ : SobolevSpace μ hQ) {ε q : ℝ}
    (hε : 0<ε) (hq : q≤1) : SobolevSpace μ hQ :=
  SobolevSpace.comp μ hQ (renyiSmoothDual_lipschitz hε hq) (renyiSmoothDual_zero ε q) ρ

variable [ProperSpace X]

theorem localGamma_renyiSmooth (u ρ : SobolevSpace μ hQ) {ε q : ℝ}
    (hε : 0<ε) (hq : q≤1) :
    localGamma μ hQ u (ρ.renyiSmooth μ hQ hε hq) =ᵐ[μ]
      fun x => renyiSmoothSlope ε q (SobolevSpace.toLp μ hQ ρ x)*localGamma μ hQ u ρ x := by
  exact localGamma_comp_C1_right μ hQ u ρ (renyiSmoothDual_lipschitz hε hq)
    (renyiSmoothDual_zero ε q) (renyiSmoothSlope_continuous hε q)
    (renyiSmoothDual_hasDerivAt hε q) ⟨|q-1| * ε^(q-1),by positivity⟩
    (renyiSmoothSlope_bound hε hq)

end RegularPointCoordinates

end

end OAI
