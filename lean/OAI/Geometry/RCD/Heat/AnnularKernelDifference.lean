import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.KernelGaussianDifference
import OAI.Geometry.RCD.Heat.HeatBallPowerVolume
import OAI.Geometry.RCD.Heat.GaussianAnnularGradient

namespace OAI

/-! # Uniform heat-kernel differences across a separated annulus -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

private theorem inverse_volume_coefficient {n : ℕ} {s R V W C H : ℝ}
    (hs : 0 < s) (hR : 0 < R) (hV : 0 < V) (hW : 0 < W) (hC : 0 ≤ C) (hH : 0 < H)
    (hv : (s/(H*R))^n*V ≤ W) :
    C/(s*W) ≤ (C*H^n/V)*((R/s)^n/s) := by
  let D := H^n*(R/s)^n
  have hD : 0 < D := by dsimp [D]; positivity
  have he : D*(s/(H*R))^n = 1 := by
    dsimp [D]
    rw [← mul_pow,← mul_pow]
    have hx : H*(R/s)*(s/(H*R)) = 1 := by field_simp
    rw [hx,one_pow]
  have hvol : V ≤ D*W := by
    calc
      V = D*((s/(H*R))^n*V) := by rw [← mul_assoc,he,one_mul]
      _ ≤ D*W := mul_le_mul_of_nonneg_left hv hD.le
  have hi : 1/W ≤ D/V := (div_le_div_iff₀ hW hV).mpr (by simpa only [one_mul] using hvol)
  calc
    C/(s*W) = (C/s)*(1/W) := by ring
    _ ≤ (C/s)*(D/V) := mul_le_mul_of_nonneg_left hi (div_nonneg hC hs.le)
    _ = _ := by dsimp [D]; ring

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Positive separation from a source annulus absorbs all small-time losses
in the Gaussian difference estimate. The constant precedes both the center
and the working radius. -/
theorem NoncollapsedRCD.annular_kernel_difference {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) :
    ∃ J : ℝ, 0 < J ∧ ∀ (p : X) (R t : ℝ), 0 < R → -1 ≤ K*R^2 →
      0 < t → t ≤ 1 → t ≤ R^2 → ∀ x y z : X,
      dist x p ≤ R/2 → R ≤ dist z p → dist z p ≤ 2*R → dist x y ≤ Real.sqrt t →
      |ker t x z-ker t y z| ≤
        J/(R*(hausdorff n X).real (ball p R))*dist x y := by
  obtain ⟨C₀,B₀,hC₀,hB₀,hupper⟩ := hg.upper_five (hausdorff n X)
  obtain ⟨C,D,B,hC,hD,hB,hdiff⟩ :=
    hX.gaussianHeatDifferenceBounds_of_upper hn hk hC₀ hB₀ hupper
  obtain ⟨Q,hQ,hbound⟩ := exists_annular_gaussian_gradient_bound n hD
  let H := 4*Real.exp 8
  let J := C*H^n*Q*Real.exp B
  have hH : 0 < H := by dsimp [H]; positivity
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  refine ⟨J,by dsimp [J]; positivity,?_⟩
  intro p R t hR hcurv ht ht1 htR x y z hxp hzp hzp2 hxy
  let μ := hausdorff n X
  let V := μ.real (ball p R)
  let W := μ.real (ball z (Real.sqrt t))
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport p R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hW : 0 < W := ENNReal.toReal_pos (hX.fullSupport z _ hs).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hv : (Real.sqrt t/(H*R))^n*V ≤ W :=
    hX.heat_ball_volume_lower hn p hR hcurv ht htR z hzp2
  have hc := inverse_volume_coefficient hs hR hV hW hC.le hH hv
  have hsep : R/2 ≤ dist x z := by
    have hh := dist_triangle z x p
    rw [dist_comm z x] at hh
    linarith
  have he : Real.exp (-dist x z^2/(D*t)+B*t) ≤
      Real.exp (-(R/2)^2/(D*t))*Real.exp B := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : (R/2)^2 ≤ dist x z^2 := pow_le_pow_left₀ (by positivity) hsep 2
    have hh := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ D*t)
    have hBt : B*t ≤ B := mul_le_of_le_one_right hB ht1
    simp only [neg_div]
    linarith
  have hgauss := hbound R t hR ht htR
  have hraw := hdiff t ht ht1 x y z hxy
  calc
    _ ≤ (C/(Real.sqrt t*W))*Real.exp (-dist x z^2/(D*t)+B*t)*dist x y := hraw.trans_eq (by dsimp [W,μ]; ring)
    _ ≤ ((C*H^n/V)*((R/Real.sqrt t)^n/Real.sqrt t))*
        (Real.exp (-(R/2)^2/(D*t))*Real.exp B)*dist x y := by
      gcongr
    _ = (C*H^n/V)*(((R/Real.sqrt t)^n/Real.sqrt t)*
        Real.exp (-(R/2)^2/(D*t)))*Real.exp B*dist x y := by ring
    _ ≤ (C*H^n/V)*(Q/R)*Real.exp B*dist x y := by gcongr
    _ = _ := by dsimp [J]; ring

end RegularPointCoordinates

end

end OAI
