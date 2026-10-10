import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGaussianCoordinates
import OAI.NumberTheory.CubicMoment.Estimates.HuxleyGaussianRows

namespace OAI

/-! The Gaussian Fourier kernel and its periodized majorant. -/
noncomputable section
namespace CubicFirstMoment

def huxleyCoordinateWeight (a : ℝ) (p : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi*a*((p.1:ℝ)^2+(p.2:ℝ)^2))

def huxleyGaussianKernel (a : ℝ) (x : ℂ) : ℂ :=
  ∑' p : ℤ × ℤ,
    huxleyGaussianFactor a (huxleyXi₀ x) p.1 *
      huxleyGaussianFactor a (huxleyXi₁ x) p.2

lemma huxleyCoordinateWeight_phase (a : ℝ) (x : ℂ) (p : ℤ × ℤ) :
    (huxleyCoordinateWeight a p:ℂ)*huxleyFrequencyPhase x (ofCoords p.1 p.2) =
      huxleyGaussianFactor a (huxleyXi₀ x) p.1 *
        huxleyGaussianFactor a (huxleyXi₁ x) p.2 := by
  rw [huxley_frequency_phase_coordinates]
  unfold huxleyCoordinateWeight huxleyGaussianFactor
  rw [show (-Real.pi*a*((p.1:ℝ)^2+(p.2:ℝ)^2)) =
    -Real.pi*a*(p.1:ℝ)^2 + -Real.pi*a*(p.2:ℝ)^2 by ring]
  rw [Real.exp_add,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_exp]
  rw [show 2*Real.pi*(p.1:ℝ)*huxleyXi₀ x = 2*Real.pi*huxleyXi₀ x*(p.1:ℝ) by ring,
    show 2*Real.pi*(p.2:ℝ)*huxleyXi₁ x = 2*Real.pi*huxleyXi₁ x*(p.2:ℝ) by ring]
  ring

lemma huxleyGaussianKernel_norm_bound {a : ℝ} (ha : 0 < a) (x : ℂ) :
    ‖huxleyGaussianKernel a x‖ ≤
      (1/a)*huxleyPeriodizedGaussian ((2/3:ℝ)*(Real.pi/a)) x := by
  let t := (2/3:ℝ)*(Real.pi/a)
  have ht : 0 < t := by dsimp [t]; positivity
  let f : ℤ × ℤ → ℝ := fun p =>
    Real.exp (-Real.pi/a*((p.1:ℝ)-huxleyXi₀ x)^2)*
      Real.exp (-Real.pi/a*((p.2:ℝ)-huxleyXi₁ x)^2)
  let g : ℤ × ℤ → ℝ := fun p =>
    Real.exp (-t*‖(huxleyDualCoordinateEquiv p:ℂ)-x‖^2)
  have hg : Summable g :=
    (huxleyPeriodizedGaussian_summable ht x).comp_injective huxleyDualCoordinateEquiv.injective
  have hfg (p : ℤ × ℤ) : f p ≤ g p := by
    have hd := huxley_dual_coordinate_distance x p.1 p.2
    have hm := mul_le_mul_of_nonneg_left hd ht.le
    dsimp [f,g,huxleyDualCoordinateEquiv]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    change -Real.pi/a*((p.1:ℝ)-huxleyXi₀ x)^2 +
      -Real.pi/a*((p.2:ℝ)-huxleyXi₁ x)^2 ≤
      -t*‖(ofCoords (p.1+p.2) p.1:ℂ)-x‖^2
    calc
      _ = -(t*((3/2:ℝ)*(((p.1:ℝ)-huxleyXi₀ x)^2+
          ((p.2:ℝ)-huxleyXi₁ x)^2))) := by dsimp [t]; ring
      _ ≤ _ := by simpa only [neg_mul] using neg_le_neg hm
  have hf : Summable f := hg.of_nonneg_of_le (fun p => by dsimp [f]; positivity) hfg
  have he : huxleyGaussianKernel a x = ((1/a)*∑' p, f p:ℝ) := by
    unfold huxleyGaussianKernel
    rw [huxley_gaussian_two_coordinate_poisson ha]
    rw [← Complex.ofReal_tsum,← Complex.ofReal_mul]
  have hn : ‖huxleyGaussianKernel a x‖ = (1/a)*∑' p, f p := by
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact mul_nonneg (by positivity) (tsum_nonneg (fun p => by dsimp [f]; positivity))
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑' p, g p := hf.tsum_le_tsum hfg hg
    _ = huxleyPeriodizedGaussian t x := huxleyDualCoordinateEquiv.tsum_eq
      (fun z : Eisenstein => Real.exp (-t*‖(z:ℂ)-x‖^2))

end CubicFirstMoment

end

end OAI
