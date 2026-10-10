import OAI.Analysis.CircleDomains.Modulus.LinePayment
import OAI.Analysis.CircleDomains.Topology.HomeomorphicCoordinateRange
import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorEnergy
import Mathlib.MeasureTheory.Integral.CircleIntegral

namespace OAI

/-! Smooth circle variation controls a homeomorphic height on the enclosed
disk. This is the boundary step of the logarithmic modulus estimate. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def smoothCircleVariation (f : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2*Real.pi), |deriv (f ∘ circleMap c r) θ|

 theorem smooth_circle_anchor_bound {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℂ) (r : ℝ) {θ : ℝ} (hθ : θ ∈ Icc 0 (2*Real.pi)) :
    |f (circleMap c r θ)-f (circleMap c r 0)| ≤ smoothCircleVariation f c r := by
  let g := f ∘ circleMap c r
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_circleMap c r)
  have hgd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hFTC : (∫ t in (0 : ℝ)..θ, deriv g t) = g θ-g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (hg.differentiable (by norm_num) t).hasDerivAt)
      (hgd.intervalIntegrable 0 θ)
  have hI : IntervalIntegrable (fun t => |deriv g t|) volume 0 (2*Real.pi) :=
    hgd.abs.intervalIntegrable _ _
  calc
    _ = |∫ t in (0 : ℝ)..θ, deriv g t| := by rw [hFTC]; rfl
    _ ≤ ∫ t in (0 : ℝ)..θ, |deriv g t| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := deriv g) (μ := volume) hθ.1
    _ ≤ smoothCircleVariation f c r :=
      intervalIntegral.integral_mono_interval le_rfl hθ.1 hθ.2
        (Eventually.of_forall (fun t => abs_nonneg (deriv g t))) hI

 theorem smoothCircleVariation_sq_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℂ) (r : ℝ) :
    (smoothCircleVariation f c r)^2 ≤
      2*Real.pi*(∫ θ in (0 : ℝ)..(2*Real.pi), (deriv (f ∘ circleMap c r) θ)^2) := by
  have hd : Continuous (deriv (f ∘ circleMap c r)) :=
    (hf.comp (contDiff_circleMap c r)).continuous_deriv (by norm_num)
  simpa only [smoothCircleVariation, sub_zero, sq_abs] using
    integral_sq_le_length_mul_integral_sq (by positivity : (0 : ℝ) ≤ 2*Real.pi)
      (hd.abs.intervalIntegrable _ _) ((hd.abs.pow 2).intervalIntegrable _ _)

 theorem homeomorphic_pair_le_circle_variation (φ : ℂ ≃ₜ ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (c : ℂ) {r ε : ℝ} (hr : 0 < r)
    (happrox : ∀ z ∈ sphere c r, |(φ z).im-f z| ≤ ε)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im| ≤ 2*(smoothCircleVariation f c r+ε) := by
  let a := f (circleMap c r 0)
  let B := smoothCircleVariation f c r+ε
  have hbd : ∀ z ∈ frontier (closedBall c r), |(φ z).im-a| ≤ B := by
    intro z hz
    rw [frontier_closedBall c hr.ne'] at hz
    have hz' : z ∈ sphere c |r| := by simpa only [abs_of_pos hr] using hz
    rw [← image_circleMap_Ioc c r] at hz'
    obtain ⟨θ, hθ, rfl⟩ := hz'
    have hθ' : θ ∈ Icc 0 (2*Real.pi) := ⟨hθ.1.le, hθ.2⟩
    have ha := smooth_circle_anchor_bound hf c r hθ'
    have he := happrox (circleMap c r θ) (by simpa only [abs_of_pos hr] using circleMap_mem_sphere' c r θ)
    calc
      _ ≤ |(φ (circleMap c r θ)).im-f (circleMap c r θ)| + |f (circleMap c r θ)-a| :=
        abs_sub_le _ _ _
      _ ≤ B := by dsimp only [a, B]; linarith
  have hhi := homeomorphic_im_le_of_boundary φ (isCompact_closedBall c r)
    (C := a+B) (fun z hz => by linarith [(abs_le.mp (hbd z hz)).2])
  have hlo := homeomorphic_im_ge_of_boundary φ (isCompact_closedBall c r)
    (C := a-B) (fun z hz => by linarith [(abs_le.mp (hbd z hz)).1])
  have hxhi := hhi x hx
  have hyhi := hhi y hy
  have hxlo := hlo x hx
  have hylo := hlo y hy
  apply abs_le.mpr
  dsimp only [B] at *
  constructor <;> linarith

 theorem smooth_circle_deriv_sq_le {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (c : ℂ) (r θ : ℝ) :
    (deriv (f ∘ circleMap c r) θ)^2 ≤
      r^2 * ‖fderiv ℝ f (circleMap c r θ)‖^2 := by
  have he := ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_circleMap c r θ)).deriv
  rw [he]
  have h := (fderiv ℝ f (circleMap c r θ)).le_opNorm (circleMap 0 r θ*Complex.I)
  rw [norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, Real.norm_eq_abs] at h
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  simpa only [mul_pow, sq_abs, mul_comm] using hsq

end CircleDomainRigidity

end

end OAI
