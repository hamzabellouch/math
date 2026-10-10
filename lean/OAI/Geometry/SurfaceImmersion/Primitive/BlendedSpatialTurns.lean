import OAI.Geometry.SurfaceImmersion.Primitive.BlendedReparamTurns
import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCalculus

namespace OAI

/-! The actual spatial derivative at each turn of the normalized blended loop. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def blendedAmplitude (a A s : ℝ) : ℝ := (1 - s) * (2 * Real.arctan a) + s * A

lemma unitAngle_zero (a A s h : ℝ) :
    unitAngle a A s h 0 = h + blendedAmplitude a A s := by
  simpa only [unitAngle, mul_zero, blendedAmplitude] using blendedAngle_zero a A s h

lemma unitAngle_half (a A s h : ℝ) :
    unitAngle a A s h (1 / 2) = h - blendedAmplitude a A s := by
  have he : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
  simpa only [unitAngle, he, blendedAmplitude] using blendedAngle_pi a A s h

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma blendedAmplitude_smooth {a A s : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A) (hs : ContDiff ℝ ∞ s) :
    ContDiff ℝ ∞ (fun x => blendedAmplitude (a x) (A x) (s x)) :=
  ((contDiff_const.sub hs).mul (contDiff_const.mul ha.arctan)).add (hs.mul hA)

lemma unitAngle_angular_zero {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) (b : B) {t : ℝ}
    (ht : Real.sin (2 * Real.pi * t) = 0) :
    fderiv ℝ (fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2)
      (b, t) (0, 1) = 0 := by
  have hd := (hasDerivAt_blendedAngle (a b) (A b) (s b) (h b) (2 * Real.pi * t)).comp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi))
  have hf := SmoothPeriodicCalculus.angle_hasDerivAt (unitAngle_smooth ha hA hs hh) b t
  have he := hf.unique hd
  simpa only [ht, neg_zero, zero_mul, SmoothPeriodicCalculus.angleDerivative] using he

variable [FiniteDimensional ℝ B] {ρ : B × ℝ → ℝ} {U : Set B}

theorem reparametrized_spatial_turns {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h)
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) (v : B) :
    let F := fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2
    let amp := fun x => blendedAmplitude (a x) (A x) (s x)
    fderiv ℝ (fun x => PositiveDensity.reparametrize ρ F (x, 0)) b v =
      fderiv ℝ h b v + fderiv ℝ amp b v ∧
    fderiv ℝ (fun x => PositiveDensity.reparametrize ρ F
      (x, PositiveDensity.clock ρ b (1 / 2))) b v =
      fderiv ℝ h b v - fderiv ℝ amp b v := by
  dsimp only
  let F := fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2
  let amp := fun x => blendedAmplitude (a x) (A x) (s x)
  have hF : ContDiff ℝ ∞ F := unitAngle_smooth ha hA hs hh
  have hamp : ContDiff ℝ ∞ amp := blendedAmplitude_smooth ha hA hs
  have hi₀ : PositiveDensity.inverseClock ρ b 0 = 0 := by
    simpa only [PositiveDensity.clock_zero] using
      PositiveDensity.inverseClock_clock hU hρ hpos hb 0
  have hi₁ := PositiveDensity.inverseClock_clock hU hρ hpos hb (1 / 2)
  have hz₀ : fderiv ℝ F (b, PositiveDensity.inverseClock ρ b 0) (0, 1) = 0 := by
    rw [hi₀]
    exact unitAngle_angular_zero ha hA hs hh b (by simp)
  have hz₁ : fderiv ℝ F
      (b, PositiveDensity.inverseClock ρ b (PositiveDensity.clock ρ b (1 / 2))) (0, 1) = 0 := by
    rw [hi₁]
    apply unitAngle_angular_zero ha hA hs hh b
    have he : 2 * Real.pi * (1 / 2 : ℝ) = Real.pi := by ring
    rw [he, Real.sin_pi]
  have hd₀ := PositiveDensity.spatial_derivative_at_turn hU hρ hpos hper hmass
    hF.contDiffOn hb 0 hz₀ v
  have hd₁ := PositiveDensity.spatial_derivative_at_turn hU hρ hpos hper hmass
    hF.contDiffOn hb (PositiveDensity.clock ρ b (1 / 2)) hz₁ v
  rw [hi₀] at hd₀
  rw [hi₁] at hd₁
  have he₀ : (fun x => F (x, 0)) = (fun x => h x + amp x) :=
    funext (fun x => unitAngle_zero (a x) (A x) (s x) (h x))
  have he₁ : (fun x => F (x, 1 / 2)) = (fun x => h x - amp x) :=
    funext (fun x => unitAngle_half (a x) (A x) (s x) (h x))
  rw [he₀, fderiv_fun_add (hh.differentiable (by simp) b)
    (hamp.differentiable (by simp) b), add_apply] at hd₀
  rw [he₁, fderiv_fun_sub (hh.differentiable (by simp) b)
    (hamp.differentiable (by simp) b), sub_apply] at hd₁
  exact ⟨hd₀, hd₁⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI
