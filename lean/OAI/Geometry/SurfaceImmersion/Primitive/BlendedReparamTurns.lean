import OAI.Geometry.SurfaceImmersion.Primitive.BlendedVelocityPath
import OAI.Geometry.SurfaceImmersion.Primitive.PositiveDensityTurns

namespace OAI

/-! Exact two-turn geometry for the blended path after positive reparametrization. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def unitAngle (a A s h t : ℝ) : ℝ := blendedAngle a A s h (2 * Real.pi * t)

variable {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]

lemma unitAngle_smooth {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z : B × ℝ => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2) := by
  have hb : ContDiff ℝ ∞ (fun z : B × ℝ => baseAngle (a z.1) (2 * Real.pi * z.2)) :=
    baseAngle_smooth.comp ((ha.comp contDiff_fst).prodMk (contDiff_const.mul contDiff_snd))
  exact ((hh.comp contDiff_fst).add
    ((contDiff_const.sub (hs.comp contDiff_fst)).mul hb)).add
      ((hs.comp contDiff_fst).mul ((hA.comp contDiff_fst).mul
        (contDiff_const.mul contDiff_snd).cos))

lemma unitAngle_deriv_zero_iff {a A s : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hs : s ∈ Icc (0 : ℝ) 1) (h t : ℝ) :
    deriv (unitAngle a A s h) t = 0 ↔ Real.sin (2 * Real.pi * t) = 0 := by
  have hd := (hasDerivAt_blendedAngle a A s h (2 * Real.pi * t)).comp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi))
  change deriv ((blendedAngle a A s h) ∘ fun u => 2 * Real.pi * u) t = 0 ↔ _
  rw [hd.deriv]
  have hspeed := (blended_speed_positive ha hA hs.1 hs.2 (2 * Real.pi * t)).ne'
  simp [hspeed, Real.pi_ne_zero]

lemma unit_sin_zero_iff {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    Real.sin (2 * Real.pi * t) = 0 ↔ t = 0 ∨ t = 1 / 2 := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hperiod : 2 * Real.pi * t ∈ Ico (0 : ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg hp.le ht.1, by nlinarith [ht.2]⟩
  have hzero := (deriv_angle_eq_zero_iff_sin (a := 1) (θ := 2 * Real.pi * t) one_ne_zero).symm.trans
    (angle_two_turns (a := 1) one_ne_zero hperiod)
  rw [hzero]
  constructor
  · rintro (hz | hz)
    · left; nlinarith
    · right; nlinarith [Real.pi_pos]
  · rintro (rfl | rfl)
    · simp
    · right; ring

variable [FiniteDimensional ℝ B] {ρ : B × ℝ → ℝ} {U : Set B}

omit [FiniteDimensional ℝ B] in
lemma inverseClock_mem_period (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) {θ : ℝ} (hθ : θ ∈ Ico (0 : ℝ) 1) :
    PositiveDensity.inverseClock ρ b θ ∈ Ico (0 : ℝ) 1 := by
  have hm := PositiveDensity.clock_strictMono hU hρ hpos hb
  have hi := PositiveDensity.clock_inverseClock hU hρ hper hmass hb θ
  have hc1 : PositiveDensity.clock ρ b 1 = 1 := hmass b hb
  constructor
  · apply hm.le_iff_le.mp
    simpa only [PositiveDensity.clock_zero, hi] using hθ.1
  · apply hm.lt_iff_lt.mp
    rw [hi, hc1]
    exact hθ.2

theorem reparametrized_two_turns
    {a A s h : B → ℝ}
    (ha : ContDiff ℝ ∞ a) (hA : ContDiff ℝ ∞ A)
    (hs : ContDiff ℝ ∞ s) (hh : ContDiff ℝ ∞ h)
    (hU : IsOpen U) (hρ : ContDiffOn ℝ ∞ ρ (U ×ˢ univ))
    (hpos : ∀ b ∈ U, ∀ t, 0 < ρ (b, t))
    (hper : ∀ b ∈ U, Function.Periodic (fun t => ρ (b, t)) 1)
    (hmass : ∀ b ∈ U, (∫ t in 0..1, ρ (b, t)) = 1)
    {b : B} (hb : b ∈ U) (hab : 0 < a b) (hAb : 0 < A b)
    (hsb : s b ∈ Icc (0 : ℝ) 1) {θ : ℝ} (hθ : θ ∈ Ico (0 : ℝ) 1) :
    deriv (fun t => PositiveDensity.reparametrize ρ
      (fun z => unitAngle (a z.1) (A z.1) (s z.1) (h z.1) z.2) (b, t)) θ = 0 ↔
      θ = 0 ∨ θ = PositiveDensity.clock ρ b (1 / 2) := by
  rw [PositiveDensity.deriv_reparametrize_eq_zero_iff hU hρ hpos hper hmass
    (unitAngle_smooth ha hA hs hh).contDiffOn hb θ]
  change deriv (unitAngle (a b) (A b) (s b) (h b)) (PositiveDensity.inverseClock ρ b θ) = 0 ↔ _
  rw [unitAngle_deriv_zero_iff hab hAb hsb,
    unit_sin_zero_iff (inverseClock_mem_period hU hρ hpos hper hmass hb hθ)]
  constructor
  · rintro (hz | hz)
    · left
      have hi := PositiveDensity.clock_inverseClock hU hρ hper hmass hb θ
      simpa only [hz, PositiveDensity.clock_zero] using hi.symm
    · right
      have hi := PositiveDensity.clock_inverseClock hU hρ hper hmass hb θ
      simpa only [hz] using hi.symm
  · rintro (rfl | rfl)
    · left
      have hi := PositiveDensity.inverseClock_clock hU hρ hpos hb 0
      simpa only [PositiveDensity.clock_zero] using hi
    · exact Or.inr (PositiveDensity.inverseClock_clock hU hρ hpos hb (1 / 2))

end ClosedSurfaceR4.CollarVelocity

end

end OAI
