import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model

namespace OAI

noncomputable section
namespace VelocityDetection.SmoothProfiles
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff

abbrev step := Real.smoothTransition

def pulse : ℝ → ℝ := deriv step

@[fun_prop] theorem contDiff_pulse : ContDiff ℝ ∞ pulse :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2

theorem pulse_nonneg (t : ℝ) : 0 ≤ pulse t :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem differentiable_step : Differentiable ℝ step :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).1

theorem pulse_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : pulse t = 0 := by
  have hd : Differentiable ℝ step := differentiable_step
  rw [pulse, ← (hd t).derivWithin (uniqueDiffWithinAt_Iic t)]
  calc
    derivWithin step (Iic t) t = derivWithin (fun _ : ℝ => (0 : ℝ)) (Iic t) t :=
      derivWithin_congr (fun x hx => Real.smoothTransition.zero_of_nonpos (hx.trans ht))
        (Real.smoothTransition.zero_of_nonpos ht)
    _ = 0 := by simp

theorem pulse_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : pulse t = 0 := by
  have hd : Differentiable ℝ step := differentiable_step
  rw [pulse, ← (hd t).derivWithin (uniqueDiffWithinAt_Ici t)]
  calc
    derivWithin step (Ici t) t = derivWithin (fun _ : ℝ => (1 : ℝ)) (Ici t) t :=
      derivWithin_congr (fun x hx => Real.smoothTransition.one_of_one_le (ht.trans hx))
        (Real.smoothTransition.one_of_one_le ht)
    _ = 0 := by simp

theorem support_pulse : support pulse ⊆ Ioo 0 1 := by
  intro t ht
  exact ⟨lt_of_not_ge (fun h => ht (pulse_zero_of_nonpos h)),
    lt_of_not_ge (fun h => ht (pulse_zero_of_one_le h))⟩

theorem compactSupport_pulse : HasCompactSupport pulse :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_pulse.trans Ioo_subset_Icc_self)

theorem integrable_pulse : Integrable pulse :=
  contDiff_pulse.continuous.integrable_of_hasCompactSupport compactSupport_pulse

theorem integral_pulse : (∫ t, pulse t) = 1 := by
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (support_pulse.trans Ioo_subset_Ioc_self)]
  change (∫ t in (0 : ℝ)..1, deriv step t) = 1
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => differentiable_step x) integrable_pulse.intervalIntegrable]
  norm_num [step]

def spatialPulse (p X : Coord 2) : ℝ :=
  ∏ i : Fin 2, pulse (X i - p i + 1 / 2)

@[fun_prop] theorem contDiff_spatialPulse (p : Coord 2) :
    ContDiff ℝ ∞ (spatialPulse p) := by
  unfold spatialPulse
  fun_prop

theorem spatialPulse_nonneg (p X : Coord 2) : 0 ≤ spatialPulse p X := by
  exact Finset.prod_nonneg (fun _ _ => pulse_nonneg _)

theorem support_spatialPulse (p : Coord 2) :
    support (spatialPulse p) ⊆ Ioo (fun i => p i - 1 / 2) (fun i => p i + 1 / 2) := by
  intro X hX
  have hi (i : Fin 2) : X i - p i + 1 / 2 ∈ Ioo (0 : ℝ) 1 := by
    apply support_pulse
    exact Finset.prod_ne_zero_iff.mp hX i (Finset.mem_univ _)
  constructor
  · exact ⟨fun i => le_of_lt (by linarith [(hi i).1]), by
      intro h
      have hh := h 0
      linarith [(hi 0).1]⟩
  · exact ⟨fun i => le_of_lt (by linarith [(hi i).2]), by
      intro h
      have hh := h 0
      linarith [(hi 0).2]⟩

theorem spatialPulse_support_bound (p X : Coord 2) (hX : spatialPulse p X ≠ 0) :
    ∀ i, |X i - p i| < 1 / 2 := by
  intro i
  have hi := support_pulse (Finset.prod_ne_zero_iff.mp hX i (Finset.mem_univ _))
  change 0 < X i - p i + 1 / 2 ∧ X i - p i + 1 / 2 < 1 at hi
  exact abs_lt.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩

theorem compactSupport_spatialPulse (p : Coord 2) : HasCompactSupport (spatialPulse p) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((support_spatialPulse p).trans Ioo_subset_Icc_self)

theorem integrable_spatialPulse (p : Coord 2) : Integrable (spatialPulse p) :=
  (contDiff_spatialPulse p).continuous.integrable_of_hasCompactSupport
    (compactSupport_spatialPulse p)

theorem integral_spatialPulse (p : Coord 2) : (∫ X, spatialPulse p X) = 1 := by
  unfold spatialPulse
  change (∫ X, ∏ i : Fin 2, pulse (X i - p i + 1 / 2) ∂Measure.pi (fun _ => volume)) = 1
  rw [integral_fin_nat_prod_eq_prod (fun (i : Fin 2) (x : ℝ) => pulse (x - p i + 1 / 2))]
  have hi (i : Fin 2) : (∫ x : ℝ, pulse (x - p i + 1 / 2)) = 1 := by
    simp_rw [show ∀ x : ℝ, x - p i + 1 / 2 = x + (-p i + 1 / 2) by intro x; ring]
    rw [integral_add_right_eq_self, integral_pulse]
  simp only [hi, Finset.prod_const_one]

def impulse (p : Coord 2) : ScalarField 2 := fun t X => pulse t * spatialPulse p X

@[fun_prop] theorem contDiff_impulse (p : Coord 2) :
    ContDiff ℝ ∞ (uncurry (impulse p)) := by
  unfold impulse uncurry
  exact (contDiff_pulse.comp contDiff_fst).mul ((contDiff_spatialPulse p).comp contDiff_snd)

theorem impulse_nonneg (p X : Coord 2) (t : ℝ) : 0 ≤ impulse p t X :=
  mul_nonneg (pulse_nonneg t) (spatialPulse_nonneg p X)

theorem impulse_support_bound (p X : Coord 2) (t : ℝ) (h : impulse p t X ≠ 0) :
    0 < t ∧ t < 1 ∧ ∀ i, |X i - p i| < 1 / 2 := by
  have h' : pulse t ≠ 0 ∧ spatialPulse p X ≠ 0 := mul_ne_zero_iff.mp h
  exact ⟨(support_pulse h'.1).1, (support_pulse h'.1).2,
    spatialPulse_support_bound p X h'.2⟩

theorem compactSupport_impulse (p : Coord 2) : HasCompactSupport (uncurry (impulse p)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
      (isCompact_Icc : IsCompact (Icc (fun i : Fin 2 => p i - 1 / 2)
        (fun i => p i + 1 / 2))))
  intro q hq
  have hq' : pulse q.1 ≠ 0 ∧ spatialPulse p q.2 ≠ 0 := mul_ne_zero_iff.mp hq
  exact ⟨Ioo_subset_Icc_self (support_pulse hq'.1),
    Ioo_subset_Icc_self (support_spatialPulse p hq'.2)⟩

theorem integral_impulse (p : Coord 2) (t : ℝ) :
    (∫ X, impulse p t X) = deriv step t := by
  simp only [impulse, integral_const_mul, integral_spatialPulse, mul_one, pulse]

theorem impulse_zero_of_time_nonpos (p : Coord 2) {t : ℝ} (ht : t ≤ 0) :
    impulse p t = 0 := by
  ext X
  simp [impulse, pulse_zero_of_nonpos ht]

theorem impulse_zero_of_time_one_le (p : Coord 2) {t : ℝ} (ht : 1 ≤ t) :
    impulse p t = 0 := by
  ext X
  simp [impulse, pulse_zero_of_one_le ht]

theorem impulse_derivatives_bounded (p : Coord 2) (k : ℕ) :
    ∃ C : ℝ, ∀ q, ‖iteratedFDeriv ℝ k (uncurry (impulse p)) q‖ ≤ C := by
  have hc := (contDiff_impulse p).continuous_iteratedFDeriv (m := k)
    (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨C, hC⟩ := hc.norm.bddAbove_range_of_hasCompactSupport
    ((compactSupport_impulse p).iteratedFDeriv k).norm
  exact ⟨C, fun q => hC (mem_range_self q)⟩

end VelocityDetection.SmoothProfiles
end

end OAI
