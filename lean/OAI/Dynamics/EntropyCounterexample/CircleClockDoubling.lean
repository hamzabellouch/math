import OAI.Dynamics.EntropyCounterexample.ClockCharts
import OAI.Geometry.SingularHomology.HomologyConjugacy

namespace OAI

noncomputable section

namespace Problem340.CircleClockDoubling

abbrev AngularCircle := AddCircle (1 : ℝ)

def homeomorph : AngularCircle ≃ₜ StandardClock :=
  (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).trans
    circleClockHomeomorph

@[simp] theorem homeomorph_apply (t : AngularCircle) :
    homeomorph t = circleClockHomeomorph (AddCircle.toCircle t) := by
  simp only [homeomorph, Homeomorph.trans_apply, AddCircle.homeomorphCircle_apply]

def angularDouble (t : AngularCircle) : AngularCircle := t + t

theorem continuous_angularDouble : Continuous angularDouble :=
  continuous_id.add continuous_id

def clockDouble (x : StandardClock) : StandardClock :=
  circleClockHomeomorph ((circleClockHomeomorph.symm x) ^ 2)

theorem continuous_clockDouble : Continuous clockDouble :=
  circleClockHomeomorph.continuous.comp (circleClockHomeomorph.symm.continuous.pow 2)

@[simp] theorem homeomorph_angularDouble (t : AngularCircle) :
    homeomorph (angularDouble t) = clockDouble (homeomorph t) := by
  simp only [homeomorph_apply, angularDouble, AddCircle.toCircle_add,
    clockDouble, Homeomorph.symm_apply_apply, pow_two]

theorem clockDouble_eq_conjugateMap :
    clockDouble = conjugateMap homeomorph angularDouble := by
  funext x
  rw [conjugateMap, homeomorph_angularDouble, Homeomorph.apply_symm_apply]

@[simp] theorem clockDouble_coe (x : StandardClock) :
    (clockDouble x).1 = complexClockLinearIsometry
      ((complexClockLinearIsometry.symm x.1) ^ 2) := by
  change complexClockLinearIsometry (((circleClockHomeomorph.symm x : Circle) ^ 2 : Circle) : ℂ) = _
  simp only [Circle.coe_pow]
  rfl

theorem clockDouble_coordinates (x : StandardClock) :
    (clockDouble x).1 = WithLp.toLp 2 ![x.1 0 ^ 2 - x.1 1 ^ 2, 2 * x.1 0 * x.1 1] := by
  rw [clockDouble_coe]
  let z := complexClockLinearIsometry.symm x.1
  have hx : complexClockLinearIsometry z = x.1 :=
    complexClockLinearIsometry.apply_symm_apply x.1
  have hx0 : z.re = x.1 0 := congrArg (fun y : ClockAmbient => y 0) hx
  have hx1 : z.im = x.1 1 := congrArg (fun y : ClockAmbient => y 1) hx
  change complexClockLinearIsometry (z ^ 2) = _
  ext i
  fin_cases i <;> simp [complexClockLinearIsometry_apply, pow_two,
    Complex.mul_re, Complex.mul_im, hx0, hx1]; ring

def homologyEquiv (n : ℕ) :
    RealSingularHomology n AngularCircle ≃ₗ[ℝ] RealSingularHomology n StandardClock :=
  realHomologyEquiv n homeomorph

@[simp] theorem homologyEquiv_apply (n : ℕ) (v : RealSingularHomology n AngularCircle) :
    homologyEquiv n v = realHomologyMap n homeomorph homeomorph.continuous v := rfl

theorem homologyEquiv_intertwines (n : ℕ) (v : RealSingularHomology n AngularCircle) :
    realHomologyMap n clockDouble continuous_clockDouble (homologyEquiv n v) =
      homologyEquiv n (realHomologyMap n angularDouble continuous_angularDouble v) := by
  simpa only [clockDouble_eq_conjugateMap, homologyEquiv] using
    realHomologyEquiv_conjugateMap n homeomorph continuous_angularDouble v

theorem eigenvector_transport (n : ℕ) (c : ℝ)
    (v : RealSingularHomology n AngularCircle) (hv : v ≠ 0)
    (heigen : realHomologyMap n angularDouble continuous_angularDouble v = c • v) :
    ∃ w : RealSingularHomology n StandardClock, w ≠ 0 ∧
      realHomologyMap n clockDouble continuous_clockDouble w = c • w := by
  refine ⟨homologyEquiv n v, ?_, ?_⟩
  · exact (map_ne_zero_iff (homologyEquiv n) (homologyEquiv n).injective).2 hv
  · rw [homologyEquiv_intertwines, heigen, map_smul]

end Problem340.CircleClockDoubling

end

end OAI
