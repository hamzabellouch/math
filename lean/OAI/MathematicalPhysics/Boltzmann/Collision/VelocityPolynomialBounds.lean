import OAI.MathematicalPhysics.Boltzmann.Branching.HalfGaussianMoment

namespace OAI

section

/-! # Hard-sphere pair rates controlled by the half-Gaussian moment -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

theorem norm_le_weight (v : Velocity) : ‖v‖ ≤ weight v := by
  have he := Real.add_one_le_exp (‖v‖^2/2)
  change ‖v‖ ≤ Real.exp (‖v‖^2/2)
  nlinarith [sq_nonneg (‖v‖-1)]

theorem pair_weight_le (v w : Velocity) : 1+‖v‖+‖w‖ ≤ 3*weight v*weight w := by
  have h1 := weight_one_le v
  have h2 := weight_one_le w
  have ha : weight v ≤ weight v*weight w := le_mul_of_one_le_right (weight_pos v).le h2
  have hb : weight w ≤ weight v*weight w := le_mul_of_one_le_left (weight_pos w).le h1
  have hc : 1 ≤ weight v*weight w := (h1.trans ha)
  linarith [norm_le_weight v,norm_le_weight w]

def pairMoment (f : Velocity → ℝ) : ℝ≥0∞ :=
  ∫⁻ p : Velocity × Velocity, ENNReal.ofReal ((1+‖p.1‖+‖p.2‖)*f p.1*f p.2)

theorem moment_tensor {f : Velocity → ℝ} (hfm : Measurable f) :
    (∫⁻ p : Velocity × Velocity, ENNReal.ofReal (weight p.1*f p.1)*
      ENNReal.ofReal (weight p.2*f p.2)) = moment f*moment f := by
  have hm : Measurable (fun v => ENNReal.ofReal (weight v*f v)) := by unfold weight; fun_prop
  rw [Measure.volume_eq_prod]
  exact MeasureTheory.lintegral_prod_mul hm.aemeasurable hm.aemeasurable

theorem pairMoment_le {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) :
    pairMoment f ≤ 3*moment f*moment f := by
  have hm : Measurable (fun p : Velocity × Velocity => ENNReal.ofReal (weight p.1*f p.1)*
      ENNReal.ofReal (weight p.2*f p.2)) := by unfold weight; fun_prop
  calc
    _ ≤ ∫⁻ p : Velocity × Velocity, (3:ℝ≥0∞)*(ENNReal.ofReal (weight p.1*f p.1)*
        ENNReal.ofReal (weight p.2*f p.2)) := by
      apply lintegral_mono
      intro p
      have he : (1+‖p.1‖+‖p.2‖)*f p.1*f p.2 ≤
          3*((weight p.1*f p.1)*(weight p.2*f p.2)) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pair_weight_le p.1 p.2)
          (hf p.1)) (hf p.2)
        nlinarith [h]
      apply (ENNReal.ofReal_le_ofReal he).trans_eq
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),ENNReal.ofReal_mul
        (mul_nonneg (weight_pos p.1).le (hf p.1)),ENNReal.ofReal_ofNat]
    _ = 3*(moment f*moment f) := by rw [lintegral_const_mul _ hm,moment_tensor hfm]
    _ = _ := by ring

theorem pairMoment_le_square {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M) (hb : moment f ≤ ENNReal.ofReal M) :
    pairMoment f ≤ ENNReal.ofReal (3*M^2) := by
  calc
    _ ≤ 3*moment f*moment f := pairMoment_le hfm hf
    _ ≤ 3*ENNReal.ofReal M*ENNReal.ofReal M := mul_le_mul' (mul_le_mul' le_rfl hb) hb
    _ = _ := by rw [pow_two,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
      ENNReal.ofReal_mul hM,ENNReal.ofReal_ofNat]; ring

end BoltzmannNonuniqueness.VelocityMoment

end

end

section

/-! # Quantitative large-velocity tails for hard-sphere pair densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

def pairTailSet (R : ℝ) : Set (Velocity × Velocity) := {p | R < ‖p.1‖ ∨ R < ‖p.2‖}
def pairTail (R : ℝ) (f : Velocity → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in pairTailSet R, ENNReal.ofReal ((1+‖p.1‖+‖p.2‖)*f p.1*f p.2)

theorem pairTailSet_measurable (R : ℝ) : MeasurableSet (pairTailSet R) :=
  (measurableSet_lt measurable_const (measurable_fst.norm)).union
    (measurableSet_lt measurable_const (measurable_snd.norm))

private theorem norm_le_quarter (v : Velocity) : ‖v‖ ≤ Real.exp (‖v‖^2/4) := by
  have he := Real.add_one_le_exp (‖v‖^2/4)
  nlinarith [sq_nonneg (‖v‖-2)]

theorem pair_tail_weight_le {R : ℝ} (hR : 0 ≤ R) (v w : Velocity)
    (h : R < ‖v‖ ∨ R < ‖w‖) :
    1+‖v‖+‖w‖ ≤ (3*Real.exp (-R^2/4))*(weight v*weight w) := by
  let a := Real.exp (‖v‖^2/4)
  let b := Real.exp (‖w‖^2/4)
  have ha : 1 ≤ a := Real.one_le_exp (by positivity)
  have hb : 1 ≤ b := Real.one_le_exp (by positivity)
  have hab : 1 ≤ a*b := ha.trans (le_mul_of_one_le_right (by positivity) hb)
  have hva : ‖v‖ ≤ a*b := (norm_le_quarter v).trans (le_mul_of_one_le_right (by positivity) hb)
  have hwb : ‖w‖ ≤ a*b := (norm_le_quarter w).trans (le_mul_of_one_le_left (by positivity) ha)
  have hsq : R^2 ≤ ‖v‖^2+‖w‖^2 := by
    rcases h with hv | hw
    · have hh := (sq_le_sq₀ hR (norm_nonneg v)).mpr hv.le
      nlinarith [sq_nonneg ‖w‖]
    · have hh := (sq_le_sq₀ hR (norm_nonneg w)).mpr hw.le
      nlinarith [sq_nonneg ‖v‖]
  have he : a*b ≤ Real.exp (-R^2/4)*(weight v*weight w) := by
    dsimp [a,b,weight]
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  nlinarith

theorem pairTail_le {R : ℝ} (hR : 0 ≤ R) {f : Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) :
    pairTail R f ≤ ENNReal.ofReal (3*Real.exp (-R^2/4))*(moment f*moment f) := by
  have hm : Measurable (fun p : Velocity × Velocity => ENNReal.ofReal (weight p.1*f p.1)*
      ENNReal.ofReal (weight p.2*f p.2)) := by unfold weight; fun_prop
  unfold pairTail
  rw [← lintegral_indicator (pairTailSet_measurable R)]
  calc
    _ ≤ ∫⁻ p : Velocity × Velocity, ENNReal.ofReal (3*Real.exp (-R^2/4))*
        (ENNReal.ofReal (weight p.1*f p.1)*ENNReal.ofReal (weight p.2*f p.2)) := by
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ pairTailSet R
      · rw [indicator_of_mem hp]
        have he : (1+‖p.1‖+‖p.2‖)*f p.1*f p.2 ≤
            (3*Real.exp (-R^2/4))*((weight p.1*f p.1)*(weight p.2*f p.2)) := by
          have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (pair_tail_weight_le hR p.1 p.2 hp) (hf p.1)) (hf p.2)
          nlinarith [hh]
        apply (ENNReal.ofReal_le_ofReal he).trans_eq
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 3*Real.exp (-R^2/4)),
          ENNReal.ofReal_mul (mul_nonneg (weight_pos p.1).le (hf p.1))]
      · rw [indicator_of_notMem hp]
        exact zero_le
    _ = _ := by rw [lintegral_const_mul _ hm,moment_tensor hfm]

theorem pairTail_le_square {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v)
    (hb : moment f ≤ ENNReal.ofReal M) :
    pairTail R f ≤ ENNReal.ofReal (3*Real.exp (-R^2/4)*M^2) := by
  calc
    _ ≤ ENNReal.ofReal (3*Real.exp (-R^2/4))*(moment f*moment f) := pairTail_le hR hfm hf
    _ ≤ ENNReal.ofReal (3*Real.exp (-R^2/4))*(ENNReal.ofReal M*ENNReal.ofReal M) :=
      mul_le_mul' le_rfl (mul_le_mul' hb hb)
    _ = _ := by rw [show M^2 = M*M by ring,ENNReal.ofReal_mul (by positivity : 0 ≤ 3*Real.exp (-R^2/4)),
      ENNReal.ofReal_mul hM]

end BoltzmannNonuniqueness.VelocityMoment

end

end

section

/-! # The polynomial factors required for collision energy integrability -/

noncomputable section

namespace BoltzmannNonuniqueness.VelocityMoment

theorem norm_sq_le_weight (v : Velocity) : ‖v‖^2 ≤ 2*weight v := by
  have h := Real.add_one_le_exp (‖v‖^2/2)
  change ‖v‖^2 ≤ 2*Real.exp (‖v‖^2/2)
  linarith

theorem norm_cube_le_weight (v : Velocity) : ‖v‖^3 ≤ 5*weight v := by
  have h := Real.pow_div_factorial_le_exp (‖v‖^2/2) (by positivity) 2
  norm_num at h
  have hs := norm_sq_le_weight v
  have he : ‖v‖^4 ≤ 8*weight v := by
    change ‖v‖^4 ≤ 8*Real.exp (‖v‖^2/2)
    nlinarith
  nlinarith [sq_nonneg (‖v‖^2-‖v‖)]

theorem norm_sq_kernel_le_weight (v w : Velocity) (ω : Sphere) :
    ‖v‖^2*collisionKernel v w ω ≤ 7*weight v*weight w := by
  have hk := (collisionKernel_le_norm v w ω).trans (norm_sub_le v w)
  have hcross : ‖v‖^2*‖w‖ ≤ (2*weight v)*weight w :=
    mul_le_mul (norm_sq_le_weight v) (norm_le_weight w) (norm_nonneg _)
      (mul_nonneg (by norm_num) (weight_pos v).le)
  have hleft : 5*weight v ≤ 5*weight v*weight w :=
    le_mul_of_one_le_right (mul_nonneg (by norm_num) (weight_pos v).le) (weight_one_le w)
  calc
    _ ≤ ‖v‖^2*(‖v‖+‖w‖) := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ = ‖v‖^3+‖v‖^2*‖w‖ := by ring
    _ ≤ 5*weight v+(2*weight v)*weight w := add_le_add (norm_cube_le_weight v) hcross
    _ ≤ _ := by nlinarith

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
