import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterGrowth

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterLinear
variable {P E : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]

theorem ParamLinearGrowth.const_mul {f : P × E → ℝ} (hf : ParamLinearGrowth f) (m : ℝ) :
    ParamLinearGrowth (fun z => m*f z) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  refine ⟨|m| *C,mul_nonneg (abs_nonneg _) hC,?_⟩
  intro p e hp
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (hf p e hp) (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem ParamLinearGrowth.gaussian_integral {f : P × (E × ℝ) → ℝ}
    (hf : ParamLinearGrowth f) :
    ParamLinearGrowth (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  let B := ∫ y : ℝ, Real.exp |y| ∂gaussianReal 0 1
  have hB : 0 ≤ B := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hI : Integrable (fun y : ℝ => Real.exp |y|) (gaussianReal 0 1) := by
    simpa only [one_mul] using integrable_exp_mul_abs_gaussian 1
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  intro p e hp
  have hh y : |f (p,(e,y))| ≤ C*(1+‖e‖)*Real.exp |y| := by
    apply (hf p (e,y) hp).trans
    rw [Prod.norm_def,Real.norm_eq_abs]
    have hmax := max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
    have hex := Real.add_one_le_exp |y|
    have hprod := mul_nonneg (norm_nonneg e) (abs_nonneg y)
    have H : 1+max ‖e‖ |y| ≤ (1+‖e‖)*Real.exp |y| := by
      calc
        _ ≤ (1+‖e‖)*(1+|y|) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact (mul_le_mul_of_nonneg_left H hC).trans_eq (mul_assoc _ _ _).symm
  calc
    _ = ‖∫ y, f (p,(e,y)) ∂gaussianReal 0 1‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖f (p,(e,y))‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C*(1+‖e‖)*Real.exp |y| ∂gaussianReal 0 1 :=
      integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) (hI.const_mul _)
        (ae_of_all _ hh)
    _ = _ := by rw [integral_const_mul]; dsimp [B]; ring
end ParameterLinear

theorem gaussian_exp_integral_bounds (g : ℝ → ℝ) (hg : Continuous g) {A C : ℝ}
    (_hC : 0 ≤ C) (hb : ∀ y, |g y| ≤ A+C*|y|) :
    let Z := ∫ y, Real.exp (g y) ∂gaussianReal 0 1
    Real.exp (-A)*(∫ y : ℝ, Real.exp (-C*|y|) ∂gaussianReal 0 1) ≤ Z ∧
    Z ≤ Real.exp A*(∫ y : ℝ, Real.exp (C*|y|) ∂gaussianReal 0 1) := by
  have hupper y : Real.exp (g y) ≤ Real.exp A*Real.exp (C*|y|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hb y))
  have hlower y : Real.exp (-A)*Real.exp (-C*|y|) ≤ Real.exp (g y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hh := (abs_le.1 (hb y)).1
    linarith
  have hI : Integrable (fun y => Real.exp (g y)) (gaussianReal 0 1) := by
    apply ((integrable_exp_mul_abs_gaussian C).const_mul (Real.exp A)).mono' (Real.continuous_exp.comp hg).aestronglyMeasurable
    exact ae_of_all _ (fun y => by simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hupper y)
  dsimp only
  constructor
  · rw [← integral_const_mul]
    exact integral_mono ((integrable_exp_mul_abs_gaussian (-C)).const_mul _) hI hlower
  · rw [← integral_const_mul]
    exact integral_mono hI ((integrable_exp_mul_abs_gaussian C).const_mul _) hupper

section LogParameterLinear
variable {P E : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]

theorem ParamLinearGrowth.log_gaussian_exp {f : P × (E × ℝ) → ℝ}
    (hf : ParamLinearGrowth f) (hc : Continuous f) :
    ParamLinearGrowth (fun z : P × E => Real.log (∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1)) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  let Bp := ∫ y : ℝ, Real.exp (C*|y|) ∂gaussianReal 0 1
  let Bm := ∫ y : ℝ, Real.exp (-C*|y|) ∂gaussianReal 0 1
  have hp : 0 < Bp := integral_exp_pos (integrable_exp_mul_abs_gaussian C)
  have hm : 0 < Bm := integral_exp_pos (integrable_exp_mul_abs_gaussian (-C))
  let D := C+|Real.log Bp|+|Real.log Bm|
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro p e he
  let A := C*(1+‖e‖)
  have hb y : |f (p,(e,y))| ≤ A+C*|y| := by
    apply (hf p (e,y) he).trans
    rw [Prod.norm_def,Real.norm_eq_abs]
    have hh := max_le_add_of_nonneg (norm_nonneg e) (abs_nonneg y)
    dsimp [A]
    nlinarith
  have H := gaussian_exp_integral_bounds (fun y => f (p,(e,y)))
    (hc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) hC hb
  let Z := ∫ y, Real.exp (f (p,(e,y))) ∂gaussianReal 0 1
  have hz : 0 < Z := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hm) H.1
  have hu := Real.log_le_log hz H.2
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) hm) H.1
  change Real.log Z ≤ Real.log (Real.exp A*Bp) at hu
  change Real.log (Real.exp (-A)*Bm) ≤ Real.log Z at hl
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne',Real.log_exp] at hu
  rw [Real.log_mul (Real.exp_pos _).ne' hm.ne',Real.log_exp] at hl
  change |Real.log Z| ≤ D*(1+‖e‖)
  apply abs_le.2
  constructor
  · have hh := le_abs_self (Real.log Bm)
    have hneg := neg_abs_le (Real.log Bm)
    have hextra := mul_nonneg (add_nonneg (abs_nonneg (Real.log Bp)) (abs_nonneg (Real.log Bm))) (norm_nonneg e)
    dsimp [A,D] at *
    linarith [abs_nonneg (Real.log Bp)]
  · have hh := le_abs_self (Real.log Bp)
    have hextra := mul_nonneg (add_nonneg (abs_nonneg (Real.log Bp)) (abs_nonneg (Real.log Bm))) (norm_nonneg e)
    dsimp [A,D] at *
    linarith [abs_nonneg (Real.log Bm)]
end LogParameterLinear
end SK.Analytic

end
end

end

end OAI
