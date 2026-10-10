import OAI.Geometry.RCD.Sobolev.InhomogeneousSobolev

namespace OAI

/-! # The localized Hölder step for harmonic level sets -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- On a finite measure space, a superquadratic moment controls L² with
the exact measure power used in the level-set iteration. -/
theorem square_integral_le_higher_moment [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 2 < p)
    (hi : Integrable (fun x => |f x|^p) μ) :
    (∫ x, (f x)^2 ∂μ) ≤ (∫ x, |f x|^p ∂μ)^(2/p)*
      (μ.real univ)^(1-2/p) := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p/2 := by positivity
  let q := Real.conjExponent (p/2)
  have hpq : (p/2).HolderConjugate q := Real.HolderConjugate.conjExponent (by linarith)
  have hpow (x : X) : ‖(f x)^2‖^(p/2) = |f x|^p := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs]
    rw [← Real.rpow_two,← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hfp : MemLp (fun x => (f x)^2) (ENNReal.ofReal (p/2)) μ := by
    apply (integrable_norm_rpow_iff (hf.pow 2) (by positivity) ENNReal.ofReal_ne_top).mp
    change Integrable (fun x => ‖(f x)^2‖^(ENNReal.ofReal (p/2)).toReal) μ
    simpa only [ENNReal.toReal_ofReal hp2.le,hpow] using hi
  have hg : MemLp (fun _ : X => (1:ℝ)) (ENNReal.ofReal q) μ := memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun x => sq_nonneg (f x))
    (Eventually.of_forall fun _ => zero_le_one) hfp hg
  have hq : 1/q = 1-2/p := by
    rw [one_div,← hpq.one_sub_inv]
    field_simp
  have hpexp : 1/(p/2) = 2/p := by field_simp
  have hpow' : (fun x => ((f x)^2)^(p/2)) = fun x => |f x|^p := by
    funext x
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f x))] using hpow x
  simpa only [mul_one,hpow',Real.one_rpow,integral_const,smul_eq_mul,mul_one,
    hpexp,hq,Measure.real] using h

/-- Restricting the L² integral to a level set inserts a positive power
of its measure while retaining the moment on the outer domain. -/
theorem square_setIntegral_le_higher_moment {Ω A : Set X}
    (_hΩ : MeasurableSet Ω) (_hA : MeasurableSet A) (hAΩ : A ⊆ Ω)
    (hfin : μ Ω < ∞) {f : X → ℝ} (hf : AEStronglyMeasurable f (μ.restrict Ω))
    {p : ℝ} (hp : 2 < p) (hi : IntegrableOn (fun x => |f x|^p) Ω μ) :
    (∫ x in A, (f x)^2 ∂μ) ≤ (∫ x in Ω, |f x|^p ∂μ)^(2/p)*
      (μ.real A)^(1-2/p) := by
  let : IsFiniteMeasure (μ.restrict A) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using lt_of_le_of_lt (measure_mono hAΩ) hfin⟩
  have hm : μ.restrict A ≤ μ.restrict Ω := Measure.restrict_mono hAΩ le_rfl
  have hh := square_integral_le_higher_moment (μ.restrict A) (hf.mono_measure hm) hp
    (hi.mono_set hAΩ)
  have hmono : (∫ x in A, |f x|^p ∂μ) ≤ ∫ x in Ω, |f x|^p ∂μ :=
    setIntegral_mono_set hi (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)
      (Eventually.of_forall fun _ hx => hAΩ hx)
  have hmom0 : 0 ≤ ∫ x in A, |f x|^p ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hp0 : 0 < p := by linarith
  simp only [Measure.real,Measure.restrict_apply_univ] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hmom0 hmono (by positivity)) (by positivity))

end RegularPointCoordinates

end

end OAI
