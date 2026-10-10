import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicPrimeWeights

namespace OAI

/-! Concrete total-variation control for rescaled prime weights and their
Mellin twists. This is the cost in the proved Abel summation inequality. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

lemma rescaled_mellin_deriv_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {Y x M D : ℝ} (hY : 0 < Y) (hx : Y ≤ x) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ‖w (x/Y)‖ ≤ M) (hwd : ‖deriv w (x/Y)‖*(x/Y) ≤ D) (u : ℝ) :
    ‖deriv (fun t => w (t/Y)*mellinPhase u t) x‖ ≤ (D+M*|u|)/Y := by
  have hxp : 0 < x := hY.trans_le hx
  have hdw := ((hw.differentiable (by norm_num)).differentiableAt.hasDerivAt).scomp x
    ((hasDerivAt_id x).div_const Y)
  have hb := norm_deriv_weighted_mellinPhase hdw u hxp
  have hd : ‖(1/Y) • deriv w (x/Y)‖ ≤ D/x := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos zero_lt_one hY)]
    apply (le_div_iff₀ hxp).mpr
    calc
      _ = ‖deriv w (x/Y)‖*(x/Y) := by ring
      _ ≤ _ := hwd
  calc
    _ ≤ D/x+M*(|u|/x) := hb.trans
      (add_le_add hd (mul_le_mul_of_nonneg_right hwm (div_nonneg (abs_nonneg _) hxp.le)))
    _ = (D+M*|u|)/x := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (add_nonneg hD (mul_nonneg hM (abs_nonneg _))) hY hx

lemma contDiffOn_rescaled_mellin {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (Y u : ℝ) :
    ContDiffOn ℝ ∞ (fun t => w (t/Y)*mellinPhase u t) (Ioi 0) := by
  intro x hx
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => u*Real.log t) x :=
    contDiffAt_const.mul (Real.contDiffAt_log.mpr (ne_of_gt hx))
  have hc : ContDiffAt ℝ ∞ (fun t : ℝ => ((u*Real.log t:ℝ):ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hl
  have hw' : ContDiff ℝ ∞ (fun t : ℝ => w (t/Y)) := hw.comp (contDiff_id.div_const Y)
  exact (hw'.contDiffAt.mul (hc.mul contDiffAt_const).cexp).contDiffWithinAt

lemma rescaled_mellin_variation {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    {Y R M D : ℝ} (hY : 0 < Y) (hR : 1 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hwm : ∀ x, ‖w x‖ ≤ M) (hwd : ∀ x, 0 < x → ‖deriv w x‖*x ≤ D) (u : ℝ) :
    let f := fun t => w (t/Y)*mellinPhase u t
    (∀ t ∈ Icc Y (R*Y), DifferentiableAt ℝ f t) ∧
    IntegrableOn (deriv f) (Icc Y (R*Y)) ∧
    ‖f Y‖+‖f (R*Y)‖+(∫ t in Ioc Y (R*Y), ‖deriv f t‖) ≤
      2*M+(R-1)*(D+M*|u|) := by
  dsimp only
  have hab : Y ≤ R*Y := by nlinarith
  have hsub : Icc Y (R*Y) ⊆ Ioi (0:ℝ) := fun _ ht => hY.trans_le ht.1
  have hs := contDiffOn_rescaled_mellin hw Y u
  have hd : ContinuousOn (deriv (fun t => w (t/Y)*mellinPhase u t)) (Icc Y (R*Y)) :=
    (hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  refine ⟨?_,hd.integrableOn_Icc,?_⟩
  · intro t ht
    exact ((hs t (hsub ht)).contDiffAt (isOpen_Ioi.mem_nhds (hsub ht))).differentiableAt (by norm_num)
  have hnorm (x : ℝ) : ‖w (x/Y)*mellinPhase u x‖ ≤ M := by
    simpa only [norm_mul,mellinPhase_norm,mul_one] using hwm (x/Y)
  have hint : (∫ t in Ioc Y (R*Y), ‖deriv (fun t => w (t/Y)*mellinPhase u t) t‖) ≤
      (R-1)*(D+M*|u|) := by
    rw [← intervalIntegral.integral_of_le hab]
    have hpoint : ∀ t ∈ uIoc Y (R*Y),
        ‖‖deriv (fun t => w (t/Y)*mellinPhase u t) t‖‖ ≤ (D+M*|u|)/Y := by
      intro t ht
      rw [uIoc_of_le hab] at ht
      rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]
      exact rescaled_mellin_deriv_bound hw hY ht.1.le hM hD (hwm _)
        (hwd _ (div_pos (hY.trans_le ht.1.le) hY)) u
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := Y) (b := R*Y)
      (f := fun t => ‖deriv (fun t => w (t/Y)*mellinPhase u t) t‖) hpoint
    have hnonneg : 0 ≤ ∫ t in Y..R*Y, ‖deriv (fun t => w (t/Y)*mellinPhase u t) t‖ :=
      intervalIntegral.integral_nonneg_of_forall hab (fun _ => _root_.norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg,abs_of_nonneg (sub_nonneg.mpr hab)] at hb
    convert hb using 1; field_simp
  linarith [hnorm Y,hnorm (R*Y)]

end CubicFirstMoment

end

end OAI
