import Mathlib
import OAI.Analysis.CoulombIonization.Variational.IntegratedTruncatedControl
import OAI.Analysis.CoulombIonization.Variational.ShortRangePotential

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PotentialRecovery_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma truncated_potential_remainder {R t : ℝ} (ht : 0 < t) (htR : t < R)
    {f : TFSpace → ℝ} (hf : MemLp f (5/3) (ballMeasure R)) :
    |(∫ x, f x/‖x‖ ∂ballMeasure R)-
      (∫ x, (1/max ‖x‖ t)*f x ∂ballMeasure R)| ≤
      ∫ x in ball 0 t, ‖f x‖/‖x‖ := by
  have hi : Integrable (fun x => f x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul hf using 1
    funext x
    exact div_eq_inv_mul _ _
  have hj : Integrable (fun x => (1/max ‖x‖ t)*f x) (ballMeasure R) := by
    convert! (truncated_kernel_memLp R ht).integrable_mul hf using 1
  have hn : Integrable (fun x => ‖f x‖/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul hf.norm using 1
    funext x
    exact div_eq_inv_mul _ _
  have hb := hn.indicator (measurableSet_ball (x := (0:TFSpace)) (ε := t))
  have he : (∫ x, (ball (0:TFSpace) t).indicator (fun x => ‖f x‖/‖x‖) x ∂ballMeasure R) =
      ∫ x in ball 0 t, ‖f x‖/‖x‖ := by
    rw [integral_indicator measurableSet_ball]
    change (∫ x, ‖f x‖/‖x‖ ∂(volume.restrict (ball 0 R)).restrict (ball 0 t)) = _
    rw [Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball htR.le)]
  rw [←integral_sub hi hj]
  rw [←he,←Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hb
  filter_upwards [ae_restrict_of_ae (ae_ne_point (0:Space))] with x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_cases hxt : ‖x‖ < t
  · rw [indicator_of_mem (by simpa only [mem_ball_zero_iff] using hxt)]
    have hle := one_div_le_one_div_of_le hx0 (le_max_left ‖x‖ t)
    have hpos : 0 ≤ 1/‖x‖-1/max ‖x‖ t := sub_nonneg.mpr hle
    have hid : f x/‖x‖-(1/max ‖x‖ t)*f x = (1/‖x‖-1/max ‖x‖ t)*f x := by ring
    rw [hid,norm_mul,Real.norm_eq_abs,abs_of_nonneg hpos,div_eq_inv_mul]
    have hh := mul_le_mul_of_nonneg_right
      (sub_le_self (1/‖x‖) (by positivity : 0 ≤ 1/max ‖x‖ t)) (norm_nonneg (f x))
    simpa only [one_div,div_eq_inv_mul,mul_one] using hh
  · rw [indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hxt),
      max_eq_left (le_of_not_gt hxt)]
    simp [div_eq_mul_inv,mul_comm]

lemma tfBallPotential_at_zero (R : ℝ) (f : TFLp (ballMeasure R)) :
    tfBallPotential R f 0 = ∫ x, f x/‖x‖ ∂ballMeasure R := by
  simp only [tfBallPotential,zero_sub,norm_neg]

theorem tfPatchGap_potential_control {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    |tfBallPotential R σ 0-tfBallPotential R (tfPatchMinimizer R T hT Φ) 0| ≤
      Real.sqrt ((2/t)*tfPatchGap R T hT Φ σ)+
      (∫ x in ball 0 t, ‖σ x‖^(5/3:ℝ))^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*t^(1/5:ℝ)+
      (∫ x in ball 0 t, ‖tfPatchMinimizer R T hT Φ x‖^(5/3:ℝ))^(3/5:ℝ)*
        (8*Real.pi)^(2/5:ℝ)*t^(1/5:ℝ) := by
  let ρ := tfPatchMinimizer R T hT Φ
  let A := ∫ x, (1/max ‖x‖ t)*σ x ∂ballMeasure R
  let B := ∫ x, (1/max ‖x‖ t)*ρ x ∂ballMeasure R
  have hA : Integrable (fun x => (1/max ‖x‖ t)*σ x) (ballMeasure R) := by
    convert! (truncated_kernel_memLp R ht).integrable_mul (Lp.memLp σ) using 1
  have hB : Integrable (fun x => (1/max ‖x‖ t)*ρ x) (ballMeasure R) := by
    convert! (truncated_kernel_memLp R ht).integrable_mul (Lp.memLp ρ) using 1
  have hpair : (∫ x, (1/max ‖x‖ t)*(σ-ρ) x ∂ballMeasure R) = A-B := by
    dsimp only [A,B]
    rw [←integral_sub hA hB]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub σ ρ] with x hx
    simp only [hx,Pi.sub_apply,mul_sub]
  have htrunc := Real.abs_le_sqrt (tfPatchGap_truncated_control ht htR T hT Φ hσ)
  change |∫ x, (1/max ‖x‖ t)*(σ-ρ) x ∂ballMeasure R| ≤ _ at htrunc
  rw [hpair] at htrunc
  have hf := (truncated_potential_remainder ht htR (Lp.memLp σ)).trans
    (coulomb_short_range_holder ht ((Lp.memLp σ).mono_measure
      (Measure.restrict_mono (ball_subset_ball htR.le) le_rfl)))
  have hg := (truncated_potential_remainder ht htR (Lp.memLp ρ)).trans
    (coulomb_short_range_holder ht ((Lp.memLp ρ).mono_measure
      (Measure.restrict_mono (ball_subset_ball htR.le) le_rfl)))
  rw [tfBallPotential_at_zero,tfBallPotential_at_zero]
  change |(∫ x, σ x/‖x‖ ∂ballMeasure R)-(∫ x, ρ x/‖x‖ ∂ballMeasure R)| ≤ _
  have he : (∫ x, σ x/‖x‖ ∂ballMeasure R)-(∫ x, ρ x/‖x‖ ∂ballMeasure R) =
      (A-B)+((∫ x, σ x/‖x‖ ∂ballMeasure R)-A)-((∫ x, ρ x/‖x‖ ∂ballMeasure R)-B) := by ring
  rw [he]
  calc
    _ ≤ |(A-B)+((∫ x, σ x/‖x‖ ∂ballMeasure R)-A)|+
        |(∫ x, ρ x/‖x‖ ∂ballMeasure R)-B| := abs_sub _ _
    _ ≤ (|A-B|+|(∫ x, σ x/‖x‖ ∂ballMeasure R)-A|)+
        |(∫ x, ρ x/‖x‖ ∂ballMeasure R)-B| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add htrunc hf) hg

end CoulombAnalysis

end Work_PotentialRecovery_scope

open MeasureTheory Filter
open scoped ENNReal

namespace CoulombAtom

lemma weighted_abs_integrable_and_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w f : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hi : Integrable w μ)
    (hf : AEStronglyMeasurable f μ)
    (hs : Integrable (fun x => w x*(f x)^2) μ) :
    Integrable (fun x => w x*|f x|) μ ∧
      (∫ x, w x*|f x| ∂μ) ≤ Real.sqrt (∫ x, w x ∂μ)*
        Real.sqrt (∫ x, w x*(f x)^2 ∂μ) := by
  let a := fun x => Real.sqrt (w x)
  let b := fun x => Real.sqrt (w x)*|f x|
  have ha : AEStronglyMeasurable a μ := Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable
  have hb : AEStronglyMeasurable b μ := ha.mul hf.norm
  have ha2 (x : α) : a x^2 = w x := Real.sq_sqrt (hw x)
  have hb2 (x : α) : b x^2 = w x*(f x)^2 := by
    dsimp only [b]
    rw [mul_pow,Real.sq_sqrt (hw x),sq_abs]
  have hab (x : α) : a x*b x = w x*|f x| := by
    dsimp only [a,b]
    rw [←mul_assoc,←pow_two,Real.sq_sqrt (hw x)]
  have hma : MemLp a 2 μ := (memLp_two_iff_integrable_sq ha).2 (by simpa only [ha2] using hi)
  have hmb : MemLp b 2 μ := (memLp_two_iff_integrable_sq hb).2 (by simpa only [hb2] using hs)
  have hip : Integrable (fun x => a x*b x) μ := by
    convert! hma.integrable_mul hmb using 1
  refine ⟨by simpa only [hab] using hip,?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.sqrt_nonneg (w x))
    (Eventually.of_forall fun x => mul_nonneg (Real.sqrt_nonneg (w x)) (abs_nonneg (f x)))
    (show MemLp a (ENNReal.ofReal 2) μ by simpa using hma)
    (show MemLp b (ENNReal.ofReal 2) μ by simpa using hmb)
  simpa only [hab,Real.rpow_two,ha2,hb2,←Real.sqrt_eq_rpow] using h

lemma finite_weighted_abs_bound {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ : ∀ i, Measure (α i)} {w f : ∀ i, α i → ℝ}
    (hw : ∀ i x, 0 ≤ w i x) (hi : ∀ i, Integrable (w i) (μ i))
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hs : ∀ i, Integrable (fun x => w i x*(f i x)^2) (μ i)) :
    (∑ i, ∫ x, w i x*|f i x| ∂μ i) ≤
      Real.sqrt (∑ i, ∫ x, w i x ∂μ i)*
        Real.sqrt (∑ i, ∫ x, w i x*(f i x)^2 ∂μ i) := by
  calc
    _ ≤ ∑ i, Real.sqrt (∫ x, w i x ∂μ i)*
        Real.sqrt (∫ x, w i x*(f i x)^2 ∂μ i) :=
      Finset.sum_le_sum fun i _ => (weighted_abs_integrable_and_bound (hw i) (hi i) (hf i) (hs i)).2
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun i => integral_nonneg (hw i))
      (fun i => integral_nonneg (fun x => mul_nonneg (hw i x) (sq_nonneg _)))

end CoulombAtom

end

end OAI
