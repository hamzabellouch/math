import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Basic
import OAI.Geometry.CAT0Fillings.Slicing.SmoothCutoff

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace CAT0Fillings.SmoothCutoff
open Set Filter
open scoped Topology NNReal

noncomputable def profile (a : ℝ≥0) (t x : ℝ) : ℝ :=
  Real.smoothTransition ((a:ℝ) * (x-t))
noncomputable def dprofile (a : ℝ≥0) (t x : ℝ) : ℝ :=
  (a:ℝ) * deriv Real.smoothTransition ((a:ℝ) * (x-t))

lemma affine_lipschitz (a : ℝ≥0) (t : ℝ) :
    LipschitzWith a (fun x : ℝ => (a:ℝ)*(x-t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,←mul_sub,sub_sub_sub_cancel_right,abs_mul,abs_of_nonneg a.coe_nonneg]
  exact le_rfl

lemma profile_hasDerivAt (a : ℝ≥0) (t x : ℝ) :
    HasDerivAt (profile a t) (dprofile a t x) x := by
  have hd := ((@Real.smoothTransition.contDiff 1).differentiable (by norm_num) ((a:ℝ)*(x-t))).hasDerivAt
  change HasDerivAt (fun y => Real.smoothTransition ((a:ℝ)*(y-t)))
    ((a:ℝ)*deriv Real.smoothTransition ((a:ℝ)*(x-t))) x
  simpa only [Function.comp_def,id_eq,mul_one,mul_comm] using
    hd.comp x (((hasDerivAt_id x).sub_const t).const_mul (a:ℝ))

lemma profile_bounds (a : ℝ≥0) (t x : ℝ) :
    0 ≤ profile a t x ∧ profile a t x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma profile_zero (a : ℝ≥0) {t x : ℝ} (hx : x ≤ t) : profile a t x = 0 :=
  Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos a.coe_nonneg (sub_nonpos.mpr hx))

lemma dprofile_zero {a : ℝ≥0} (ha : 0 < a) {t x : ℝ}
    (hx : x ∉ Icc t (t+(a:ℝ)⁻¹)) : dprofile a t x = 0 := by
  have ha' : 0 < (a:ℝ) := ha
  have hnot : (a:ℝ)*(x-t) ∉ Icc 0 1 := by
    intro h
    apply hx
    refine ⟨?_,?_⟩
    · have : 0 ≤ x-t := (mul_nonneg_iff_of_pos_left ha').mp h.1
      linarith
    · have : x-t ≤ (a:ℝ)⁻¹ := by
        rw [inv_eq_one_div]
        apply (le_div_iff₀ ha').mpr
        simpa [mul_comm] using h.2
      linarith
  simp [dprofile,deriv_transition_eq_zero hnot]

lemma exists_profile_bounds : ∃ C : ℝ≥0, ∀ (a : ℝ≥0) (t : ℝ),
    LipschitzWith (C*a) (profile a t) ∧
    LipschitzWith (a*(C*a)) (dprofile a t) ∧
    ∀ x, |dprofile a t x| ≤ (C*a:ℝ≥0) := by
  obtain ⟨C,hC,hD,hb⟩ := exists_lipschitz_transition
  refine ⟨C,fun a t => ⟨hC.comp (affine_lipschitz a t),?_,?_⟩⟩
  · change LipschitzWith (a*(C*a)) (fun x => (a:ℝ)*deriv Real.smoothTransition ((a:ℝ)*(x-t)))
    simpa only [sub_zero,Function.comp_def] using
      (affine_lipschitz a 0).comp (hD.comp (affine_lipschitz a t))
  · intro x
    simp only [dprofile,abs_mul,abs_of_nonneg a.coe_nonneg,NNReal.coe_mul]
    calc
      (a:ℝ) * |deriv Real.smoothTransition ((a:ℝ)*(x-t))| ≤ (a:ℝ)*C :=
        mul_le_mul_of_nonneg_left (hb _) a.coe_nonneg
      _ = (C:ℝ)*a := mul_comm _ _

lemma profile_sequence_tendsto (t x : ℝ) :
    Tendsto (fun n : ℕ => profile ((n:ℝ≥0)+1) t x) atTop
      (𝓝 ((Ioi t).indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : t < x
  · rw [indicator_of_mem (show x ∈ Ioi t from hx)]
    have hlim : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(x-t)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const (sub_pos.mpr hx)
    have heq : (fun n : ℕ => profile ((n:ℝ≥0)+1) t x) =ᶠ[atTop] fun _ => (1:ℝ) := by
      filter_upwards [hlim.eventually (eventually_ge_atTop 1)] with n hn
      apply Real.smoothTransition.one_of_one_le
      simpa only [NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hn
    exact tendsto_const_nhds.congr' heq.symm
  · rw [indicator_of_notMem (show x ∉ Ioi t from hx)]
    simpa only [profile_zero _ (le_of_not_gt hx)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end CAT0Fillings.SmoothCutoff
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

end

end OAI
