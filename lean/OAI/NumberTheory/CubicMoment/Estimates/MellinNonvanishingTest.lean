import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition
import OAI.NumberTheory.CubicMoment.Estimates.MellinSmooth

namespace OAI

/-! At any chosen Mellin parameter a compact smooth test can cancel
the Mellin phase. Its transform there is a fixed positive integral. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def mellinPhaseCancelWeight (s : ℂ) (x : ℝ) : ℂ :=
  normPartitionWeight x*Complex.exp ((1-s)*(Real.log x:ℂ))

lemma mellinPhaseCancelWeight_compact (s : ℂ) :
    HasCompactSupport (mellinPhaseCancelWeight s) := normPartitionWeight_compact.mul_right

lemma mellinPhaseCancelWeight_positive (s : ℂ) :
    tsupport (mellinPhaseCancelWeight s) ⊆ Ioi 0 :=
  tsupport_mul_subset_left.trans normPartitionWeight_positive_support

lemma mellinPhaseCancelWeight_smooth (s : ℂ) : ContDiff ℝ ∞ (mellinPhaseCancelWeight s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (0:ℝ) ∉ tsupport normPartitionWeight := fun h =>
      (lt_irrefl (0:ℝ)) (normPartitionWeight_positive_support h)
    have he := notMem_tsupport_iff_eventuallyEq.mp hz
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    change normPartitionWeight y = 0 at hy
    simp only [mellinPhaseCancelWeight,hy,zero_mul]
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y:ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)
    exact normPartitionWeight_smooth.contDiffAt.mul (contDiffAt_const.mul hl).cexp

lemma normPartitionWeight_mellin_one_ne_zero : mellin normPartitionWeight 1 ≠ 0 := by
  let f : ℝ → ℝ := fun x => normPartitionStep x-normPartitionStep (3*x/4)
  have hf : Continuous f := by unfold f normPartitionStep; fun_prop
  have hfc : HasCompactSupport f := by
    have he : tsupport f = tsupport normPartitionWeight := by
      apply congrArg closure
      ext x
      simp only [Function.mem_support,f,normPartitionWeight,Complex.ofReal_ne_zero]
    change IsCompact (tsupport f)
    rw [he]
    exact normPartitionWeight_compact.isCompact
  have hfn : 0 ≤ f := by
    intro x
    by_cases hx : x < 1
    · have hzero := normPartitionWeight_low hx
      exact le_of_eq ((Complex.ofReal_eq_zero.mp hzero).symm)
    · exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
  have hp : 0 < ∫ x : ℝ, f x := by
    apply integral_pos_of_integrable_nonneg_nonzero hf (hf.integrable_of_hasCompactSupport hfc) hfn
      (x := (4/3:ℝ))
    simp only [f,normPartitionStep_one le_rfl]
    norm_num [normPartitionStep]
  have hsupport : Function.support f ⊆ Ioi 0 := by
    intro x hx
    apply normPartitionWeight_positive_support
    apply subset_tsupport
    change ((f x:ℝ):ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr hx
  have he : mellin normPartitionWeight 1 = (∫ x : ℝ, f x : ℝ) := by
    simp only [mellin,sub_self,Complex.cpow_zero,one_smul]
    change (∫ x : ℝ in Ioi 0, (f x:ℂ)) = _
    rw [integral_complex_ofReal,setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by by_contra hn; exact hx (hsupport hn))]
  rw [he]
  exact Complex.ofReal_ne_zero.mpr hp.ne'

lemma mellinPhaseCancelWeight_value (s : ℂ) :
    mellin (mellinPhaseCancelWeight s) s = mellin normPartitionWeight 1 := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  simp only [mellinPhaseCancelWeight,smul_eq_mul,sub_self,Complex.cpow_zero,one_mul]
  rw [Complex.cpow_def_of_ne_zero hx0,←Complex.ofReal_log (le_of_lt hx)]
  calc
    _ = normPartitionWeight x*Complex.exp (((Real.log x:ℂ)*(s-1))+(1-s)*(Real.log x:ℂ)) := by
      rw [Complex.exp_add]
      ring
    _ = _ := by ring_nf; simp

theorem exists_mellin_nonzero_test (s : ℂ) :
    ∃ W : ℝ → ℂ, HasCompactSupport W ∧ tsupport W ⊆ Ioi 0 ∧
      ContDiff ℝ ∞ W ∧ mellin W s ≠ 0 :=
  ⟨mellinPhaseCancelWeight s,mellinPhaseCancelWeight_compact s,
    mellinPhaseCancelWeight_positive s,mellinPhaseCancelWeight_smooth s,
    by rw [mellinPhaseCancelWeight_value]; exact normPartitionWeight_mellin_one_ne_zero⟩

end CubicFirstMoment

end

end OAI
