import OAI.NumberTheory.CubicMoment.Angular.AngularLatticeProfile
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace OAI

/-! Fixed smooth cutoffs and a proper smooth logarithmic extension.
They transfer the common log-derivative bounds to the actual annuli. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology SchwartzMap
namespace CubicFirstMoment

def angularPositiveCutoff (a b x : ℝ) : ℝ :=
  Real.smoothTransition ((x-a/2)/(a/2))*Real.smoothTransition ((2*b-x)/b)

lemma angularPositiveCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (angularPositiveCutoff a b) := by
  unfold angularPositiveCutoff
  exact (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

lemma angularPositiveCutoff_one {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : a ≤ x ∧ x ≤ b) : angularPositiveCutoff a b x = 1 := by
  rw [angularPositiveCutoff,
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (by positivity : 0 < a/2)).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ hb).mpr (by linarith))]
  exact one_mul _

lemma angularPositiveCutoff_tsupport {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    tsupport (angularPositiveCutoff a b) ⊆ Icc (a/2) (2*b) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    have hzero : Real.smoothTransition ((x-a/2)/(a/2)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    exact hx (by simp only [angularPositiveCutoff,hzero,zero_mul])
  · by_contra hn
    have hzero : Real.smoothTransition ((2*b-x)/b) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hb.le)
    exact hx (by simp only [angularPositiveCutoff,hzero,mul_zero])

lemma angularPositiveCutoff_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (angularPositiveCutoff a b) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (angularPositiveCutoff_tsupport ha hb)

lemma angularPositiveCutoff_positive {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    tsupport (angularPositiveCutoff a b) ⊆ Ioi 0 := by
  intro x hx
  exact lt_of_lt_of_le (by linarith) (angularPositiveCutoff_tsupport ha hb hx).1

def angularLogPerturbation (a b x : ℝ) : ℝ :=
  angularPositiveCutoff a b x*(-Real.log x-x)

lemma angularLogPerturbation_smooth {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContDiff ℝ ∞ (angularLogPerturbation a b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hn : (0:ℝ) ∉ tsupport (angularPositiveCutoff a b) :=
      fun hh => (lt_irrefl (0:ℝ)) (angularPositiveCutoff_positive ha hb hh)
    have he := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    change angularPositiveCutoff a b x = 0 at hx
    simp only [angularLogPerturbation,hx,zero_mul]
  · exact (angularPositiveCutoff_smooth a b).contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).neg.sub contDiffAt_id)

lemma angularLogPerturbation_compact {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasCompactSupport (angularLogPerturbation a b) :=
  (angularPositiveCutoff_compact ha hb).mul_right

def angularLogExtension (a b x : ℝ) : ℝ := x+angularLogPerturbation a b x

lemma angularLogExtension_temperate {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Function.HasTemperateGrowth (angularLogExtension a b) := by
  have ht := (angularLogPerturbation_compact ha hb).hasTemperateGrowth
    (angularLogPerturbation_smooth ha hb)
  exact (ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth.add ht

lemma angularLogExtension_growth {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C*(1+‖angularLogExtension a b x‖)^k := by
  obtain ⟨M,hM⟩ := (angularLogPerturbation_smooth ha hb).continuous.bounded_above_of_compact_support
    (angularLogPerturbation_compact ha hb)
  refine ⟨1,max M 0+1,?_⟩
  intro x
  have hsmall := hM x
  have htri : ‖x‖ ≤ ‖angularLogExtension a b x‖+‖angularLogPerturbation a b x‖ := by
    have he : x = angularLogExtension a b x-angularLogPerturbation a b x := by
      simp only [angularLogExtension,add_sub_cancel_right]
    calc
      _ = ‖angularLogExtension a b x-angularLogPerturbation a b x‖ := congrArg (fun t : ℝ => ‖t‖) he
      _ ≤ _ := norm_sub_le _ _
  have hm : M ≤ max M 0 := le_max_left _ _
  rw [pow_one]
  nlinarith [_root_.norm_nonneg (angularLogExtension a b x),le_max_right M 0]

lemma angularLogExtension_eq_log {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : a ≤ x ∧ x ≤ b) : angularLogExtension a b x = -Real.log x := by
  rw [angularLogExtension,angularLogPerturbation,angularPositiveCutoff_one ha hb hx,one_mul]
  ring

end CubicFirstMoment

end

end OAI
