import OAI.Geometry.Kahler.BaseLogFactor

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma logFactor_complex_identity (ε : ℝ) (v : ℂ) :
    ‖1-v‖^2+ε^2 = logFactor ‖v‖ ε*‖1-v/(logFactor ‖v‖ ε:ℂ)‖^2 := by
  have hl := (logFactor_pos ‖v‖ ε).ne'
  have he := logFactor_equation ‖v‖ ε
  have hn := Complex.sq_norm v
  simp only [Complex.normSq_apply] at hn
  have hdiv : v/(logFactor ‖v‖ ε:ℂ)=( (logFactor ‖v‖ ε)⁻¹:ℝ) * v := by
    push_cast; ring
  rw [hdiv]
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,zero_sub,add_zero]
  field_simp at he ⊢
  nlinarith

lemma logFactor_ratio_bound {ε : ℝ} (he : ε ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ q ∈ Icc 0 A, q/logFactor q ε ≤ θ := by
  have hc : Continuous (fun q : ℝ => q/logFactor q ε) :=
    continuous_id.div (logFactor_continuous.comp (continuous_id.prodMk continuous_const))
      (fun q => (logFactor_pos q ε).ne')
  obtain ⟨q,hq,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hA) hc.continuousOn
  let θ := (1+q/logFactor q ε)/2
  have hr : q/logFactor q ε < 1 := (div_lt_one (logFactor_pos q ε)).mpr (logFactor_gt he)
  have hr0 : 0 ≤ q/logFactor q ε := div_nonneg hq.1 (logFactor_pos q ε).le
  refine ⟨θ,by dsimp [θ]; linarith,by dsimp [θ]; linarith,?_⟩
  intro r hr'
  exact (hmax hr').trans (by dsimp [θ]; linarith)

def logMean (ε : ℝ) (v : ℂ) : ℝ := Real.log (logFactor ‖v‖ ε)-Real.log (1+ε^2)
def logNormalized (ε : ℝ) (v : ℂ) : ℂ := v/(logFactor ‖v‖ ε:ℂ)
def logTerm (ε : ℝ) (n : ℕ) (v : ℂ) : ℝ := -2*((logNormalized ε v)^(n+1)).re/(n+1)
def logTruncation (ε : ℝ) (M : ℕ) (v : ℂ) : ℝ := logMean ε v+∑ n ∈ Finset.range M, logTerm ε n v

lemma logNormalized_norm_lt {ε : ℝ} (he : ε ≠ 0) (v : ℂ) : ‖logNormalized ε v‖ < 1 := by
  rw [logNormalized,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (logFactor_pos _ _)]
  exact (div_lt_one (logFactor_pos _ _)).mpr (logFactor_gt he)

lemma regularizedLog_hasSum {ε : ℝ} (he : ε ≠ 0) (v : ℂ) :
    HasSum (fun n => logTerm ε n v) (regularizedLog 1 ε v-logMean ε v) := by
  have hs := (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' (logNormalized_norm_lt he v))).mul_left (-2)
  have heq : Real.log (‖1-v‖^2+ε^2)=Real.log (logFactor ‖v‖ ε)+Real.log (‖1-logNormalized ε v‖^2) := by
    rw [logFactor_complex_identity]
    apply Real.log_mul (logFactor_pos _ _).ne'
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    intro hz
    have hh := congrArg norm (sub_eq_zero.mp hz)
    rw [norm_one] at hh
    exact (ne_of_lt (logNormalized_norm_lt he v)) hh.symm
  have hval : -2 * (-Complex.log (1-logNormalized ε v)).re = regularizedLog 1 ε v-logMean ε v := by
    rw [Complex.neg_re,Complex.log_re,regularizedLog_eq 1 ε v he]
    simp only [Complex.ofReal_one,one_mul,logMean]
    rw [heq,Real.log_pow]
    ring
  rw [hval] at hs
  apply hs.congr_fun
  intro n
  simp only [logTerm,Complex.div_re,Complex.add_re,Complex.natCast_re,Complex.one_re,
    Complex.add_im,Complex.natCast_im,Complex.one_im,add_zero,mul_zero,add_zero,
    Complex.normSq_apply]
  field_simp
  ring

lemma logTerm_bound {ε θ : ℝ} (hθ : 0 ≤ θ) {v : ℂ} (hv : ‖logNormalized ε v‖ ≤ θ) (n : ℕ) :
    |logTerm ε n v| ≤ 2*θ^(n+1) := by
  have hn : (1:ℝ) ≤ n+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
  calc
    _ = 2*|((logNormalized ε v)^(n+1)).re|/(n+1) := by
      simp only [logTerm,abs_div,abs_mul,abs_of_pos (by positivity : (0:ℝ)<n+1)]
      norm_num
    _ ≤ 2*‖(logNormalized ε v)^(n+1)‖/(n+1) := by gcongr; exact Complex.abs_re_le_norm _
    _ ≤ 2*θ^(n+1)/(n+1) := by rw [norm_pow]; gcongr
    _ ≤ 2*θ^(n+1) := div_le_self (by positivity) hn

lemma logTruncation_error {ε θ : ℝ} (he : ε ≠ 0) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    {v : ℂ} (hv : ‖logNormalized ε v‖ ≤ θ) (M : ℕ) :
    |regularizedLog 1 ε v-logTruncation ε M v| ≤ 2*θ^(M+1)/(1-θ) := by
  have hsum := regularizedLog_hasSum he v
  have htail : regularizedLog 1 ε v-logTruncation ε M v = ∑' n : ℕ, logTerm ε (n+M) v := by
    have h := hsum.summable.sum_add_tsum_nat_add M
    rw [hsum.tsum_eq] at h
    dsimp [logTruncation]
    linarith
  rw [htail,← Real.norm_eq_abs]
  have hbound : ∀ n : ℕ, ‖logTerm ε (n+M) v‖ ≤ (2*θ^(M+1))*θ^n := by
    intro n
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 2*θ^(n+M+1) := logTerm_bound hθ hv (n+M)
      _ = _ := by rw [show n+M+1=(M+1)+n by omega,pow_add]; ring
  have hg : Summable (fun n : ℕ => (2*θ^(M+1))*θ^n) := (summable_geometric_of_lt_one hθ hθ1).mul_left _
  have hn : Summable (fun n : ℕ => ‖logTerm ε (n+M) v‖) :=
    hg.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc
    _ ≤ ∑' n : ℕ, ‖logTerm ε (n+M) v‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, (2*θ^(M+1))*θ^n := hn.tsum_le_tsum hbound hg
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hθ hθ1]; rfl

lemma logNormalized_continuous (ε : ℝ) : Continuous (logNormalized ε) := by
  unfold logNormalized
  exact continuous_id.div
    (Complex.continuous_ofReal.comp (logFactor_continuous.comp (continuous_norm.prodMk continuous_const)))
    (fun v => Complex.ofReal_ne_zero.mpr (logFactor_pos _ _).ne')

lemma logMean_continuous (ε : ℝ) : Continuous (logMean ε) := by
  unfold logMean
  exact ((logFactor_continuous.comp (continuous_norm.prodMk continuous_const)).log
    (fun v => (logFactor_pos _ _).ne')).sub continuous_const

lemma logTerm_continuous (ε : ℝ) (n : ℕ) : Continuous (logTerm ε n) := by
  unfold logTerm
  exact (continuous_const.mul (Complex.continuous_re.comp ((logNormalized_continuous ε).pow _))).div_const _

lemma logTruncation_continuous (ε : ℝ) (M : ℕ) : Continuous (logTruncation ε M) := by
  unfold logTruncation
  exact (logMean_continuous ε).add (continuous_finsetSum _ (fun n _ => logTerm_continuous ε n))

end PinchedHartogs.BaseConstruction

end

end OAI
