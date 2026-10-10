import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivativeBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridPrime
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedSmoothPullback
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightDerivConstants

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative
open Characters.RationalHistory HistoryGiantPriorGrid PrimeCellFreezing
open HistoryRepeatedSmoothPullback HistoryBulkCorrectedXiBounds

private theorem partition_logCurve_data {ι : Type*} [DecidableEq ι]
    (G : ℝ) (z : ι → ℝ) (i j : ι) :
    DifferentiableAt ℝ (fun t => smoothPartition
      (Real.log (Expr.logCurve (fun a => Real.exp (z a)) i t j)-G)) 0 ∧
    |deriv (fun t => smoothPartition
      (Real.log (Expr.logCurve (fun a => Real.exp (z a)) i t j)-G)) 0| ≤ partitionDerivativeConstant := by
  have he : (fun t => smoothPartition (Real.log
      (Expr.logCurve (fun a => Real.exp (z a)) i t j)-G)) =
      (fun t => smoothPartition (z j+(if j=i then t else 0)-G)) := by
    funext t
    simp only [Expr.logCurve,Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),Real.log_exp]
  rw [he]
  by_cases hji : j=i
  · simp only [ite_eq_left hji]
    have hd : HasDerivAt (fun t : ℝ => smoothPartition (z j+t-G))
        (deriv smoothPartition (z j-G)) 0 := by
      have hφ := (smoothPartition_contDiff.differentiable (by simp) (z j-G)).hasDerivAt
      convert hφ.comp_of_eq 0 (((hasDerivAt_const (0:ℝ) (z j)).add (hasDerivAt_id (0:ℝ))).sub_const G) (by simp) using 1 <;> simp [Function.comp_def]
    exact ⟨hd.differentiableAt,by rw [hd.deriv]; exact partition_deriv_le_constant _⟩
  · simp only [ite_eq_right hji,add_zero]
    exact ⟨differentiableAt_const _,by simpa only [deriv_const,abs_zero] using partitionDerivativeConstant_pos.le⟩

private theorem partition_abs_le_one (t : ℝ) : |smoothPartition t| ≤ 1 := by
  rw [abs_of_nonneg (smoothPartition_nonneg _)]
  exact smoothPartition_le_one _

private theorem norm_deriv_real_mul_le (c : ℝ → ℝ) (f : ℝ → ℂ) (A D : ℝ)
    (_hA : 0 ≤ A) (hD : 0 ≤ D) (hc : DifferentiableAt ℝ c 0)
    (hf : DifferentiableAt ℝ f 0) (hc0 : |c 0| ≤ 1) (hcd : |deriv c 0| ≤ D)
    (hf0 : ‖f 0‖ ≤ A) (hfd : ‖deriv f 0‖ ≤ A) :
    ‖deriv (fun t => (c t:ℂ)*f t) 0‖ ≤ (D+1)*A := by
  rw [(hc.hasDerivAt.ofReal_comp.fun_mul hf.hasDerivAt).deriv]
  calc
    _ ≤ |deriv c 0| *‖f 0‖+|c 0| *‖deriv f 0‖ := by
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
        norm_add_le (((deriv c 0:ℝ):ℂ)*f 0) ((c 0:ℂ)*deriv f 0)
    _ ≤ D*A+1*A := add_le_add
      (mul_le_mul hcd hf0 (norm_nonneg _) hD)
      (mul_le_mul hc0 hfd (norm_nonneg _) zero_le_one)
    _ = _ := by ring

private theorem raw_curve_differentiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ ∞ (fun z : ι → ℝ => f (fun j => Real.exp (z j))))
    (z : ι → ℝ) (i : ι) :
    DifferentiableAt ℝ (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0 := by
  apply differentiableAt_logCurve_comp f id _ i (fun j => Real.exp_pos _)
  simpa only [id_eq,Real.log_exp] using hf.differentiable (by simp) z

theorem primeCutoff_giant_bounds (G : ℝ) (f : (Bool → ℝ) → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ContDiff ℝ ∞ (fun z : Bool → ℝ => f (fun j => Real.exp (z j))) ∧
      ∀ z ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
        (∀ i, ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ A) ∧
        ‖f (fun j => Real.exp (z j))‖ ≤ A) :
    ContDiff ℝ ∞ (fun z : Bool → ℝ => primeCutoff G f (fun j => Real.exp (z j))) ∧
      ∀ z ∈ logRectangle (fun _ : Bool => G-1) (fun _ => G+1),
        (∀ i, ‖deriv (fun t => primeCutoff G f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          (2*partitionDerivativeConstant+1)*A) ∧
        ‖primeCutoff G f (fun j => Real.exp (z j))‖ ≤ A := by
  have ha (i : Bool) : ContDiff ℝ ∞ (fun z : Bool → ℝ =>
      (giantCell G (Real.exp (z i)):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((giantCell_contDiff G).comp (by fun_prop))
  refine ⟨((ha false).mul (ha true)).mul hf.1,?_⟩
  intro z hz
  constructor
  · intro i
    let a : ℝ → ℝ := fun t => smoothPartition (Real.log (Expr.logCurve (fun j => Real.exp (z j)) i t false)-G)
    let b : ℝ → ℝ := fun t => smoothPartition (Real.log (Expr.logCurve (fun j => Real.exp (z j)) i t true)-G)
    let F : ℝ → ℂ := fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)
    have ha := partition_logCurve_data G z i false
    have hb := partition_logCurve_data G z i true
    have ha0 : |a 0| ≤ 1 := partition_abs_le_one _
    have hb0 : |b 0| ≤ 1 := partition_abs_le_one _
    have hc0 : |a 0*b 0| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul ha0 hb0 (abs_nonneg _) zero_le_one
    have hcd : |deriv (fun t => a t*b t) 0| ≤ 2*partitionDerivativeConstant := by
      rw [(ha.1.hasDerivAt.fun_mul hb.1.hasDerivAt).deriv]
      calc
        _ ≤ |deriv a 0| * |b 0|+|a 0| * |deriv b 0| := by
          simpa only [abs_mul] using abs_add_le (deriv a 0*b 0) (a 0*deriv b 0)
        _ ≤ partitionDerivativeConstant*1+1*partitionDerivativeConstant :=
          add_le_add (mul_le_mul ha.2 hb0 (abs_nonneg _) partitionDerivativeConstant_pos.le)
            (mul_le_mul ha0 hb.2 (abs_nonneg _) zero_le_one)
        _ = _ := by ring
    have he : (fun t => primeCutoff G f (Expr.logCurve (fun j => Real.exp (z j)) i t)) =
        (fun t => ((a t*b t:ℝ):ℂ)*F t) := by
      funext t
      simp only [primeCutoff,giantCell_of_pos G (logCurve_positive _ (fun j => Real.exp_pos _) i t false),
        giantCell_of_pos G (logCurve_positive _ (fun j => Real.exp_pos _) i t true),a,b,F,Complex.ofReal_mul]
    rw [he]
    exact norm_deriv_real_mul_le _ F A (2*partitionDerivativeConstant) hA (by positivity [partitionDerivativeConstant_pos])
      (ha.1.mul hb.1) (raw_curve_differentiable f hf.1 z i) hc0 hcd
      (by simpa only [F,Expr.logCurve_zero] using (hf.2 z hz).2) ((hf.2 z hz).1 i)
  · rw [primeCutoff,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    have hc : |giantCell G (Real.exp (z false))| * |giantCell G (Real.exp (z true))| ≤ 1 := by
      rw [abs_of_nonneg (giantCell_bounds _ _).1,abs_of_nonneg (giantCell_bounds _ _).1]
      simpa only [one_mul] using mul_le_mul (giantCell_bounds G (Real.exp (z false))).2
        (giantCell_bounds G (Real.exp (z true))).2 (giantCell_bounds _ _).1 zero_le_one
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by simpa only [one_mul] using (hf.2 z hz).2)

theorem mixedCutoff_giant_bounds (G : ℝ) (f : (Option Unit → ℝ) → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ContDiff ℝ ∞ (fun z : Option Unit → ℝ => f (fun j => Real.exp (z j))) ∧
      ∀ z ∈ logRectangle (fun _ : Option Unit => G-1) (fun _ => G+1),
        (∀ i, ‖deriv (fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤ A) ∧
        ‖f (fun j => Real.exp (z j))‖ ≤ A) :
    ContDiff ℝ ∞ (fun z : Option Unit → ℝ => mixedGiantPrimeTest G f (fun j => Real.exp (z j))) ∧
      ∀ z ∈ logRectangle (fun _ : Option Unit => G-1) (fun _ => G+1),
        (∀ i, ‖deriv (fun t => mixedGiantPrimeTest G f (Expr.logCurve (fun j => Real.exp (z j)) i t)) 0‖ ≤
          (2*partitionDerivativeConstant+1)*A) ∧
        ‖mixedGiantPrimeTest G f (fun j => Real.exp (z j))‖ ≤ A := by
  have ha : ContDiff ℝ ∞ (fun z : Option Unit → ℝ => (smoothPartition (z (some ())-G):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (smoothPartition_contDiff.comp (by fun_prop))
  refine ⟨?_,?_⟩
  · simpa only [mixedGiantPrimeTest,Real.log_exp] using ha.mul hf.1
  intro z hz
  constructor
  · intro i
    let a : ℝ → ℝ := fun t => smoothPartition (Real.log (Expr.logCurve (fun j => Real.exp (z j)) i t (some ()))-G)
    let F : ℝ → ℂ := fun t => f (Expr.logCurve (fun j => Real.exp (z j)) i t)
    have ha := partition_logCurve_data G z i (some ())
    exact norm_deriv_real_mul_le a F A (2*partitionDerivativeConstant) hA (by positivity [partitionDerivativeConstant_pos])
      ha.1 (raw_curve_differentiable f hf.1 z i) (partition_abs_le_one _)
      (ha.2.trans (by linarith [partitionDerivativeConstant_pos]))
      (by simpa only [F,Expr.logCurve_zero] using (hf.2 z hz).2) ((hf.2 z hz).1 i)
  · rw [mixedGiantPrimeTest,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (partition_abs_le_one _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using (hf.2 z hz).2)

end Ostmann.Arithmetic.HistoryBulkReferenceGiantDerivative

end

end OAI
