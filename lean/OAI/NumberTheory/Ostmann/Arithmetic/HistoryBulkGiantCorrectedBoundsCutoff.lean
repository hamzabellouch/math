import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkGiantCorrectedBoundsSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantPriorGridPrime

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped ContDiff
namespace Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds
open HistoryBulkIntegralReplacement HistoryGiantPriorGrid PrimeCellFreezing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bulkBounds_const_mul {k : ℕ} {L C : ℝ} {f : (ι→ℝ)→ℂ}
    (hf : BulkBounds k L C f) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    BulkBounds k L C (fun x=>c*f x) := by
  refine ⟨fun z hz=>(hf.differentiable z hz).const_mul c,?_,?_⟩
  · intro z hz i
    rw [deriv_const_mul_field, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hf.derivative z hz i)
  · intro z hz
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hf.norm z hz)

def primeJointCutoff (G : ℝ) (f : (Bool→ℝ)→(ι→ℝ)→ℂ)
    (u : Bool→ℝ) (x : ι→ℝ) : ℂ := primeCutoff G (fun v=>f v x) u

def mixedJointCutoff (G : ℝ) (f : (Option Unit→ℝ)→(ι→ℝ)→ℂ)
    (u : Option Unit→ℝ) (x : ι→ℝ) : ℂ := mixedGiantPrimeTest G (fun v=>f v x) u

theorem primeJointCutoff_bulkBounds {k : ℕ} {L C : ℝ} (G : ℝ)
    (f : (Bool→ℝ)→(ι→ℝ)→ℂ) (u : Bool→ℝ) (hf : BulkBounds k L C (f u)) :
    BulkBounds k L C (primeJointCutoff G f u) := by
  apply bulkBounds_const_mul hf
  rw [norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (giantCell_bounds G (u false)).1,
    abs_of_nonneg (giantCell_bounds G (u true)).1]
  exact (mul_le_mul_of_nonneg_right (giantCell_bounds G (u false)).2
    (giantCell_bounds G (u true)).1).trans (by simpa using (giantCell_bounds G (u true)).2)

theorem mixedJointCutoff_bulkBounds {k : ℕ} {L C : ℝ} (G : ℝ)
    (f : (Option Unit→ℝ)→(ι→ℝ)→ℂ) (u : Option Unit→ℝ) (hf : BulkBounds k L C (f u)) :
    BulkBounds k L C (mixedJointCutoff G f u) := by
  apply bulkBounds_const_mul hf
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothPartition_nonneg _)]
  exact smoothPartition_le_one _

omit [DecidableEq ι] in
theorem primeJointCutoff_log_contDiff (G : ℝ) (f : (Bool→ℝ)→(ι→ℝ)→ℂ)
    (hf : ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(ι→ℝ)=>
      f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))) :
    ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(ι→ℝ)=>
      primeJointCutoff G f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) := by
  have ha : ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(ι→ℝ)=>
      (giantCell G (Real.exp (z.1 false)):ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp ((giantCell_contDiff G).comp (by fun_prop))
  have hb : ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(ι→ℝ)=>
      (giantCell G (Real.exp (z.1 true)):ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp ((giantCell_contDiff G).comp (by fun_prop))
  exact (ha.mul hb).mul hf

omit [DecidableEq ι] in
theorem mixedJointCutoff_log_contDiff (G : ℝ) (f : (Option Unit→ℝ)→(ι→ℝ)→ℂ)
    (hf : ContDiff ℝ ∞ (fun z : (Option Unit→ℝ)×(ι→ℝ)=>
      f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))) :
    ContDiff ℝ ∞ (fun z : (Option Unit→ℝ)×(ι→ℝ)=>
      mixedJointCutoff G f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) := by
  have ha : ContDiff ℝ ∞ (fun z : (Option Unit→ℝ)×(ι→ℝ)=>
      (smoothPartition (z.1 (some ())-G):ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (smoothPartition_contDiff.comp (by fun_prop))
  simpa only [mixedJointCutoff,mixedGiantPrimeTest,Real.log_exp] using ha.mul hf

theorem primeJointCutoff_joint_bounds {k : ℕ} {L C : ℝ} (G : ℝ)
    (f : (Bool→ℝ)→(ι→ℝ)→ℂ)
    (hf : ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(ι→ℝ)=>
        f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
      ∀z∈logRectangle (fun _=>G-1) (fun _=>G+1),
        BulkBounds k L C (f (fun i=>Real.exp (z i)))) :
    ContDiff ℝ ∞ (fun z : (Bool→ℝ)×(ι→ℝ)=>
        primeJointCutoff G f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
      ∀z∈logRectangle (fun _=>G-1) (fun _=>G+1),
        BulkBounds k L C (primeJointCutoff G f (fun i=>Real.exp (z i))) :=
  ⟨primeJointCutoff_log_contDiff G f hf.1,
    fun z hz=>primeJointCutoff_bulkBounds G f _ (hf.2 z hz)⟩

theorem mixedJointCutoff_joint_bounds {k : ℕ} {L C : ℝ} (G : ℝ)
    (f : (Option Unit→ℝ)→(ι→ℝ)→ℂ)
    (hf : ContDiff ℝ ∞ (fun z : (Option Unit→ℝ)×(ι→ℝ)=>
        f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
      ∀z∈logRectangle (fun _=>G-1) (fun _=>G+1),
        BulkBounds k L C (f (fun i=>Real.exp (z i)))) :
    ContDiff ℝ ∞ (fun z : (Option Unit→ℝ)×(ι→ℝ)=>
        mixedJointCutoff G f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i))) ∧
      ∀z∈logRectangle (fun _=>G-1) (fun _=>G+1),
        BulkBounds k L C (mixedJointCutoff G f (fun i=>Real.exp (z i))) :=
  ⟨mixedJointCutoff_log_contDiff G f hf.1,
    fun z hz=>mixedJointCutoff_bulkBounds G f _ (hf.2 z hz)⟩

end Ostmann.Arithmetic.HistoryBulkGiantCorrectedBounds

end

end OAI
