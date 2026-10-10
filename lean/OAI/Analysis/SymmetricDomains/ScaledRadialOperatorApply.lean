import Mathlib
import OAI.Analysis.SymmetricDomains.BishopDiscRadialExpansion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def radialPoint (t : ℝ) : ClosedDisc :=
  ⟨1-(max 0 (min 1 t) : ℝ),radial_mem_closedDisc (le_max_left _ _)
    (max_le (by norm_num) (min_le_left _ _))⟩

lemma radialPoint_coe {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (radialPoint t : ℂ) = 1-(t : ℂ) := by
  simp only [radialPoint,min_eq_right ht1,max_eq_right ht]

def schwarzDifference {k : ℕ} (z : ClosedDisc) : BoundarySpace k →L[ℝ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi (fun i =>
    (((ContinuousMap.evalCLM ℝ (M := ℂ) z)-(ContinuousMap.evalCLM ℝ (M := ℂ) (⟨0,by simp [ClosedDisc]⟩ : ClosedDisc))).comp
      realSchwarz).comp (ContinuousLinearMap.proj i))

lemma schwarzDifference_apply {k : ℕ} (z : ClosedDisc) (Y : BoundarySpace k) (i : Fin k) :
    schwarzDifference z Y i = realSchwarz (Y i) z-realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩ := rfl

lemma schwarzDifference_norm {k : ℕ} (z : ClosedDisc) :
    ‖schwarzDifference (k := k) z‖ ≤ 6 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro Y
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [schwarzDifference_apply]
  calc
    ‖realSchwarz (Y i) z-realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩‖ ≤
        ‖realSchwarz (Y i) z‖+‖realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩‖ := norm_sub_le _ _
    _ ≤ ‖realSchwarz (Y i)‖+‖realSchwarz (Y i)‖ :=
      add_le_add ((realSchwarz (Y i)).norm_coe_le_norm _) ((realSchwarz (Y i)).norm_coe_le_norm _)
    _ ≤ 3*‖Y i‖+3*‖Y i‖ := add_le_add (schwarz_norm _) (schwarz_norm _)
    _ ≤ 6*‖Y‖ := by have hi := norm_le_pi_norm Y i; nlinarith

def scaledRadialOperator {k : ℕ} (t : ℝ) : BoundarySpace k →L[ℝ] (Fin k → ℂ) :=
  (-(t/(1-t))) • schwarzDifference (radialPoint t)

lemma scaledRadialOperator_norm_tendsto {k : ℕ} :
    Tendsto (fun t : ℝ => ‖scaledRadialOperator (k := k) t‖) (𝓝 0) (𝓝 0) := by
  have hs : Tendsto (fun t : ℝ => |-(t/(1-t))| * 6) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ => |-(t/(1-t))| * 6) 0 := by fun_prop (disch := norm_num)
    simpa using hc.tendsto
  apply squeeze_zero (fun _ => norm_nonneg _) _ hs
  intro t
  rw [scaledRadialOperator,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (schwarzDifference_norm _) (abs_nonneg _)

lemma scaledRadialOperator_apply {k : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (Y : BoundarySpace k) (i : Fin k) :
    scaledRadialOperator t Y i =
      -(t : ℂ)/(1-(t : ℂ))*(discValue (Y i : Space) (1-(t : ℂ))-discValue (Y i : Space) 0) := by
  change (-(t/(1-t))) • (realSchwarz (Y i) (radialPoint t)-
    realSchwarz (Y i) ⟨0,by simp [ClosedDisc]⟩) = _
  have he : radialPoint t = ⟨1-(t : ℂ),radial_mem_closedDisc ht ht1⟩ :=
    Subtype.ext (radialPoint_coe ht ht1)
  rw [he]
  change (-(t/(1-t))) • (schwarz (Y i : Space) _-schwarz (Y i : Space) _) = _
  rw [← discValue_eq _ (radial_mem_closedDisc ht ht1),← discValue_eq _ (by simp [ClosedDisc])]
  simp only [Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_sub,
    Complex.ofReal_one,neg_div]

end Release061.Wiener

end

end OAI
