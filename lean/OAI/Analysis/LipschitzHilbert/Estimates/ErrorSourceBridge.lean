import OAI.Analysis.LipschitzHilbert.Estimates.ActualErrorSource
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalErrorSources
import OAI.Analysis.LipschitzHilbert.Trees.SourceParameters

namespace OAI

/-! Construction of the line error data from the manuscript's actual
two-coordinate direction profile and common vertical averaging kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def actualErrorSources {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2 : ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) : LineErrorSources N := by
  let K := J+4*E
  let F := fun (j : Fin N) (p : ℝ × ℝ) =>
    A * errorSourceProfile c (C' * ((2 : ℝ)^E)^4) (a*(2 : ℝ)^j.val) |direction p-t|
  have hR : C' * ((2 : ℝ)^E)^4 ≤ c*(2 : ℝ)^K := by
    have hp : (2 : ℝ)^(4*E) = ((2 : ℝ)^E)^4 := by rw [Nat.mul_comm, pow_mul]
    apply (mul_le_mul_of_nonneg_right hC (by positivity : 0 ≤ ((2 : ℝ)^E)^4)).trans_eq
    dsimp [K]
    rw [pow_add,hp]
    ring
  have hF (j : Fin N) : Measurable (F j) := by
    apply Measurable.const_mul
    apply errorSourceProfile_measurable
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hdirection.sub measurable_const).norm
  have hF0 (j : Fin N) (p : ℝ × ℝ) : 0 ≤ F j p :=
    mul_nonneg hA (errorSourceProfile_nonneg c _ _ _ (by positivity) (abs_nonneg _))
  have hFb (j : Fin N) (p : ℝ × ℝ) : F j p ≤ A*(1+c) :=
    mul_le_mul_of_nonneg_left (errorSourceProfile_bound c _ _ _ hc (by positivity) (abs_nonneg _)) hA
  have hFs (p : ℝ × ℝ) : (∑ j, F j p) ≤ A*((K+1 : ℕ)+4*c) := by
    dsimp [F]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_errorSourceProfile N K a c _ _ ha hc (abs_nonneg _) hR) hA
  exact verticalErrorSources F hF topLength W y (A*(1+c)) (A*((K+1 : ℕ)+4*c))
    hL hW (by positivity) (by positivity) hF0 hFb hFs

theorem actualErrorSources_source {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2 : ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) (j : Fin N) (x : ℝ) :
    (actualErrorSources J E direction hdirection t a c C' A topLength W y ha hc hA hC hL hW).source j x =
      positiveConvolution W (fun z => A * errorSourceProfile c (C' * ((2 : ℝ)^E)^4)
        (a*(2 : ℝ)^j.val) |direction (x,z)-t|) y := rfl

theorem actualErrorSources_log_sumBound {N : ℕ} (J E : ℕ) (direction : ℝ × ℝ → ℝ)
    (hdirection : Measurable direction) (t a c C' A topLength W y : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hA : 0 ≤ A)
    (hC : C' ≤ c*(2 : ℝ)^J) (hL : 0 < topLength) (hW : 0 < W) :
    (actualErrorSources (N := N) J E direction hdirection t a c C' A topLength W y ha hc hA hC hL hW).sumBound =
      (A * ((J+1 : ℕ)+4*c+(4/Real.log 2)*Real.log ((2 : ℝ)^E))) * Real.pi := by
  change (A*((J+4*E+1 : ℕ)+4*c))*Real.pi = _
  rw [Real.log_pow]
  push_cast
  field_simp
  ring

theorem source_branching_eq_two_pow (L : ℝ) :
    SourceParameters.branching L =
      (2 : ℝ)^(SourceParameters.stepExponent L * SourceParameters.blockCount L) := by
  simp only [SourceParameters.branching, SourceParameters.step, pow_mul]

end LipschitzHilbert

end

end OAI
