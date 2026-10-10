import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.Divergence

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation.FiniteEntropy

lemma mul_log_div_scaled {x c p : ℝ} (hx : 0 ≤ x) (hc : 0 < c) (hp : 0 < p) :
    c*((x/c)*Real.log ((x/c)/p)) = x*Real.log (x/p)-x*Real.log c := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  · rw [Real.log_div (div_pos hx hc).ne' hp.ne', Real.log_div hx.ne' hc.ne',
      Real.log_div hx.ne' hp.ne']
    field_simp
    ring

lemma binaryDivergence_mass_split {l r p : ℝ} (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hp : p ∈ Set.Ioo 0 1) :
    (l+r)*binaryDivergence (r/(l+r)) p +(l+r)*Real.log (l+r) =
      l*Real.log l+r*Real.log r-l*Real.log (1-p)-r*Real.log p := by
  by_cases hzero : l+r = 0
  · have hl0 : l = 0 := by linarith
    have hr0 : r = 0 := by linarith
    simp [hl0, hr0]
  · have hpos : 0 < l+r := lt_of_le_of_ne (add_nonneg hl hr) (Ne.symm hzero)
    have hcomp : 1-r/(l+r) = l/(l+r) := by field_simp; ring
    have h1 := mul_log_div_scaled hr hpos hp.1
    have h2 := mul_log_div_scaled hl hpos (sub_pos.mpr hp.2)
    unfold binaryDivergence
    rw [hcomp, mul_add, h1, h2, mul_log_div_eq hp.1.ne',
      mul_log_div_eq (sub_pos.mpr hp.2).ne']
    ring

variable {X : Type*} [Fintype X]
lemma divergence_scale_reference (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hs : ∀ x, 0 < P x → 0 < R x) {c : ℝ} (hc : 0 < c) :
    divergence P (fun x => c*R x) = divergence P R - (∑ x, P x)*Real.log c := by
  have ht (x : X) : P x*Real.log (P x/(c*R x)) =
      P x*Real.log (P x/R x)-P x*Real.log c := by
    rcases eq_or_lt_of_le (hP x) with hz | hp
    · simp [← hz]
    · have hr := hs x hp
      rw [Real.log_div hp.ne' (mul_pos hc hr).ne', Real.log_mul hc.ne' hr.ne',
        Real.log_div hp.ne' hr.ne']
      ring
  simp only [divergence, ht, Finset.sum_sub_distrib, ← Finset.sum_mul]

end CriticalPercolation.FiniteEntropy

end
end

end OAI
