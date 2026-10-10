import Mathlib
import OAI.Probability.SKValue.Equations.ForcedGenerator

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
lemma ForcedTest.source_measurable {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) {t:ℝ} (ht:t∈Icc (0:ℝ) T) :
    Measurable (forcedSource γ u V b p t) := by
  have h1:=((h.smooth t ht).continuous_deriv (by norm_num)).measurable
  have h2:Measurable (fun x ↦ deriv (deriv (V t)) x) := by
    have hh:=((h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)).measurable
    simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hh
  exact ((h.b_measurable t ht).add h2).const_mul (1/2:ℝ) |>.add
    (((h.p_measurable t ht).add ((h.drift_measurable t ht).mul h1)).const_mul (γ t))
lemma ForcedTest.source_bound {T K L:ℝ} {γ:ℝ → ℝ} {u V b p:ℝ → ℝ → ℝ}
    (h:ForcedTest T γ u V b p K L) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ) :
    |forcedSource γ u V b p t x| ≤ (1+2*γ T)*K := by
  have hb:|b t x+deriv (deriv (V t)) x| ≤ K+K :=
    (abs_add_le _ _).trans (add_le_add (h.b_bound t ht x) (h.second_bound t ht x))
  have hp:|p t x+u t x*deriv (V t) x| ≤ K+K := by
    apply (abs_add_le _ _).trans
    apply add_le_add (h.p_bound t ht x)
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (h.drift_bound t ht x) (h.first_bound t ht x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  unfold forcedSource
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (h.gamma_nonneg t ht)]
  norm_num only [abs_div,abs_one,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hγ:=h.gamma_mono ht ⟨ht.1.trans ht.2,le_rfl⟩ ht.2
  have hK:=h.K_nonneg
  have hmul:=mul_le_mul hp hγ (h.gamma_nonneg t ht) (by linarith : (0:ℝ) ≤ K+K)
  nlinarith
end SKValue

end

end OAI
