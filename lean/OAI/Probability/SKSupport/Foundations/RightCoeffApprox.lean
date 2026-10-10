import Mathlib
import OAI.Probability.SKSupport.Diffusion.FiniteFeedback

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat

lemma rightCoeff_eq_finiteCoeff (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) {t : ℝ}
    (hne : ∀ k < N, t ≠ ((k+1:ℕ):ℝ)*h) : rightCoeff c h N i t=finiteCoeff c h N i t := by
  induction N generalizing i t with
  | zero => rfl
  | succ N ih =>
    have hh : t ≠ (h:ℝ) := by simpa using hne 0 (by omega)
    rw [rightCoeff,finiteCoeff]
    by_cases ht : t < h
    · rw [ite_eq_left ht,ite_eq_left ht.le]
    · rw [ite_eq_right ht,ite_eq_right (by exact not_le.mpr (lt_of_le_of_ne (le_of_not_gt ht) hh.symm))]
      apply ih
      intro k hk he
      apply hne (k+1) (by omega)
      have he' := he
      push_cast at he' ⊢
      linarith

lemma rightCoeff_ae (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) :
    rightCoeff c h N i =ᵐ[volume] finiteCoeff c h N i := by
  have hn : ∀ᵐ t : ℝ, ∀ k : ℕ, t ≠ ((k+1:ℕ):ℝ)*h := by
    rw [ae_all_iff]
    intro k
    exact ae_iff.mpr (by simp)
  filter_upwards [hn] with t ht
  exact rightCoeff_eq_finiteCoeff c h N i (fun k _ => ht k)

lemma rightCoeff_intervalIntegrable (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (a b : ℝ) :
    IntervalIntegrable (rightCoeff c h N i) volume a b :=
  (finiteCoeff_intervalIntegrable c h N i a b).congr_ae (ae_restrict_of_ae (rightCoeff_ae c h N i).symm)

lemma finiteFeedback_bound_on {f : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) {T D : ℝ}
    (hD : ∀ s ∈ Icc (0:ℝ) T, finiteCoeff c h N 0 s ≤ D) :
    ∀ᵐ s ∂volume, ∀ _ : s ∈ Icc (0:ℝ) T, ∀ x, |(finiteFeedback hf hLip c h N 0).f s x| ≤ D := by
  filter_upwards [rightCoeff_ae c h N 0] with s hs hst x
  change |rightCoeff c h N 0 s*deriv (finiteValue c h f N 0 s) x| ≤ D
  rw [hs,abs_mul,abs_of_nonneg (finiteCoeff_nonneg c h N 0 s)]
  have hg := norm_deriv_le_of_lipschitz (finiteValue_lipschitz hLip c h N 0 s) (x₀ := x)
  have hb : |deriv (finiteValue c h f N 0 s) x| ≤ 1 := by simpa only [Real.norm_eq_abs,NNReal.coe_one] using hg
  exact (mul_le_mul_of_nonneg_left hb (finiteCoeff_nonneg c h N 0 s)).trans (by simpa using hD s hst)

end ZeroTemperatureSK

end
end

end OAI
