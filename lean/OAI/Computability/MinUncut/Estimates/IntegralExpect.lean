import Mathlib
import OAI.Computability.MinUncut.Estimates.Basic

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma integral_expect {T Ω : Type*} [Fintype T] [MeasurableSpace Ω] {μ : Measure Ω}
    (f : T → Ω → ℝ) (hf : ∀ t, Integrable (f t) μ) :
    (∫ x, (𝔼 t, f t x) ∂μ) = 𝔼 t, ∫ x, f t x ∂μ := by
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _ (fun t _ => hf t)]

lemma integral_norm_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, |f x| * |g x| ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) * Real.sqrt (∫ x, g x^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num : (2:ℝ).HolderConjugate 2)
    (by simpa using hf) (by simpa using hg)
  simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using h

variable {ι : Type*} [Fintype ι]

lemma psi_l1 (I : ι → ℕ) : (∫ x, |psi I x| ∂γpi ι) ≤ 1 := by
  have h := integral_norm_mul_le_sqrt (memLp_psi I)
    (memLp_const (1:ℝ) (p:=2) (μ:=γpi ι))
  have hn : (∫ x, psi I x^2 ∂γpi ι) = 1 := by simpa [sq] using psi_product I I
  simpa [hn] using h

end MinUncut.GaussianHermite

end

end OAI
