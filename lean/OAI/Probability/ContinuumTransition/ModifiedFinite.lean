import OAI.Probability.ContinuumTransition.ModifiedInsertion

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem cellLowerBound_gibbs_moment_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) (z : Lattice)
    {c : ℝ} (hc : c ≤ β*(t^2/8)/4) :
    GrandFinite (momentFamily
      (gibbsFamily V β h) (latticeCell z) c) D := by
  apply GrandFinite.of_bound _ hDfin
    (fun ι _ => measurable_momentFamily _ (measurableSet_latticeCell z) c (measurable_gibbsFamily hVm β h ι))
    (momentFamily_nonneg _ (gibbsFamily_nonneg _ β h) _ _)
  intro ι _ x
  apply gibbs_moment_stable_bound _ β h (t^2/2) c _ x
  have he := mul_le_mul_of_nonneg_left (cellLowerBound_moment_energy ht hσ hR hs hsmall hV x z) hβ
  have hcc := mul_le_mul_of_nonneg_right hc (sq_nonneg (occupation (latticeCell z) x))
  nlinarith only [he, hcc]

theorem cellLowerBound_gibbs_finite {t β : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) {D : Set Space} (hDfin : volume D ≠ ⊤) (h : ℝ) :
    GrandFinite (gibbsFamily V β h) D := by
  have h0 : (0 : ℝ) ≤ β*(t^2/8)/4 := by positivity
  have hh := cellLowerBound_gibbs_moment_finite ht hβ hσ hR hs hsmall hV hVm hDfin h (fun _ => 0) h0
  have he : momentFamily (gibbsFamily V β h)
      (latticeCell (fun _ => 0)) 0 = gibbsFamily V β h := by
    funext ι inst x
    simp only [momentFamily, zero_mul, Real.exp_zero, mul_one]
  rw [he] at hh
  exact hh

end ContinuumTemperature
end

end OAI
