import OAI.Probability.ContinuumTransition.ModifiedMoments

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

noncomputable def momentConstant (t β h : ℝ) : ℝ :=
  (2*Real.exp (Real.exp (h+β*(t^2/2)))+(Real.exp (Real.exp (h+β*(t^2/2))))^2)/(β*(t^2/8)/4)

theorem momentConstant_pos {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) (h : ℝ) :
    0 < momentConstant t β h := by unfold momentConstant; positivity

theorem cellLowerBound_pair_moment {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) (hVsym : ∀ x y, V x y = V y x)
    (h L : ℝ) (z w : cubeCells L) :
    grandIntegral (occupationPairFamily (gibbsFamily V β h) (latticeCell z) (latticeCell w)) (cube L)/
      grandIntegral (gibbsFamily V β h) (cube L) ≤ momentConstant t β h := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hF := cellLowerBound_gibbs_finite ht.le hβ.le hσ hR hs hsmall hV hVm hfin h
  have hfull (i : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ.le hσ hR hs hsmall
    hV hVm hfin h i (le_refl (β*(t^2/8)/4))
  exact grand_pair_moment_le (measurableSet_cube L) (gibbsFamily_nonneg V β h)
    (fun ι _ => measurable_gibbsFamily hVm β h ι)
    (measurableSet_latticeCell z) (measurableSet_latticeCell w) (by positivity)
    (hfull z) (hfull w) (grandIntegral_gibbs_pos V β h (cube L) hF.summable)
    (cellLowerBound_exponential_moment_bound ht hβ.le hσ hR hs hsmall hV hVm hVsym h L z)
    (cellLowerBound_exponential_moment_bound ht hβ.le hσ hR hs hsmall hV hVm hVsym h L w)

end ContinuumTemperature
end

end OAI
