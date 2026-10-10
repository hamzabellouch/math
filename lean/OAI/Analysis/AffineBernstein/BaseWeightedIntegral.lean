import Mathlib
import OAI.Analysis.AffineBernstein.BaseWeightedIBP

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrable_local_mul_test {f σ : E → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x) :
    Integrable (fun x => f x*σ x) μ := by
  apply integrable_of_support_subset_compact hc.isCompact
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport σ))
  have hfc : ContinuousOn f (tsupport σ) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  exact hfc.mul hσ.continuous.continuousOn

lemma integrable_local_mul_dirDeriv_test {f σ : E → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x) (v : E) :
    Integrable (fun x => f x*dirDeriv v σ x) μ := by
  have hs : tsupport (dirDeriv v σ) ⊆ tsupport σ := tsupport_fderiv_apply_subset ℝ v
  exact integrable_local_mul_test (contDiff_dirDeriv hσ v)
    (hc.of_isClosed_subset (isClosed_tsupport _) hs) (fun x hx => hf x (hs hx))

variable [FiniteDimensional ℝ E]

/- Base cofactor integration by parts. Only smoothness near the compact test
support is needed; no boundary regularity or global coefficient extension is assumed. -/
theorem integral_flatCofactor_trace {f β g σ : E → ℝ} (v : ι → E)
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hf : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ f x)
    (hβ : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ β x)
    (hg : ∀ x ∈ tsupport σ, ContDiffAt ℝ ∞ g x) :
    (∫ x, (β x*flatCofactorTrace f v g x+flatCofactorPair f v β g x)*σ x ∂μ) =
      -(∫ x, β x*flatCofactorPair f v σ g x ∂μ) := by
  let J := flatCofactorFlux f v β g
  have hJ (j : ι) (x : E) (hx : x ∈ tsupport σ) : ContDiffAt ℝ ∞ (J j) x :=
    contDiffAt_flatCofactorFlux (hf x hx) (hβ x hx) (hg x hx) v j
  have hi (j : ι) : Integrable (fun x => dirDeriv (v j) (J j) x*σ x) μ :=
    integrable_local_mul_test hσ hc (fun x hx => contDiffAt_dirDeriv (hJ j x hx) (v j))
  have hi' (j : ι) : Integrable (fun x => J j x*dirDeriv (v j) σ x) μ :=
    integrable_local_mul_dirDeriv_test hσ hc (hJ j) (v j)
  have hibp (j : ι) : (∫ x, dirDeriv (v j) (J j) x*σ x ∂μ) =
      -(∫ x, J j x*dirDeriv (v j) σ x ∂μ) := by
    have hh := integral_mul_fderiv_compact (μ := μ) (J j) σ (v j)
      (fun x hx => (hJ j x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
      (hσ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)) hc
    change (∫ x, J j x*dirDeriv (v j) σ x ∂μ) = -(∫ x, dirDeriv (v j) (J j) x*σ x ∂μ) at hh
    linarith
  calc
    _ = ∫ x, ∑ j, dirDeriv (v j) (J j) x*σ x ∂μ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [← Finset.sum_mul]
      by_cases hx : x ∈ tsupport σ
      · rw [flatCofactorFlux_divergence (hf x hx) (hβ x hx) (hg x hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = ∑ j, ∫ x, dirDeriv (v j) (J j) x*σ x ∂μ := integral_finsetSum _ (fun j _ => hi j)
    _ = -(∑ j, ∫ x, J j x*dirDeriv (v j) σ x ∂μ) := by simp only [hibp,Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ j, J j x*dirDeriv (v j) σ x ∂μ) := by rw [integral_finsetSum _ (fun j _ => hi' j)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [J,flatCofactorFlux,flatCofactorPair,Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

end AffineBernstein
end

end OAI
