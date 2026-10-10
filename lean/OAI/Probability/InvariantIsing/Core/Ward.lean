import OAI.Probability.InvariantIsing.Haar.HaarDerivative
import OAI.Probability.IsingPerceptron.GaussianIntegration

namespace OAI

/-!
# Finite-volume Gibbs rotation identity

Differentiation of a normalized Gibbs average produces the observable
variation and its covariance with the Hamiltonian variation. Haar invariance
then gives their exact integral identity. The spin prior may have zero weights.
No limiting Ward equations or pressure bounds are assumed here.
-/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators Topology

namespace InvariantIsing

variable {S : Type*} [Fintype S]

/-- Finite normalized Gibbs expectation, for an arbitrary nonzero positive prior. -/
def gibbsAverage (w H A : S → ℝ) : ℝ :=
  ∑ σ, finiteGibbs w H σ * A σ

lemma abs_gibbsAverage_le {w : S → ℝ} (hw : GibbsReference w)
    (H A : S → ℝ) {K : ℝ} (hA : ∀ σ, |A σ| ≤ K) :
    |gibbsAverage w H A| ≤ K := finiteGibbs_average_bound hw H A hA

lemma measurable_gibbsAverage {Ω : Type*} [MeasurableSpace Ω]
    (w : S → ℝ) (H A : Ω → S → ℝ)
    (hH : ∀ σ, Measurable (fun ω => H ω σ))
    (hA : ∀ σ, Measurable (fun ω => A ω σ)) :
    Measurable (fun ω => gibbsAverage w (H ω) (A ω)) := by
  unfold gibbsAverage finiteGibbs finitePartition
  exact Finset.measurable_sum _ fun σ _ =>
    ((measurable_const.mul (hH σ).exp).div
      (Finset.measurable_sum _ fun τ _ => measurable_const.mul (hH τ).exp)).mul (hA σ)

/-- Derivative of a finite Gibbs expectation: the variation of the observable
plus its Gibbs covariance with the variation of the Hamiltonian. -/
lemma hasDerivAt_gibbsAverage {w : S → ℝ} (hw : GibbsReference w)
    {H A : ℝ → S → ℝ} {dH dA : S → ℝ} {t : ℝ}
    (hH : ∀ σ, HasDerivAt (fun s => H s σ) (dH σ) t)
    (hA : ∀ σ, HasDerivAt (fun s => A s σ) (dA σ) t) :
    HasDerivAt (fun s => gibbsAverage w (H s) (A s))
      (gibbsAverage w (H t) dA +
        gibbsAverage w (H t) (fun σ => A t σ * dH σ) -
        gibbsAverage w (H t) (A t) * gibbsAverage w (H t) dH) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (hasDerivAt_finiteGibbs hw hH σ).mul (hA σ))
  convert hd using 1
  · rfl
  · simp only [gibbsAverage]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    ring

lemma abs_gibbsVariation_le {w : S → ℝ} (hw : GibbsReference w)
    (H A dH dA : S → ℝ) {K L M : ℝ}
    (hK : 0 ≤ K)
    (hA : ∀ σ, |A σ| ≤ K) (hH : ∀ σ, |dH σ| ≤ L)
    (hdA : ∀ σ, |dA σ| ≤ M) :
    |gibbsAverage w H dA + gibbsAverage w H (fun σ => A σ * dH σ) -
      gibbsAverage w H A * gibbsAverage w H dH| ≤ M + 2 * K * L := by
  have ha := abs_gibbsAverage_le hw H A hA
  have hh := abs_gibbsAverage_le hw H dH hH
  have hda := abs_gibbsAverage_le hw H dA hdA
  have hprod := abs_gibbsAverage_le hw H (fun σ => A σ * dH σ) (fun σ => by
    rw [abs_mul]
    exact mul_le_mul (hA σ) (hH σ) (abs_nonneg _) hK)
  calc
    _ ≤ |gibbsAverage w H dA| + |gibbsAverage w H (fun σ => A σ * dH σ)| +
        |gibbsAverage w H A * gibbsAverage w H dH| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M + K * L + K * L := by
      rw [abs_mul]
      exact add_le_add (add_le_add hda hprod) (mul_le_mul ha hh (abs_nonneg _) hK)
    _ = M + 2 * K * L := by ring

/-- Exact finite-volume Haar Ward identity. All regularity assumptions concern
finite-dimensional derivatives; none assumes a limiting overlap identity. -/
theorem integral_gibbs_rotation_identity {N : ℕ}
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (R : ℝ → Orthogonal N) (hR : R 0 = 1)
    {w : S → ℝ} (hw : GibbsReference w)
    (H A : Orthogonal N → S → ℝ)
    (hHm : ∀ σ, Measurable (fun U => H U σ))
    (hAm : ∀ σ, Measurable (fun U => A U σ))
    (dH dA : ℝ → Orthogonal N → S → ℝ)
    (hdHm : ∀ σ, Measurable (fun U => dH 0 U σ))
    (hdAm : ∀ σ, Measurable (fun U => dA 0 U σ))
    (hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => H (R s * U) σ) (dH t U σ) t)
    (hAd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ,
      HasDerivAt (fun s => A (R s * U) σ) (dA t U σ) t)
    (K L M : ℝ) (hK : 0 ≤ K)
    (hAb : ∀ U σ, |A U σ| ≤ K)
    (hdHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dH t U σ| ≤ L)
    (hdAb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ σ, |dA t U σ| ≤ M) :
    (∫ U, gibbsAverage w (H U) (dA 0 U) +
      gibbsAverage w (H U) (fun σ => A U σ * dH 0 U σ) -
      gibbsAverage w (H U) (A U) * gibbsAverage w (H U) (dH 0 U) ∂μ) = 0 := by
  let f : Orthogonal N → ℝ := fun U => gibbsAverage w (H U) (A U)
  let f' : ℝ → Orthogonal N → ℝ := fun t U =>
    gibbsAverage w (H (R t * U)) (dA t U) +
      gibbsAverage w (H (R t * U)) (fun σ => A (R t * U) σ * dH t U σ) -
      gibbsAverage w (H (R t * U)) (A (R t * U)) *
        gibbsAverage w (H (R t * U)) (dH t U)
  have hm : Measurable f := measurable_gibbsAverage w H A hHm hAm
  have hi : Integrable f μ := (integrable_const K).mono' hm.aestronglyMeasurable
    (ae_of_all μ fun U => by
      simpa only [Real.norm_eq_abs] using
        (abs_gibbsAverage_le hw (H U) (A U) (hAb U)))
  have hm' : Measurable (f' 0) := by
    simp only [f', hR, one_mul]
    exact ((measurable_gibbsAverage w H (dA 0) hHm hdAm).add
      (measurable_gibbsAverage w H (fun U σ => A U σ * dH 0 U σ) hHm
        (fun σ => (hAm σ).mul (hdHm σ)))).sub
      ((measurable_gibbsAverage w H A hHm hAm).mul
        (measurable_gibbsAverage w H (dH 0) hHm hdHm))
  have hb : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1, ‖f' t U‖ ≤ M + 2 * K * L := by
    exact ae_of_all _ fun U t ht => by
      simpa only [f', Real.norm_eq_abs] using
        abs_gibbsVariation_le hw (H (R t * U)) (A (R t * U)) (dH t U) (dA t U)
          hK (hAb _) (hdHb U t ht) (hdAb U t ht)
  have hd : ∀ᵐ U ∂μ, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun s => f (R s * U)) (f' t U) t :=
    ae_of_all _ fun U t ht => hasDerivAt_gibbsAverage hw (hHd U t ht) (hAd U t ht)
  have he := integral_rotation_derivative_eq_zero μ R hR f hm hi f'
    hm'.aestronglyMeasurable (fun _ => M + 2 * K * L) (integrable_const _) hb hd
  simpa only [f', hR, one_mul] using he

end InvariantIsing

end

end OAI
