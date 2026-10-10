import OAI.Probability.FreeIsing.Ising.CoordinateIntegrals
import OAI.Probability.FreeIsing.Ising.CovarianceTimeL2

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem exists_covariance_coordinate_integrals
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let Q := (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod P
    let F := ArrayPosteriorStationarity.filtration B hmB
    ∃ (X : ℕ → TreeVertex d → State d A → ℝ) (I : TreeVertex d → State d A → ℝ),
      (∀ n u, MemLp (X n u) 2 P) ∧
      (∀ n u, Tendsto (fun k => ∫ q,
        (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
          T k q - X n u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ u, Measurable (I u)) ∧
      (∀ u, AEStronglyMeasurable[F T] (I u) P) ∧
      (∀ u, MemLp (I u) 2 P) ∧
      (∀ u, (∫ q, I u q ∂P) = 0) ∧
      (∀ u, Tendsto (fun n => ∫ q, (X n u q - I u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ u, (∫ q, I u q ^ 2 ∂P) =
        ∫ p : ℝ × State d A, covariance beta B v u p.1.toNNReal p.2 ^ 2 ∂Q) ∧
      (∀ u, (∫ q, posterior beta B v T q * I u q ∂P) =
        ∫ p : ℝ × State d A, covariance beta B v u p.1.toNNReal p.2 ^ 2 ∂Q) ∧
      Pairwise (fun u w => ∫ q, I u q * I w q ∂P = 0) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let τ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  let Q := τ.prod P
  let F := ArrayPosteriorStationarity.filtration (d := d) B hmB
  let G (n : ℕ) (u : TreeVertex d) (p : ℝ × State d A) :=
    finiteCovariance beta B v u n p.1.toNNReal p.2
  let C (u : TreeVertex d) (p : ℝ × State d A) :=
    covariance beta B v u p.1.toNNReal p.2
  have hG (n : ℕ) (u : TreeVertex d) : MemLp (G n u) 2 Q :=
    memLp_finiteCovariance_time beta B hmB hcB P τ v u n
  have hC (u : TreeVertex d) : MemLp (C u) 2 Q :=
    memLp_covariance_time beta B hmB hcB P τ v u
  have hW (u : TreeVertex d) :=
    (isBrownianReal_innovation hμ ν hB hmB hcB u).toIsPreBrownianReal
  have hAd (u : TreeVertex d) :=
    (innovation_martingale hμ ν hB hmB hcB u).stronglyAdapted
  have hind (u : TreeVertex d) (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past
      (innovation_increment_indep_filtration hμ ν hB hmB hcB s t hst) u
  have hH (n : ℕ) (u : TreeVertex d) :=
    finiteCovariance_stronglyAdapted beta B hmB v u n
  have hcH (n : ℕ) (u : TreeVertex d) :
      ∀ᵐ q ∂P, Continuous (fun t => finiteCovariance beta B v u n t q) :=
    Eventually.of_forall (finiteCovariance_continuous beta B hcB v u n)
  have hbH (n : ℕ) (u : TreeVertex d) :
      ∀ᵐ q ∂P, ∀ t, |finiteCovariance beta B v u n t q| ≤ 2 :=
    Eventually.of_forall (fun q t => finiteCovariance_abs_le_two beta B v u n t q)
  obtain ⟨X, htX, hX, hzX, haX⟩ :=
    exists_finiteCovariance_integrals hμ ν hB hmB hcB v T
  have hiso (n : ℕ) (u : TreeVertex d) :
      (∫ q, X n u q ^ 2 ∂P) = ∫ p, G n u p ^ 2 ∂Q := by
    calc
      _ = ∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
          finiteCovariance beta B v u n r.toNNReal q ^ 2 ∂P :=
        BrownianFiltrationGrid.uniform_meanSquare_limit_isometry
          (hW u) (hAd u) (hind u) _ (hH n u) (hcH n u)
          (by norm_num) (hbH n u) T (hX n u) (haX n u)
      _ = _ := interval_integral_eq_timeSpace T (hG n u).integrable_sq
  have hpair (u : TreeVertex d) (n k : ℕ) :
      (∫ q, (X n u q - X k u q) ^ 2 ∂P) =
        ∫ p, (G n u p - G k u p) ^ 2 ∂Q := by
    calc
      _ = ∫ r in (0 : ℝ)..(T : ℝ), ∫ q,
          (finiteCovariance beta B v u n r.toNNReal q -
            finiteCovariance beta B v u k r.toNNReal q) ^ 2 ∂P :=
        BrownianFiltrationGrid.uniform_meanSquare_difference_isometry
          (hW u) (hAd u) (hind u) _ _ (hH n u) (hH k u) (hcH n u) (hcH k u)
          (by norm_num) (by norm_num) (hbH n u) (hbH k u) T
          (hX n u) (hX k u) (haX n u) (haX k u)
      _ = _ := interval_integral_eq_timeSpace T ((hG n u).sub (hG k u)).integrable_sq
  have htest (u : TreeVertex d) (n : ℕ) :
      (∫ q, posterior beta B v T q * X n u q ∂P) = ∫ p, C u p * G n u p ∂Q := by
    rw [finiteCovariance_integral_cross hμ ν hB hmB hcB v u n T (hX n u) (haX n u)]
    have he := interval_integral_eq_timeSpace T ((hG n u).integrable_mul (hC u))
    simpa only [G, C, Pi.mul_apply, mul_comm] using he
  have hex (u : TreeVertex d) :=
    FilteringRepresentationClosure.exists_terminal_limit_of_coefficient_approximation
      F T (posterior_memLp beta B hmB hcB P v T)
      (fun n => X n u) (fun n => G n u) (C u)
      (fun n => hX n u) (fun n => (htX n u).aestronglyMeasurable)
      (fun n => hzX n u) (fun n => hG n u) (hC u)
      (finiteCovariance_tendsto_timeMeanSquare hμ ν hB hmB hcB v u T)
      (hpair u) (fun n => hiso n u) (htest u)
  choose I hmI htI hI hzI haI heI hcI using hex
  refine ⟨X, I, hX, haX, hmI, htI, hI, hzI, haI, heI, hcI, ?_⟩
  apply FilteringRepresentationClosure.pairwise_orthogonal_of_meanSquare_limits hX hI haI
  intro n
  exact finiteCovariance_integrals_orthogonal hμ ν hB hmB hcB v n T (hX n) (haX n)

end Problem367.IsingInnovation

end

end OAI
