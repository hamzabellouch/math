import OAI.Probability.FreeIsing.Ising.CoordinateCompletion
import OAI.Probability.FreeIsing.Ising.CovarianceTotalEnergy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem covariance_integrals_hasSum_posterior
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0)
    (I : TreeVertex d → State d A → ℝ)
    (hI : ∀ u, MemLp (I u) 2 (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (heI : ∀ u, (∫ q, I u q ^ 2 ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) =
      ∫ p : ℝ × State d A, covariance beta B v u p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
          (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (hcI : ∀ u, (∫ q, posterior beta B v T q * I u q
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) =
      ∫ p : ℝ × State d A, covariance beta B v u p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
          (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (hoI : Pairwise fun u w => ∫ q, I u q * I w q
      ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)) = 0)
    (hM : MemLp (posterior beta B v T) 2
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))) :
    HasSum (fun u => (hI u).toLp (I u)) (hM.toLp (posterior beta B v T)) := by
  have he := covariance_timeEnergy_hasSum hμ hd hb hcrit ν hB hmB hcB v T
  apply FilteringRepresentationClosure.hasSum_toLp_of_cross_energy hM I hI hoI
  · simpa only [heI] using he.summable
  · intro u
    exact (hcI u).trans (heI u).symm
  · simpa only [heI] using he.tsum_eq.symm

theorem exists_posterior_integral_representation
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) (T : ℝ≥0) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    ∃ (X : ℕ → TreeVertex d → State d A → ℝ) (I : TreeVertex d → State d A → ℝ)
      (hI : ∀ u, MemLp (I u) 2 P) (hM : MemLp (posterior beta B v T) 2 P),
      (∀ n u, MemLp (X n u) 2 P) ∧
      (∀ n u, Tendsto (fun k => ∫ q,
        (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
          T k q - X n u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ u, Tendsto (fun n => ∫ q, (X n u q - I u q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ u, Measurable (I u)) ∧
      (∀ u, AEStronglyMeasurable[ArrayPosteriorStationarity.filtration B hmB T] (I u) P) ∧
      (∀ u, (∫ q, I u q ∂P) = 0) ∧
      HasSum (fun u => (hI u).toLp (I u)) (hM.toLp (posterior beta B v T)) ∧
      Tendsto (fun s : Finset (TreeVertex d) => ∫ q,
        ((∑ u ∈ s, I u q) - posterior beta B v T q) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨X, I, hX, haX, hmI, htI, hI, hzI, haI, heI, hcI, hoI⟩ :=
    exists_covariance_coordinate_integrals hμ ν hB hmB hcB v T
  have hM := posterior_memLp beta B hmB hcB
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) v T
  have hs := covariance_integrals_hasSum_posterior hμ hd hb hcrit ν hB hmB hcB
    v T I hI heI hcI hoI hM
  exact ⟨X, I, hI, hM, hX, haX, haI, hmI, htI, hzI, hs,
    PredictableL2.tendsto_integral_sq_error_of_hasSum I hI hM hs⟩

end Problem367.IsingInnovation

end

end OAI
