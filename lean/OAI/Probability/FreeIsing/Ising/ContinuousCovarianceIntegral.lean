import OAI.Probability.FreeIsing.Brownian.ContinuousRowCompletion
import OAI.Probability.FreeIsing.Gibbs.CovarianceNativeRowCauchy
import OAI.Probability.FreeIsing.Ising.InnovationIndependence
import OAI.Probability.FreeIsing.Ising.MixedFiltering

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem finiteCovariance_fullTime_interval_energy_cauchy
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) {T : ℝ} (hT : 0 ≤ T) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    (∀ n, Summable (fun u => ∫ t in (0 : ℝ)..T,
      ∫ q, finiteCovariance beta B v u n t.toNNReal q ^ 2 ∂P)) ∧
    (∀ n k, Summable (fun u => ∫ t in (0 : ℝ)..T,
      ∫ q, (finiteCovariance beta B v u n t.toNNReal q -
        finiteCovariance beta B v u k t.toNNReal q) ^ 2 ∂P)) ∧
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∑' u, ∫ t in (0 : ℝ)..T,
        ∫ q, (finiteCovariance beta B v u n t.toNNReal q -
          finiteCovariance beta B v u k t.toNNReal q) ^ 2 ∂P) < ε := by
  have h := hμ.finiteGibbsCovariance_fullTime_interval_energy_cauchy
    hd hb hcrit (fun _ : TreeVertex d => ν) (fun _ => hB)
    (fun _ => hmB) (fun _ => hcB) v hT
  simpa only [finiteCovariance, plantedArrayObservation,
    ArrayPosteriorStationarity.spinArray, add_comm] using h

theorem exists_continuous_covariance_integral
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    ∃ (I : ℕ → TreeVertex d → ℝ≥0 → State d A → ℝ)
      (Y : ℕ → ℝ≥0 → State d A → ℝ) (Z : ℝ≥0 → State d A → ℝ)
      (hI2 : ∀ n u t, MemLp (I n u t) 2 P)
      (hY2 : ∀ n t, MemLp (Y n t) 2 P) (_hZ2 : ∀ t, MemLp (Z t) 2 P),
      (∀ n, IsStronglyPredictable F (Y n) ∧ Martingale (Y n) F P ∧
        (∀ᵐ q ∂P, Continuous (fun t => Y n t q))) ∧
      (∀ n u (N : ℕ), 0 < N → Tendsto (fun k => ∫ q,
        (BrownianGrid.uniformSum (innovation beta B u) (finiteCovariance beta B v u n)
          N k q - I n u N q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ n t, HasSum (fun u => (hI2 n u t).toLp (I n u t))
        ((hY2 n t).toLp (Y n t))) ∧
      (∀ n t, (∫ q, Y n t q ^ 2 ∂P) =
        ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) ∧
      (∀ n m (N : ℕ), 0 < N → (∫ q, (Y n N q - Y m N q) ^ 2 ∂P) =
        ∑' u, ∫ s in (0 : ℝ)..(N : ℝ), ∫ q,
          (finiteCovariance beta B v u n s.toNNReal q -
            finiteCovariance beta B v u m s.toNNReal q) ^ 2 ∂P) ∧
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ q ∂P, Continuous (fun t => Z t q)) ∧ Z 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ q, Z t q ∂P) = 0) ∧
      (∀ t, Tendsto (fun n => ∫ q, (Y n t q - Z t q) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ t : ℝ≥0, Tendsto (fun n => ∑' u, ∫ s in (0 : ℝ)..(t : ℝ),
        ∫ q, finiteCovariance beta B v u n s.toNNReal q ^ 2 ∂P) atTop
          (𝓝 (∫ q, Z t q ^ 2 ∂P))) ∧
      (∀ T, Tendsto (fun n => ∫ q,
        MartingaleStrongMaximal.maximalSquare (Y n - Z) T q ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hW (u : TreeVertex d) := isBrownianReal_innovation hμ ν hB hmB hcB u
  have hAd (u : TreeVertex d) :=
    (innovation_martingale hμ ν hB hmB hcB u).stronglyAdapted
  have hcross (s t : ℝ≥0) (hst : s ≤ t) : Pairwise fun u w =>
      IndepFun (fun q => innovation beta B u t q - innovation beta B u s q)
        (fun q => innovation beta B w t q - innovation beta B w s q) P := by
    intro u w huw
    exact (innovation_increment_law_and_indep hμ ν hB hmB hcB
      (Y := fun _ => ()) s t hst measurable_const).2.1.indepFun huw
  have hrow (N : ℕ) := finiteCovariance_fullTime_interval_energy_cauchy
    hd hμ hb hcrit ν hB hmB hcB v (Nat.cast_nonneg N)
  exact BrownianArrayFiltration.exists_global_continuous_integral_limit_of_row_energy_cauchy
    (fun u => (hW u).toIsPreBrownianReal) hAd
    (innovation_increment_indep_filtration hμ ν hB hmB hcB) hcross
    (fun u => (hW u).cont)
    (fun n u => finiteCovariance beta B v u n)
    (fun n u => finiteCovariance_stronglyAdapted beta B hmB v u n)
    (fun n u => Eventually.of_forall (finiteCovariance_continuous beta B hcB v u n))
    (fun _ _ => 2) (fun _ _ => by norm_num)
    (fun n u => Eventually.of_forall (fun q t => finiteCovariance_abs_le_two beta B v u n t q))
    (fun n N => (hrow N).1 n) (fun N _hN => (hrow N).2.2)

end Problem367.IsingInnovation

end

end OAI
