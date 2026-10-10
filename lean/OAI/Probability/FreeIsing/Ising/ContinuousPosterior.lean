import OAI.Probability.FreeIsing.Ising.ContinuousCovarianceIntegral
import OAI.Probability.FreeIsing.Ising.FiniteCovarianceEnergy
import OAI.Probability.FreeIsing.Ising.PosteriorIntegralRepresentation
import OAI.Probability.FreeIsing.Spectral.OrthogonalRowIdentification

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.IsingInnovation

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

theorem posterior_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    Martingale (posterior beta B v) (ArrayPosteriorStationarity.filtration B hmB)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  have h := martingale_condExp (fun q : State d A => spinSign (q.1 v))
    (ArrayPosteriorStationarity.filtration B hmB)
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
  exact h.congr (posterior_progressive beta B hmB hcB v).stronglyAdapted
    (fun t => (posterior_eq_condExp hμ ν hB hmB t v).symm)

theorem ae_eq_posterior_of_integer
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) {Z : ℝ≥0 → State d A → ℝ}
    (hZ : Martingale Z (ArrayPosteriorStationarity.filtration B hmB)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))))
    (he : ∀ N : ℕ, 0 < N → Z N =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior beta B v N) (t : ℝ≥0) :
    Z t =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      posterior beta B v t := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  have hN0 : 0 < N := by
    have hn : (0 : ℝ≥0) < (N : ℝ≥0) := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ t from zero_le) hN
    exact_mod_cast hn
  exact (hZ.condExp_ae_eq hN.le).symm.trans
    ((condExp_congr_ae (he N hN0)).trans
      ((posterior_martingale hμ ν hB hmB hcB v).condExp_ae_eq hN.le))

theorem exists_continuous_posterior
    (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (ν : Measure A) {B : ℝ≥0 → A → ℝ} (hB : IsPreBrownianReal B ν)
    (hmB : ∀ t, Measurable (B t)) (hcB : ∀ a, Continuous (fun t => B t a))
    (v : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F := ArrayPosteriorStationarity.filtration B hmB
    ∃ Z : ℝ≥0 → State d A → ℝ,
      IsStronglyPredictable F Z ∧ Martingale Z F P ∧
      (∀ᵐ q ∂P, Continuous (fun t => Z t q)) ∧
      (∀ t, MemLp (Z t) 2 P) ∧ Z 0 =ᵐ[P] 0 ∧
      ∀ t, Z t =ᵐ[P] posterior beta B v t := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let : IsProbabilityMeasure ν := hB.isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  obtain ⟨J, Y, Z, hJ, hY, hZ, hYprop, hJlim, hJsum, hYE, hYdiff,
      hZpred, hZM, hZcont, hZ0, hZmean, hYZ, hZE, hmax⟩ :=
    exists_continuous_covariance_integral hd hμ hb hcrit ν hB hmB hcB v
  refine ⟨Z, hZpred, hZM, hZcont, hZ, hZ0, ?_⟩
  apply ae_eq_posterior_of_integer hμ ν hB hmB hcB v hZM
  intro N hN
  obtain ⟨X, I, hI, hM, hX, hXlim, hXI, hmI, htI, hImean, hsI, hfinite⟩ :=
    exists_posterior_integral_representation hμ hd hb hcrit ν hB hmB hcB v N
  have hJX (n : ℕ) (u : TreeVertex d) : J n u N =ᵐ[P] X n u := by
    apply BrownianGrid.ae_eq_of_mean_square_limits _ (hJ n u N) (hX n u)
      (hJlim n u N hN) (hXlim n u)
    intro k
    exact BrownianFiltrationGrid.uniformSum_memLp
      (isBrownianReal_innovation hμ ν hB hmB hcB u).toIsPreBrownianReal
      (innovation_martingale hμ ν hB hmB hcB u).stronglyAdapted
      (fun s t hst => BrownianArrayFiltration.coordinate_increment_indep_past
        (innovation_increment_indep_filtration hμ ν hB hmB hcB s t hst) u)
      (finiteCovariance beta B v u n) (finiteCovariance_stronglyAdapted beta B hmB v u n)
      (finiteCovariance_memLp beta B hmB P v u n) N k
  have hJI (u : TreeVertex d) : Tendsto (fun n =>
      ∫ q, (J n u N q - I u q) ^ 2 ∂P) atTop (𝓝 0) := by
    apply (hXI u).congr'
    apply Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hJX n u] with q hq
    rw [hq]
  have ho (n : ℕ) : Pairwise fun u w =>
      ∫ q, J n u N q * J n w N q ∂P = 0 :=
    finiteCovariance_integrals_orthogonal hμ ν hB hmB hcB v n N
      (fun u => hJ n u N) (fun u => hJlim n u N hN)
  have he : (∫ q, Z N q ^ 2 ∂P) = ∫ q, posterior beta B v N q ^ 2 ∂P :=
    tendsto_nhds_unique (hZE N)
      (finiteCovariance_timeEnergy_tendsto hμ ν hB hmB hcB v N)
  exact FilteringRepresentationClosure.ae_eq_of_orthogonal_row_meanSquare_limits
    (fun n u => hJ n u N) (fun n => hY n N) hI (hZ N) hM
    (fun n => hJsum n N) ho hJI (hYZ N) hsI he

end Problem367.IsingInnovation

end

end OAI
