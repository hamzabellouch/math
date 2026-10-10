import OAI.Probability.FreeIsing.Brownian.ArrayCompensator
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingFilteringIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

def quadraticCompensator (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (p : State d Ω) : ℝ :=
  ∑ u : D, ∫ r in (0 : ℝ)..(t : ℝ), covariance beta D v u B r.toNNReal p ^ 2

omit [MeasurableSpace Ω] in
theorem quadraticCompensator_eq_selected
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (t : ℝ≥0) (p : State d Ω) :
    quadraticCompensator beta D v B t p =
      ∑ u : D, SelectedCompensator.selected (covariance beta D v u B) t t p := by
  apply Finset.sum_congr rfl
  intro u hu
  simpa only [min_self] using
    (SelectedCompensator.selected_eq_integral_of_continuous
      (continuous_covariance beta D v u B hcB p) t t).symm

theorem stronglyAdapted_quadraticCompensator
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) :
    StronglyAdapted (observationFiltration B hmB D) (quadraticCompensator beta D v B) := by
  intro t
  have h : quadraticCompensator beta D v B t = fun p =>
      ∑ u : D, SelectedCompensator.selected (covariance beta D v u B) t t p :=
    funext (quadraticCompensator_eq_selected beta D v B hcB t)
  rw [h]
  exact Finset.stronglyMeasurable_fun_sum _ fun u _ =>
    SelectedCompensator.selected_stronglyAdapted
      (stronglyAdapted_covariance beta D v u B hmB) t t

omit [MeasurableSpace Ω] in
theorem quadraticCompensator_eq_integral_energy
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ)
    (hcB : ∀ i omega, Continuous (fun t => B i t omega)) (t : ℝ≥0) (p : State d Ω) :
    quadraticCompensator beta D v B t p =
      ∫ r in (0 : ℝ)..(t : ℝ), ∑ u : D, covariance beta D v u B r.toNNReal p ^ 2 := by
  symm
  apply intervalIntegral.integral_finsetSum
  intro u hu
  have hc : Continuous (fun r : ℝ => covariance beta D v u B r.toNNReal p ^ 2) :=
    ((continuous_covariance beta D v u B hcB p).comp (by fun_prop)).pow 2
  exact hc.intervalIntegrable _ _

theorem mean_compensatedSquare_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) :
    Martingale (fun t p => mean beta D v B t p ^ 2 - quadraticCompensator beta D v B t p)
      (observationFiltration B hmB D) (μ.prod (Measure.infinitePi ν)) := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hind (s t : ℝ≥0) (hst : s ≤ t) : Pairwise fun u w : D =>
      IndepFun (fun p => innovation beta D u B t p - innovation beta D u B s p)
        (fun p => innovation beta D w B t p - innovation beta D w B s p)
        (μ.prod (Measure.infinitePi ν)) := by
    intro u w huw
    exact (innovation_increment_law_and_indep hμ ν hB hmB hcB D hD s t hst
      (Y := fun _ => ()) measurable_const).2.1.indepFun huw
  have h := BrownianArrayCompensator.compensatedSquare_of_terminal_meanSquare
    (fun u : D => (innovation_isBrownianReal hμ ν hB hmB hcB D hD u).toIsPreBrownianReal)
    (fun u => innovation_stronglyAdapted beta D u B hmB hcB)
    (innovation_increment_indep_filtration hμ ν hB hmB hcB D hD) hind
    (fun u => stronglyAdapted_covariance beta D v u B hmB)
    (fun u => Eventually.of_forall (continuous_covariance beta D v u B hcB))
    (fun _ => 2) (fun _ => by norm_num)
    (fun u => Eventually.of_forall fun p t => abs_covariance_le_two beta D v u B t p)
    (mean_martingale hμ ν hB hmB D hD v)
    (fun t => memLp_mean (μ.prod (Measure.infinitePi ν)) beta D v B hmB t 2)
    (tendsto_uniformSum_row_meanSquare hμ ν hB hmB hcB D hD v)
  convert h using 1
  funext t p
  rw [quadraticCompensator_eq_selected beta D v B hcB t p]

theorem mean_compensatedSquare_energy_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) :
    Martingale (fun t p => mean beta D v B t p ^ 2 -
      ∫ r in (0 : ℝ)..(t : ℝ), ∑ u : D, covariance beta D v u B r.toNNReal p ^ 2)
      (observationFiltration B hmB D) (μ.prod (Measure.infinitePi ν)) := by
  convert mean_compensatedSquare_martingale hμ ν hB hmB hcB D hD v using 1
  funext t p
  rw [quadraticCompensator_eq_integral_energy beta D v B hcB t p]

end Problem367.FiniteIsingFiltering

end

end OAI
