import OAI.Probability.FreeIsing.Ising.CopyEnergyIntegrability
import OAI.Probability.FreeIsing.Ising.CopyStoppedEnergy

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

theorem field_variance_equation_of_local_square
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (v : TreeVertex d)
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Joint d))}
    {X : ℝ≥0 → Joint d → ℝ} (hX : IsStronglyProgressive F X)
    (hc : ∀ᵐ q ∂copies beta μ, Continuous (fun t => X t q))
    (hver : ∀ t, X t =ᵐ[copies beta μ]
      (fun q => field beta v t q.2.1 - field beta v t q.2.2))
    {τ : ℕ → Joint d → WithTop ℝ≥0} (hτ : ∀ n, IsStoppingTime F (τ n))
    {T : ℝ≥0}
    (hexit : ∀ᵐ q ∂copies beta μ, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n q)
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ q, (stoppedProcess X (τ n) t q) ^ 2 ∂copies beta μ) =
        (∫ q, (X 0 q) ^ 2 ∂copies beta μ) + ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ q, if (s.toNNReal : WithTop ℝ≥0) ≤ τ n q then density beta v s q else 0
            ∂copies beta μ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ q,
      (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) 0 T ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        deriv (fun s : ℝ => ∫ q,
          (field beta v s.toNNReal q.2.1 - field beta v s.toNNReal q.2.2) ^ 2
            ∂copies beta μ) t =
          (∑' w, ∫ q, (responseRow beta v w (t, q.2.1) -
            responseRow beta v w (t, q.2.2)) ^ 2 ∂copies beta μ) +
          2 * ∫ q, (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) *
            (posterior beta v t.toNNReal q.2.1 * (∑' w, responseRow beta v w (t, q.2.1) ^ 2) -
              posterior beta v t.toNNReal q.2.2 * (∑' w, responseRow beta v w (t, q.2.2) ^ 2))
              ∂copies beta μ) := by
  obtain ⟨hac, hd⟩ := field_difference_energy_analysis_of_stopped_version hμ hb v
    hX hc hver hτ hexit (density_integrable hμ hb v T) hlocal
  refine ⟨hac, ?_⟩
  filter_upwards [hd, ae_integral_density_eq hμ hb v T] with t ht he
  exact ht.trans he

end Problem367.IsingObservationFactor

end

end OAI
