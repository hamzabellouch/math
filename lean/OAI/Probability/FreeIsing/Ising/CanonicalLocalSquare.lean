import OAI.Probability.FreeIsing.Ising.CanonicalArtanh
import OAI.Probability.FreeIsing.Ising.CopyVarianceEquation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

 theorem continuousField_initial_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    continuousField beta v 0 =ᵐ[observationLaw μ] 0 := by
  filter_upwards [continuousPosterior_initial_zero hd hμ hb hcrit v] with x hx
  have he := artanh_continuousPosterior beta v 0 x
  rw [hx] at he
  simpa only [Pi.zero_apply, Real.artanh_zero] using he.symm

 theorem continuousDifference_initial_zero
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    continuousDifference beta v 0 =ᵐ[copies beta μ] 0 := by
  have h0 := continuousField_initial_zero hd hμ hb hcrit v
  filter_upwards [(copyProjection_measurePreserving beta μ true).quasiMeasurePreserving.ae h0,
    (copyProjection_measurePreserving beta μ false).quasiMeasurePreserving.ae h0] with q hl hr
  change continuousField beta v 0 q.2.1 - continuousField beta v 0 q.2.2 = 0
  change continuousField beta v 0 q.2.1 = 0 at hl
  change continuousField beta v 0 q.2.2 = 0 at hr
  rw [hl, hr, sub_self]

theorem actual_variance_analysis_of_common_local_square
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (T : ℝ≥0)
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ q, (stoppedProcess (continuousDifference beta v)
        (commonPosteriorExit beta v n) t q) ^ 2 ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ q,
        if (s.toNNReal : WithTop ℝ≥0) ≤ commonPosteriorExit beta v n q
          then density beta v s q else 0 ∂copies beta μ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ q,
      (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ q,
        (field beta v s.toNNReal q.2.1 - field beta v s.toNNReal q.2.2) ^ 2
          ∂copies beta μ) t = ∫ q, density beta v t q ∂copies beta μ) := by
  obtain ⟨hc, hver⟩ := continuousDifference_modification hd hμ hb hcrit v
  have hprog := DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
    ContinuousCopyBrownian.joinedFiltration.le_rightCont
    (continuousDifference_progressive beta v)
  have hτ := isLocalizingSequence_commonPosteriorExit hd hμ hb hcrit v
  apply field_difference_energy_analysis_of_stopped_version hμ hb v hprog hc hver
    hτ.isStoppingTime (ae_eventually_le_commonPosteriorExit hd hμ hb hcrit v T)
    (density_integrable hμ hb v T)
  have hzero : (∫ q, (continuousDifference beta v 0 q) ^ 2 ∂copies beta μ) = 0 := by
    calc
      _ = ∫ _q, (0 : ℝ) ∂copies beta μ := integral_congr_ae
        ((continuousDifference_initial_zero hd hμ hb hcrit v).mono (fun q hq => by
          change continuousDifference beta v 0 q = 0 at hq
          rw [hq, zero_pow (by decide : 2 ≠ 0)]))
      _ = 0 := integral_zero _ _
  intro n t ht
  rw [hzero, zero_add]
  exact hlocal n t ht

theorem actual_variance_analysis_of_local_square
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (T : ℝ≥0)
    {τ : ℕ → Joint d → WithTop ℝ≥0}
    (hstopping : ∀ n, IsStoppingTime ContinuousCopyBrownian.joinedFiltration.rightCont (τ n))
    (hexit : ∀ᵐ q ∂copies beta μ, ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ τ n q)
    (hlocal : ∀ n, ∀ t ≤ T,
      (∫ q, (stoppedProcess (continuousDifference beta v)
        (τ n) t q) ^ 2 ∂copies beta μ) =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ q,
        if (s.toNNReal : WithTop ℝ≥0) ≤ τ n q
          then density beta v s q else 0 ∂copies beta μ) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ q,
      (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ q,
        (field beta v s.toNNReal q.2.1 - field beta v s.toNNReal q.2.2) ^ 2
          ∂copies beta μ) t = ∫ q, density beta v t q ∂copies beta μ) := by
  obtain ⟨hc, hver⟩ := continuousDifference_modification hd hμ hb hcrit v
  have hprog := DominatedMartingaleRightContinuation.isStronglyProgressive_mono_filtration
    ContinuousCopyBrownian.joinedFiltration.le_rightCont
    (continuousDifference_progressive beta v)
  apply field_difference_energy_analysis_of_stopped_version hμ hb v hprog hc hver
    hstopping hexit
    (density_integrable hμ hb v T)
  have hzero : (∫ q, (continuousDifference beta v 0 q) ^ 2 ∂copies beta μ) = 0 := by
    calc
      _ = ∫ _q, (0 : ℝ) ∂copies beta μ := integral_congr_ae
        ((continuousDifference_initial_zero hd hμ hb hcrit v).mono (fun q hq => by
          change continuousDifference beta v 0 q = 0 at hq
          rw [hq, zero_pow (by decide : 2 ≠ 0)]))
      _ = 0 := integral_zero _ _
  intro n t ht
  rw [hzero, zero_add]
  exact hlocal n t ht

end Problem367.IsingObservationFactor

end

end OAI
