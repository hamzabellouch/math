import OAI.Probability.FreeIsing.Ising.CanonicalContinuousFields
import OAI.Probability.FreeIsing.Ising.CopyStationarity

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ProgressiveVersionPushforward

theorem ae_all_version_comp_eq
    {Ω Ξ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : ℝ≥0 → Ξ → ℝ} {N : ℝ≥0 → Ω → ℝ} {φ : Ω → Ξ}
    (h : ∀ t, (fun ω => M t (φ ω)) =ᵐ[μ] N t) :
    ∀ᵐ ω ∂μ, ∀ t, version M t (φ ω) = version N t ω := by
  have hgrid : ∀ᵐ ω ∂μ, ∀ p : ℤ × ℕ,
      M (gridTime p) (φ ω) = N (gridTime p) ω :=
    ae_all_iff.mpr (fun p => h (gridTime p))
  filter_upwards [hgrid] with ω hω
  intro t
  change ContinuousModification.sampledLimit leftTime
      (fun s ω => M s (φ ω)) t ω =
    ContinuousModification.sampledLimit leftTime N t ω
  apply ContinuousModification.sampledLimit_congr
  intro n
  obtain ⟨p, hp⟩ := leftTime_mem_range t n
  rw [← hp]
  exact hω p

end Problem367.ProgressiveVersionPushforward

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem continuousField_array_relabel_ae [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    ∀ᵐ x ∂observationLaw μ,
      (fun v t => continuousField beta v t (relabel g x)) =
        relabel g (fun v t => continuousField beta v t x) := by
  have hcoord (v : TreeVertex d) : ∀ᵐ x ∂observationLaw μ, ∀ t,
      continuousField beta v t (relabel g x) =
        continuousField beta (g.toEquiv.symm v) t x := by
    apply ProgressiveVersionPushforward.ae_all_version_comp_eq
    intro t
    filter_upwards [field_array_relabel_ae hμ g t] with x hx
    exact congrFun hx v
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  exact funext (fun v => funext (hx v))

theorem continuousDifference_array_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) :
    ∀ᵐ q ∂copies beta μ,
      (fun v t => continuousDifference beta v t (copyRelabel g q)) =
        relabel g (fun v t => continuousDifference beta v t q) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards
    [hl.quasiMeasurePreserving.ae (continuousField_array_relabel_ae hμ g),
      hr.quasiMeasurePreserving.ae (continuousField_array_relabel_ae hμ g)]
      with q hql hqr
  funext v t
  exact congrArg₂ (fun a b : ℝ => a - b)
    (congrFun (congrFun hql v) t) (congrFun (congrFun hqr v) t)

end Problem367.IsingObservationFactor

end

end OAI
