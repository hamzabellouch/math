import OAI.Analysis.FiniteFactor.Coupling.Noncrossing
import OAI.Analysis.FiniteFactor.TailEstimate
import Mathlib.Probability.Kernel.CondDistrib

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- Identification with mathlib's regular conditional distribution. -/
theorem vectorPosterior_eq_condDistrib {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool) :
    condDistrib (vectorEndpoint (fun i => !right i)) (vectorEndpoint right) (vectorCoupling p)
      =ᵐ[(vectorCoupling p).map (vectorEndpoint right)] vectorPosterior p right :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (vectorEndpoint_measurable right) (vectorEndpoint_measurable (fun i => !right i))
    (vectorPosterior_disintegration p right).symm

/-- A bound on the proved full-vector posterior is a conditional-expectation
bound on the original augmented probability space. -/
theorem vector_condExp_event_le {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool)
    {B : Set ((ι → ℝ) × (ι → ℝ))} (hB : MeasurableSet B) {δ : ℝ}
    (hb : ∀ᵐ x ∂(vectorCoupling p).map (vectorEndpoint right),
      (vectorPosterior p right x).real (Prod.mk x ⁻¹' B) ≤ δ) :
    ∀ᵐ ω ∂vectorCoupling p,
      (vectorCoupling p)[
        (fun ω => B.indicator (fun _ => (1 : ℝ))
          (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω)) |
        (inferInstance : MeasurableSpace (ι → ℝ)).comap (vectorEndpoint right)] ω ≤ δ := by
  have hX := vectorEndpoint_measurable right
  have hY := vectorEndpoint_measurable (fun i => !right i)
  have hint : Integrable (B.indicator (fun _ => (1 : ℝ)))
      ((vectorCoupling p).map (fun ω => (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω))) :=
    (integrable_const _).indicator hB
  have hc := condExp_prod_ae_eq_integral_condDistrib' hX hY.aemeasurable hint
  have hk := ae_eq_comp hX.aemeasurable (vectorPosterior_eq_condDistrib p right)
  have hb' := ae_of_ae_map hX.aemeasurable hb
  filter_upwards [hc, hk, hb'] with ω hcω hkω hbω
  simp only [Function.comp_apply] at hkω
  rw [hcω, hkω]
  have he : (fun y => B.indicator (fun _ => (1 : ℝ)) (vectorEndpoint right ω, y)) =
      (Prod.mk (vectorEndpoint right ω) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := rfl
  rw [he, integral_indicator (measurable_prodMk_left hB), setIntegral_const]
  simpa using hbω

/-- The countably infinite masked estimate, instantiated on the actual
augmented coupling using the verified posterior. No conditional probability
hypothesis remains to be supplied independently of the kernel. -/
theorem vector_mask_tsum_integral_le {ι V : Type*} [Countable ι] [Countable V]
    (p : ι → CouplingParameters) (right : ι → Bool)
    (B : V → Set ((ι → ℝ) × (ι → ℝ))) (hB : ∀ v, MeasurableSet (B v))
    (f : V → (ι → Fin 6 × (ℝ × ℝ)) → ℝ) (δ : ℝ)
    (hf : ∀ v, Integrable (f v) (vectorCoupling p))
    (hfm : ∀ v, StronglyMeasurable[(inferInstance : MeasurableSpace (ι → ℝ)).comap (vectorEndpoint right)] (f v))
    (hf0 : ∀ v ω, 0 ≤ f v ω)
    (hsum : ∀ᵐ ω ∂vectorCoupling p, Summable (fun v => f v ω))
    (hint : Integrable (fun ω => ∑' v, f v ω) (vectorCoupling p))
    (hb : ∀ v, ∀ᵐ x ∂(vectorCoupling p).map (vectorEndpoint right),
      (vectorPosterior p right x).real (Prod.mk x ⁻¹' B v) ≤ δ) :
    (∫ ω, (∑' v, ((fun ω => (vectorEndpoint right ω,
        vectorEndpoint (fun i => !right i) ω)) ⁻¹' B v).indicator (f v) ω) ∂vectorCoupling p) ≤
      δ * ∫ ω, (∑' v, f v ω) ∂vectorCoupling p := by
  apply conditional_mask_tsum_integral_le (vectorEndpoint_measurable right).comap_le
    hf hfm hf0
    (fun v => (hB v).preimage ((vectorEndpoint_measurable right).prodMk
      (vectorEndpoint_measurable (fun i => !right i)))) hsum hint
  intro v
  exact vector_condExp_event_le p right (hB v) (hb v)

end CouplingParameters
end
end FiniteFactor

end OAI
