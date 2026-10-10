import OAI.MathematicalPhysics.Boltzmann.Branching.WindowLocalizedSource
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

section

/-! # A local L1 limit of commonly supported functions is a global L1 limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem supported_l1_limit {f : ℕ → X → ℝ} {g : X → ℝ} {K : Set X}
    (hK : MeasurableSet K) (hf : ∀ n x, x ∉ K → f n x = 0) (hg : IntegrableOn g K μ)
    (hc : Tendsto (fun n => eLpNorm (f n-g) 1 (μ.restrict K)) atTop (𝓝 0)) :
    Integrable (K.indicator g) μ ∧
      Tendsto (fun n => eLpNorm (f n-K.indicator g) 1 μ) atTop (𝓝 0) := by
  refine ⟨hg.integrable_indicator hK,?_⟩
  have he (n : ℕ) : f n-K.indicator g = K.indicator (f n-g) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [Pi.sub_apply,indicator_of_mem hx]
    · simp only [Pi.sub_apply,indicator_of_notMem hx,hf n x hx,sub_self]
  simpa only [he,eLpNorm_indicator_eq_eLpNorm_restrict hK] using hc

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Compactly supported transport tests need only local integrability -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.TransportCutoff

theorem transportDerivative_tsupport_subset (χ : KineticPhase → ℝ) :
    tsupport (transportDerivative χ) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra hn
  exact hz (transportDerivative_eq_zero hn)

theorem supported_mul_integrable {s : Set KineticPhase} (hs : MeasurableSet s)
    {χ f : KineticPhase → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ s) (hf : Integrable f (volume.restrict s)) :
    Integrable (fun z => χ z*f z) := by
  obtain ⟨C,hC⟩ := hχ.bounded_above_of_compact_support hc
  have hi := hf.bdd_mul hχ.measurable.aestronglyMeasurable (ae_of_all _ hC)
  have h0 := (integrable_indicator_iff hs).mpr hi
  apply h0.congr
  exact ae_of_all _ (fun z => by
    by_cases hz : z ∈ s
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz]
      dsimp only
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hχs h)),zero_mul])

theorem transport_test_integrable {s : Set KineticPhase} (hs : MeasurableSet s)
    {χ f Q : KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hχs : tsupport χ ⊆ s)
    (hf : Integrable f (volume.restrict s)) (hQ : Integrable Q (volume.restrict s)) :
    Integrable (fun z => transportDerivative χ z*f z+χ z*Q z) :=
  (supported_mul_integrable hs (transportDerivative_continuous hχ)
    (transportDerivative_hasCompactSupport hc)
    ((transportDerivative_tsupport_subset χ).trans hχs) hf).add
    (supported_mul_integrable hs hχ.continuous hc hχs hQ)

end BoltzmannNonuniqueness.TransportCutoff

end

end

end OAI
