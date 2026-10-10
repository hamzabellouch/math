import OAI.Probability.MatroidProphet.Main
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! Transfer a proved finite seed/prefix experiment to every ambient probability
space in the secretary statement.  The executed adversarial order is deliberately
absent: no independence assumption on it is needed or introduced. -/

open MeasureTheory ProbabilityTheory

namespace MatroidProphet

theorem secretary_product_law {n : ℕ} {Q Ω : Type*}
    [MeasurableSpace Q] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Q)
    (η : Measure (ArrivalOrder n))
    (R : Ω → Q) (σ : Ω → ArrivalOrder n)
    (hR : Measurable R) (hσ : Measurable σ)
    (hRlaw : μ.map R = ν) (hσlaw : μ.map σ = η)
    (hind : IndepFun R σ μ) :
    MeasurePreserving (fun ω => (R ω, σ ω)) μ (ν.prod (η)) := by
  refine ⟨hR.prodMk hσ, ?_⟩
  rw [hind.map_prod_eq_prod_map_map hR.aemeasurable hσ.aemeasurable, hRlaw, hσlaw]

/-- A complete reconstructed seed has its source law on every admissible
ambient space once that law is established on the independent product model. -/
theorem secretary_reconstruction_law {n bits : ℕ} {Q Ω : Type*}
    [MeasurableSpace Q] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Q)
    (η : Measure (ArrivalOrder n))
    (ρ : Measure (Seed bits)) (reconstruct : Q × ArrivalOrder n → Seed bits)
    (hm : Measurable reconstruct)
    (hlaw : (ν.prod (η)).map reconstruct = ρ)
    (R : Ω → Q) (σ : Ω → ArrivalOrder n)
    (hR : Measurable R) (hσ : Measurable σ)
    (hRlaw : μ.map R = ν) (hσlaw : μ.map σ = η)
    (hind : IndepFun R σ μ) :
    MeasurePreserving (fun ω => reconstruct (R ω, σ ω)) μ ρ := by
  have hbase := secretary_product_law μ ν η R σ hR hσ hRlaw hσlaw hind
  exact (show MeasurePreserving reconstruct (ν.prod (η)) ρ
    from ⟨hm, hlaw⟩).comp hbase

/-- All almost-everywhere construction identities, including correct masked
support, pull back jointly; knowing only a mask marginal would not suffice. -/
theorem secretary_product_ae {n : ℕ} {Q Ω : Type*}
    [MeasurableSpace Q] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Q)
    (η : Measure (ArrivalOrder n))
    (R : Ω → Q) (σ : Ω → ArrivalOrder n)
    (hR : Measurable R) (hσ : Measurable σ)
    (hRlaw : μ.map R = ν) (hσlaw : μ.map σ = η)
    (hind : IndepFun R σ μ) (P : Q × ArrivalOrder n → Prop)
    (hP : ∀ᵐ x ∂ν.prod (η), P x) :
    ∀ᵐ ω ∂μ, P (R ω, σ ω) :=
  (secretary_product_law μ ν η R σ hR hσ hRlaw hσlaw hind).quasiMeasurePreserving.ae hP

end MatroidProphet

end OAI
