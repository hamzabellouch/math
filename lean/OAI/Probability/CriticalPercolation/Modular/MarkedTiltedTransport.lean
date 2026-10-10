import Mathlib
import OAI.Probability.CriticalPercolation.Modular.TiltedTransportENNReal
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneBernoulli

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma expected_mark_transport_aut
    (F : (E → ℝ) → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun u => F u x y))
    (ha : ∀ (φ : G.Aut) u x y,
      F (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) = F u x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ u, F u (φ.vertex x) (φ.vertex y) ∂markLaw) = ∫⁻ u, F u x y ∂markLaw := by
  conv_lhs => rw [←markLaw_map_reindex φ.edge]
  rw [lintegral_map (hm _ _) (measurable_reindexMarks φ.edge)]
  simp only [ha]

omit [Countable E] in
lemma OrbitRepresentatives.mark_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : (E → ℝ) → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun u => F u x y))
    (ha : ∀ (φ : G.Aut) u x y,
      F (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) = F u x y) :
    (∑ x ∈ R.roots, ∫⁻ u, ∑' y, F u x y ∂markLaw) =
      ∑ y ∈ R.roots, ∫⁻ u, ∑' x, F u x y * G.stabilizerWeight y x ∂markLaw := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _
    (G.expected_mark_transport_aut F hm ha)

omit [Countable V] [Countable E] in
lemma marks_ae_of_law_ae (p : unitInterval) (P : Set E → Prop) (h : ∀ᵐ ω ∂G.law p, P ω) :
    ∀ᵐ u ∂markLaw, P (atParameter p u) := by
  apply ae_of_ae_map (measurable_atParameter p).aemeasurable
  rwa [markLaw_map_atParameter,BernoulliProduct.law_const]

end CriticalPercolation.BondGraph
end
end

end OAI
