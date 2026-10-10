import Mathlib
import OAI.Probability.CriticalPercolation.Modular.TiltedTransportENNReal

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] (G : BondGraph V E)

omit [Countable V] in
lemma expected_enn_transport_aut (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ ω, F ω (φ.vertex x) (φ.vertex y) ∂G.law p) = ∫⁻ ω, F ω x y ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (hm _ _) (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [ha]

lemma OrbitRepresentatives.random_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y) :
    (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) =
      ∑ y ∈ R.roots, ∫⁻ ω, ∑' x, F ω x y * G.stabilizerWeight y x ∂G.law p := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _ (G.expected_enn_transport_aut p F hm ha)

lemma OrbitRepresentatives.incoming_finite_ae (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (N : ℝ≥0∞) (hN : N < ∞) (hb : ∀ ω x, ∑' y, F ω x y ≤ N) (v : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, F ω x v * G.stabilizerWeight v x) < ∞ := by
  have hout : (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) < ∞ := by
    apply ENNReal.sum_lt_top.mpr
    intro x hx
    exact (calc
      (∫⁻ ω, ∑' y, F ω x y ∂G.law p) ≤ ∫⁻ _ : Set E, N ∂G.law p :=
        lintegral_mono (fun ω => hb ω x)
      _ = N := by simp).trans_lt hN
  rw [OrbitRepresentatives.random_tilted_transport G R hc hl p F hm ha] at hout
  obtain ⟨u,hu,φ,rfl⟩ := R.cover v
  have hu' : (∫⁻ ω, ∑' x, F ω x u * G.stabilizerWeight u x ∂G.law p) < ∞ :=
    (Finset.single_le_sum (fun _ _ => zero_le) hu).trans_lt hout
  have he : (∫⁻ ω, ∑' x, F ω x (φ.vertex u) * G.stabilizerWeight (φ.vertex u) x ∂G.law p) =
      ∫⁻ ω, ∑' x, F ω x u * G.stabilizerWeight u x ∂G.law p := by
    conv_lhs => rw [←G.law_map_aut p φ]
    rw [lintegral_map (Measurable.tsum (fun x => (hm x _).mul_const _))
      (BernoulliProduct.measurable_image_equiv φ.edge)]
    apply lintegral_congr
    intro ω
    rw [←φ.vertex.tsum_eq]
    simp only [ha,Aut.stabilizerWeight]
  exact ae_lt_top (Measurable.tsum (fun x => (hm x _).mul_const _)) (he.trans_lt hu').ne

end CriticalPercolation.BondGraph
end
end

end OAI
