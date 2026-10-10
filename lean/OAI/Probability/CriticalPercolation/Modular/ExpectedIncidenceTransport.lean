import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Modular.NormalizedIncidenceTransport

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

lemma lintegral_ne_top_of_uniform_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) (C : ℝ≥0∞) (hC : C≠∞)
    (hb : ∀ a, f a≤C) : (∫⁻ a, f a ∂μ)≠∞ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (measure_ne_top μ Set.univ))
  simpa only [lintegral_const] using lintegral_mono hb

lemma sum_integral_toReal {α ι : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (S : Finset ι) (F : ι → α → ℝ≥0∞) (hm : ∀ i∈S, Measurable (F i))
    (C : ι → ℝ≥0∞) (hC : ∀ i∈S, C i≠∞) (hb : ∀ i∈S, ∀ a, F i a≤C i) :
    (∑ i∈S, ∫ a, (F i a).toReal ∂μ)=(∑ i∈S, ∫⁻ a, F i a ∂μ).toReal := by
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_toReal (hm i hi).aemeasurable (Eventually.of_forall (fun a =>
      lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top (hC i hi) (hb i hi a))))
  · intro i hi
    exact lintegral_ne_top_of_uniform_bound μ (F i) (C i) (hC i hi) (hb i hi)

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

def selectedIncidenceReturn (hl : G.LocallyFinite) (H : Set E → E → ℝ≥0∞)
    (ω : Set E) (y : V) : ℝ≥0∞ :=
  ∑ e∈(hl y).toFinset, H ω e*G.incidentClusterCount ω e

lemma selectedIncidenceReturn_eq_tsum (hl : G.LocallyFinite) (H : Set E → E → ℝ≥0∞)
    (ω : Set E) (y : V) : G.selectedIncidenceReturn hl H ω y =
      ∑' e, if y∈G.ends e then H ω e*G.incidentClusterCount ω e else 0 := by
  rw [tsum_eq_sum (s := (hl y).toFinset) (fun e he => ite_eq_right (by simpa using he))]
  apply Finset.sum_congr rfl
  intro e he
  exact (ite_eq_left ((hl y).mem_toFinset.mp he)).symm

lemma measurable_selectedIncidenceReturn [Countable V] [Countable E]
    (hl : G.LocallyFinite) (H : Set E → E → ℝ≥0∞) (hm : ∀ e, Measurable (fun ω => H ω e)) (y : V) :
    Measurable (fun ω => G.selectedIncidenceReturn hl H ω y) :=
  Finset.measurable_sum _ (fun e _ => (hm e).mul (G.measurable_incidentClusterCount e))

lemma selectedIncidenceReturn_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (H : Set E → E → ℝ≥0∞) (hH : ∀ ω e, H ω e≤1) (ω : Set E) (y : V) :
    G.selectedIncidenceReturn hl H ω y≤(hl y).toFinset.card*2 := by
  unfold selectedIncidenceReturn
  calc _ ≤ ∑ _e∈(hl y).toFinset, (2:ℝ≥0∞) := by
          apply Finset.sum_le_sum
          intro e _
          exact (mul_le_mul' (hH ω e) (G.incidentClusterCount_le_two hc hl ω e)).trans_eq (one_mul 2)
       _ = _ := by simp

lemma selectedIncidenceReturn_toReal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (H : Set E → E → ℝ≥0∞) (hH : ∀ ω e, H ω e≤1) (ω : Set E) (y : V) :
    (G.selectedIncidenceReturn hl H ω y).toReal=
      ∑ e∈(hl y).toFinset, (H ω e).toReal*(G.incidentClusterCount ω e).toReal := by
  unfold selectedIncidenceReturn
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro e _
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hH ω e))
      (ne_top_of_le_ne_top (by norm_num : (2:ℝ≥0∞)≠∞) (G.incidentClusterCount_le_two hc hl ω e))

lemma expected_selectedIncidence_real [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (H : Set E → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e)) (hH : ∀ ω e, H ω e≤1)
    (ha : ∀ (φ : G.Aut) ω e, H (φ.edge '' ω) (φ.edge e)=H ω e) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.normalizedSelectedIncidence H ω x).toReal ∂G.law p)=
      ∑ y∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.selectedIncidenceReturn hl H ω y).toReal ∂G.law p := by
  rw [sum_integral_toReal (G.law p) _ _ (fun x _ => G.measurable_normalizedSelectedIncidence H hm x)
      (fun _ => (D*(2*K) : ℕ)) (fun _ _ => ENNReal.natCast_ne_top _)
      (fun x _ ω => G.normalizedSelectedIncidence_le hc hl D K hD hK H hH ω x),
    sum_integral_toReal (G.law p) _ _ (fun y _ => G.measurable_selectedIncidenceReturn hl H hm y)
      (fun y => (hl y).toFinset.card*2) (fun _ _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num))
      (fun y _ ω => G.selectedIncidenceReturn_le hc hl H hH ω y)]
  congr 1
  simp_rw [G.selectedIncidenceReturn_eq_tsum]
  exact G.expected_normalizedSelectedIncidence hc hl hq p H hm ha

end BondGraph
end CriticalPercolation
end
end

end OAI
