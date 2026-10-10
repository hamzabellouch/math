import OAI.Geometry.IsometricImmersion.Flows.FiniteMetricChosenFlow
import OAI.Geometry.IsometricImmersion.Caps.UpperCapMetricJets
import OAI.Geometry.IsometricImmersion.Caps.OpenCapFlowUniqueness

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

def upperCapPointwiseRequests {floor : ℝ} (n : ℕ) (r : UpperCapRectangle floor) :
    List (ℕ × UpperCapRectangle floor) :=
  (lowerCapPointwiseRequests n r.lower).map (fun b => (b.1,reflectedUpperRectangle b.2))

def FiniteUpperCapMetricJets {floor : ℝ} (g : MetricField) (Y : ℝ → ℝ → ℝ)
    (J : UpperCapMetricJetBudget floor) (L : List (ℕ × UpperCapRectangle floor)) : Prop :=
  ∀ b ∈ L, ∀ (i j : Fin 2) (k : ℕ), k ≤ b.1+2 →
    ∀ p ∈ b.2.image Y, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ J b.1 b.2

theorem upperCapPointwiseRequests_length {floor : ℝ} (n : ℕ)
    (r : UpperCapRectangle floor) :
    (upperCapPointwiseRequests n r).length = 2*(n-6) := by
  simp only [upperCapPointwiseRequests,List.length_map,lowerCapPointwiseRequests_length]

theorem upperCapPointwiseRequests_full_order_le {floor : ℝ} (n : ℕ)
    (r : UpperCapRectangle floor) (b : ℕ × UpperCapRectangle floor)
    (hb : b ∈ upperCapPointwiseRequests n r) {k : ℕ} (hk : k ≤ b.1+2) :
    k ≤ max 8 (n+3) := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  exact lowerCapPointwiseRequests_full_order_le n r.lower a ha hk

theorem reflectedMetric_finiteCapJets {floor : ℝ} {g : MetricField}
    {Y : ℝ → ℝ → ℝ} {J : UpperCapMetricJetBudget floor}
    (L : List (ℕ × LowerCapRectangle (-floor)))
    (hJ : FiniteUpperCapMetricJets g (conjugateFlow Y) J
      (L.map (fun b => (b.1,reflectedUpperRectangle b.2)))) :
    FiniteCapMetricJets (reflectedMetric g) Y (reflectedUpperBudget J) L := by
  intro b hb i j k hk p hp
  rw [reflectedMetric_entry_jet_norm]
  apply hJ (b.1,reflectedUpperRectangle b.2) (List.mem_map.mpr ⟨b,hb,rfl⟩) i j k hk
  rw [reflectedUpperRectangle_image]
  exact ⟨p,hp,rfl⟩

theorem finiteUpperCapMetricJets_of_chart_eqOn
    {floor : ℝ} {g : MetricField} {Y Z : ℝ → ℝ → ℝ}
    {J : UpperCapMetricJetBudget floor} {L : List (ℕ × UpperCapRectangle floor)}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (hJ : FiniteUpperCapMetricJets g Y J L) : FiniteUpperCapMetricJets g Z J L := by
  intro b hb i j k hk p hp
  have himg : b.2.image Y = b.2.image Z :=
    capChart_images_eq_of_eqOn heq b.2.region_subset_domain
  rw [←himg] at hp
  exact hJ b hb i j k hk p hp

end SmoothLocal.Flow.Reflection

end

end OAI
