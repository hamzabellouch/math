import OAI.Geometry.IsometricImmersion.Flows.VaryingMetricChosenFlow
import OAI.Geometry.IsometricImmersion.Caps.UpperCapWords

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

abbrev UpperCapMetricJetBudget (floor : ℝ) := ℕ → UpperCapRectangle floor → ℝ

def LocalUpperCapMetricJets {floor : ℝ} (g : MetricField) (Y : ℝ → ℝ → ℝ)
    (J : UpperCapMetricJetBudget floor) : Prop :=
  ∀ (N : ℕ) (r : UpperCapRectangle floor) (i j : Fin 2) (k : ℕ),
    k ≤ N + 2 → ∀ p ∈ r.image Y, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ J N r

def reflectedUpperRectangle {floor : ℝ} (r : LowerCapRectangle (-floor)) :
    UpperCapRectangle floor where
  left := r.left
  right := r.right
  bottom := -r.top
  top := -r.bottom
  left_gt := r.left_gt
  right_lt := r.right_lt
  top_lt := by simpa only [neg_neg] using neg_lt_neg r.bottom_gt
  horizontal := r.horizontal
  vertical := neg_le_neg r.vertical
  bottom_gt := by simpa only [neg_neg] using neg_lt_neg r.top_lt
  floor_nonneg := neg_nonpos.mp r.ceiling_le

theorem reflectedUpperRectangle_lower {floor : ℝ} (r : LowerCapRectangle (-floor)) :
    (reflectedUpperRectangle r).lower = r := by
  cases r
  simp only [reflectedUpperRectangle, UpperCapRectangle.lower, neg_neg]

theorem reflectedUpperRectangle_image {floor : ℝ} (r : LowerCapRectangle (-floor))
    (Y : ℝ → ℝ → ℝ) :
    (reflectedUpperRectangle r).image (conjugateFlow Y) = reflectPoint '' r.image Y := by
  rw [UpperCapRectangle.conjugate_image, reflectedUpperRectangle_lower]

def reflectedUpperBudget {floor : ℝ} (J : UpperCapMetricJetBudget floor) :
    CapMetricJetBudget (-floor) := fun N r => J N (reflectedUpperRectangle r)

theorem reflectedMetric_localCapJets {floor : ℝ} {g : MetricField}
    {Y : ℝ → ℝ → ℝ} {J : UpperCapMetricJetBudget floor}
    (hJ : LocalUpperCapMetricJets g (conjugateFlow Y) J) :
    LocalCapMetricJets (reflectedMetric g) Y (reflectedUpperBudget J) := by
  intro N r i j k hk p hp
  rw [reflectedMetric_entry_jet_norm]
  apply hJ N (reflectedUpperRectangle r) i j k hk
  rw [reflectedUpperRectangle_image]
  exact ⟨p, hp, rfl⟩

theorem conjugateFlow_twice (Y : ℝ → ℝ → ℝ) :
    conjugateFlow (conjugateFlow Y) = Y := by
  funext s t
  simp only [conjugateFlow, neg_neg]

end SmoothLocal.Flow.Reflection

end

end OAI
