import OAI.Analysis.LipschitzHilbert.Trees.SourceRadialScales

namespace OAI

/-! Positive self mass and the fixed total mass bound every radial eligible
mass along a top's eligible path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

theorem nearbyEligibleMass_self_le (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) {r : ℝ} (hr : 0 < r) (x : X) :
    weight top x ≤ g.nearbyEligibleMass tops slope precision cutoff weight i r (slope top) x := by
  apply Finset.single_le_sum (fun t _ => hw t x)
  exact Finset.mem_filter.mpr ⟨htop,he,by simpa using hr⟩

theorem nearbyEligibleMass_le_total (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 ≤ weight t x) (i : ℕ) (r s : ℝ) (x : X) :
    g.nearbyEligibleMass tops slope precision cutoff weight i r s x ≤ ∑ t ∈ tops, weight t x :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun t _ _ => hw t x)

def radialPathLogMass (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (epsilon : ℝ) (N : ℕ) (top : τ) (x : X) (i : ℕ) : ℝ :=
  if i < N then Real.log
    (g.nearbyEligibleMass tops slope precision cutoff weight i (epsilon*g.width i) (slope top) x /
      weight top x) else 0

theorem radialPathLogMass_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 < weight t x) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (N : ℕ) (top : τ) (htop : top ∈ tops)
    (he : ∀ i < N, g.eligible cutoff (precision top) i) (x : X) (i : ℕ) :
    0 ≤ g.radialPathLogMass tops slope precision cutoff weight epsilon N top x i ∧
      g.radialPathLogMass tops slope precision cutoff weight epsilon N top x i ≤
        Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  have htotal : weight top x ≤ ∑ t ∈ tops, weight t x :=
    Finset.single_le_sum (fun t _ => (hw t x).le) htop
  have htotallog : 0 ≤ Real.log ((∑ t ∈ tops, weight t x)/weight top x) :=
    Real.log_nonneg ((one_le_div (hw top x)).mpr htotal)
  by_cases hi : i < N
  · have hself := g.nearbyEligibleMass_self_le tops slope precision cutoff weight
      (fun t x => (hw t x).le) i top htop (he i hi) (mul_pos hepsilon (g.width_pos i)) x
    have hmasspos := (hw top x).trans_le hself
    have hupper := g.nearbyEligibleMass_le_total tops slope precision cutoff weight
      (fun t x => (hw t x).le) i (epsilon*g.width i) (slope top) x
    simp only [radialPathLogMass,ite_eq_left hi]
    exact ⟨Real.log_nonneg ((one_le_div (hw top x)).mpr hself),
      Real.log_le_log (div_pos hmasspos (hw top x))
        (div_le_div_of_nonneg_right hupper (hw top x).le)⟩
  · simpa only [radialPathLogMass,ite_eq_right hi] using And.intro le_rfl htotallog

end LipschitzHilbert.AngularGrid

end

end OAI
