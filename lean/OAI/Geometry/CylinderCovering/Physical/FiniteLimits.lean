import OAI.Geometry.CylinderCovering.Physical.Finite

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace RadialPhysical

lemma physicalActualCost_nonneg (centered : Bool) (b eta : ℝ) (T : ℝ → ℝ)
    (N : ℕ) (tagU tagL : Fin N → ℝ) :
    0 ≤ physicalActualCost centered b eta T N tagU tagL := by
  exact add_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

lemma scaledCost_zero_cap (b eta : ℝ) : scaledCost b eta (fun _ => 0) = 0 := by
  simp [scaledCost, scaledDensity]

theorem physicalActualCost_tendsto_zero_of_cost_zero
    (centered : Bool) (b eta : ℝ) (hb : 0 < b) (T : ℝ → ℝ)
    (hT : ContinuousOn T (Icc (-b) b))
    (hT0 : ∀ s ∈ Icc (-b) b, 0 ≤ T s)
    (hcost : scaledCost b eta T = 0)
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (htagU : ∀ N, CylinderCovering.RadialRiemann.IsTagged (-b) b N (tagU N))
    (htagL : ∀ N, CylinderCovering.RadialRiemann.IsTagged (-b) b N (tagL N)) :
    Tendsto (fun N => physicalActualCost centered b eta T N (tagU N) (tagL N))
      atTop (𝓝 0) := by
  obtain ⟨U, L, hgeometry, htriangles, hupper, hlimsup⟩ :=
    physical_finite centered b eta hb T hT hT0 tagU tagL htagU htagL
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hupper (ε / 2) (by linarith)] with N hN
  rw [hcost, zero_add] at hN
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (physicalActualCost_nonneg centered b eta T N (tagU N) (tagL N))]
  linarith

theorem physicalActualCost_zero_cap_tendsto
    (centered : Bool) (b eta : ℝ) (hb : 0 < b)
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (htagU : ∀ N, CylinderCovering.RadialRiemann.IsTagged (-b) b N (tagU N))
    (htagL : ∀ N, CylinderCovering.RadialRiemann.IsTagged (-b) b N (tagL N)) :
    Tendsto (fun N => physicalActualCost centered b eta (fun _ => 0)
      N (tagU N) (tagL N)) atTop (𝓝 0) := by
  exact physicalActualCost_tendsto_zero_of_cost_zero centered b eta hb
    (fun _ => 0) continuousOn_const (fun _ _ => le_rfl)
    (scaledCost_zero_cap b eta) tagU tagL htagU htagL

end RadialPhysical

end

end OAI
