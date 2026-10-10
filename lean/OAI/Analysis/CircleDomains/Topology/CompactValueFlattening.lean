import OAI.Analysis.CircleDomains.Sobolev.CountableValueFlattening

namespace OAI

/-! Flattening preserves compact support of the old source tests, in
addition to their continuous representatives and quantitative errors. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_compact_value_flattening
    (hcoarea : PlanarSobolevCoarea) {U : Set EuclideanPlane} (hU : IsOpen U)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u U) {C : Set ℝ} (hC : C.Countable)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ O : Set ℝ, ∃ W' : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ u) U,
      IsOpen O ∧ C ⊆ O ∧ Continuous (flattenValues O ∘ u) ∧
      HasCompactSupport (flattenValues O ∘ u) ∧
      (∀ t, |flattenValues O t-t| < δ) ∧
      (∫⁻ p in U, ENNReal.ofReal (‖W'.weakGrad p-W.weakGrad p‖^2)) < ENNReal.ofReal ε ∧
      (∀ p, W.weakGrad p = 0 → W'.weakGrad p = 0) := by
  obtain ⟨B, hB⟩ := hu.bounded_above_of_compact_support hs
  have hb : ∀ p ∈ U, u p ∈ Icc (-max B 0) (max B 0) := by
    intro p _
    apply abs_le.mp
    exact (show |u p| ≤ B from hB p).trans (le_max_left _ _)
  obtain ⟨O, W', hO, hCO, hLip, hclose, henergy, _, hzero⟩ :=
    exists_countable_value_flattening hcoarea hU hu W (le_max_right B 0) hb hC hδ hε
  exact ⟨O, W', hO, hCO, hLip.continuous.comp hu,
    hs.comp_left (flattenValues_zero O), hclose, henergy, hzero⟩

end CircleDomainRigidity

end

end OAI
