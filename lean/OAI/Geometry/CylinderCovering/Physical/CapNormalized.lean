import OAI.Geometry.CylinderCovering.Physical.CapNormalizedDefinitions
import OAI.Geometry.CylinderCovering.Physical.CapFinite
import OAI.Geometry.CylinderCovering.Physical.Minimum

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace RadialPhysical
open CylinderCovering

lemma physicalHalfReference_eq (centered : Bool) (b : ℝ) :
    physicalHalfReference centered b = ((if centered then 4 else 1)*b*height b)/2 := by
  cases centered <;> simp only [physicalHalfReference, Bool.false_eq_true, ite_false, ite_true]
  · ring
  · ring

private lemma actualRelative_le (centered : Bool) {b : ℝ} (hb : 0 < b)
    (eta : ℝ) (T : ℝ → ℝ) (N : ℕ) (tagU tagL : Fin N → ℝ)
    (hU : ∀ i, ‖upperPhysicalAxis b eta (tagU i)‖ = 1)
    (hL : ∀ i, ‖lowerPhysicalAxis b eta (tagL i)‖ = 1) :
    physicalActualRelativeCost centered b eta T N tagU tagL ≤
      physicalActualCost centered b eta T N tagU tagL /
        ((if centered then 4 else 1)*b*height b) := by
  unfold physicalActualRelativeCost physicalActualCost
  rw [add_div, Finset.sum_div, Finset.sum_div]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg
      (PhysicalMinimum.reference_pos centered hb)
      (PhysicalMinimum.shadow_lower centered hb _ (hU i))
  · apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg
      (PhysicalMinimum.reference_pos centered hb)
      (PhysicalMinimum.shadow_lower centered hb _ (hL i))

theorem PhysicalFamilyConclusion.eventually_both_half_bounds
    {centered : Bool} {b eta : ℝ} (hb : 0 < b) {T : ℝ → ℝ}
    {tagU tagL : (N : ℕ) → Fin N → ℝ}
    {C : (N : ℕ) → Fin (2*N) → TriangularCovering.TriCylinder}
    (hC : PhysicalFamilyConclusion centered b eta T tagU tagL C)
    (hcost : scaledCost b eta T < physicalHalfReference centered b) :
    ∀ᶠ N in atTop, 0 < N ∧
      PhysicalBothHalfBounds centered b eta T N (tagU N) (tagL N) (C N) := by
  filter_upwards [hC.eventually_strict hcost] with N hN
  have htriangle := PhysicalMinimum.both_half_bounds centered hb (C N)
    (by simpa only [physicalHalfReference_eq] using hN.2.1)
  have hactual : physicalActualCost centered b eta T N (tagU N) (tagL N) <
      minimumShadowArea (modelBody centered b)/2 := by
    change physicalActualCost centered b eta T N (tagU N) (tagL N) <
      Similarity.minimumArea (modelBody centered b)/2
    rw [PhysicalMinimum.minimum_modelBody centered hb]
    simpa only [physicalHalfReference_eq] using hN.2.2
  have hU : ∀ i, ‖upperPhysicalAxis b eta (tagU N i)‖ = 1 := by
    intro i
    rw [← (hC.local_properties N hN.1 i).1]
    exact (C N (RadialPairedSweep.upperIndex i)).unit_axis
  have hL : ∀ i, ‖lowerPhysicalAxis b eta (tagL N i)‖ = 1 := by
    intro i
    rw [← (hC.local_properties N hN.1 i).2.1]
    exact (C N (RadialPairedSweep.lowerIndex i)).unit_axis
  have hrelative := actualRelative_le centered hb eta T N (tagU N) (tagL N) hU hL
  have hratio : physicalActualCost centered b eta T N (tagU N) (tagL N) /
      ((if centered then 4 else 1)*b*height b) < 1/2 := by
    apply (div_lt_iff₀ (PhysicalMinimum.reference_pos centered hb)).2
    have h := hN.2.2
    rw [physicalHalfReference_eq] at h
    linarith
  exact ⟨hN.1, htriangle.1, htriangle.2, hactual, hrelative.trans_lt hratio⟩

theorem physical_cap_normalized : PhysicalCapNormalizedStatement := by
  intro centered square b beta hb hbeta hbetamax
  filter_upwards [eventually_physicalModelCap_covers centered square hb hbeta,
    eventually_physicalModelCap_strict centered square hb hbeta hbetamax] with eta hcover hcost
  intro tagU tagL htagU htagL
  obtain ⟨C, hC⟩ := physical_family_of_sweep_cover centered b eta hb
    (physicalModelCap centered square b eta beta)
    (physicalModelCap_continuous centered square b eta beta).continuousOn
    (fun s _ => physicalModelCap_nonneg centered square b eta beta s hbeta.le)
    hcover tagU tagL htagU htagL
  exact ⟨C, hC, hC.eventually_both_half_bounds hb hcost⟩

end RadialPhysical

end

end OAI
