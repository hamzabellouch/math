import OAI.Geometry.CylinderCovering.Radial.SqrtActualDefinitions
import OAI.Geometry.CylinderCovering.Radial.SqrtRealization
import OAI.Geometry.CylinderCovering.Radial.PairedActual
import OAI.Geometry.CylinderCovering.Radial.TetraGeometry

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace CylinderCovering.RadialPairedSweep

lemma actualRelativeCost_le {ε : ℝ} {R : ℝ → ℝ} {N : ℕ}
    (tagU tagL : Fin N → ℝ)
    (hU : ∀ i, ‖upperAxis (Real.sqrt 2) ε (tagU i)‖ = 1)
    (hL : ∀ i, ‖lowerAxis (Real.sqrt 2) ε (tagL i)‖ = 1) :
    actualRelativeCost ε R N tagU tagL ≤
      pairedActualCost (Real.sqrt 2) ε R N tagU tagL / (4 * Real.sqrt 2) := by
  unfold actualRelativeCost pairedActualCost
  rw [add_div, Finset.sum_div, Finset.sum_div]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg (by positivity)
      (reference_shadow_lower _ (hU i))
  · apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg (by positivity)
      (reference_shadow_lower _ (hL i))

end CylinderCovering.RadialPairedSweep
namespace CylinderCovering.RadialSqrtCap
open RadialPairedSweep

lemma actual_family {β ε : ℝ}
    (hcover : tetrahedron (Real.sqrt 2) ⊆
      upperSweep (Real.sqrt 2) ε (cap β ε) ∪ lowerSweep (Real.sqrt 2) ε (cap β ε))
    (tagU tagL : (N : ℕ) → Fin N → ℝ)
    (htagU : ∀ N, RadialRiemann.IsTagged (-1) 1 N (tagU N))
    (htagL : ∀ N, RadialRiemann.IsTagged (-1) 1 N (tagL N)) :
    ActualFamilyConclusion β ε tagU tagL := by
  obtain ⟨hgeom, hbound, hlim⟩ := paired_actual_sweeps (Real.sqrt 2) ε (by positivity)
    (cap β ε) (cap_continuous β ε).continuousOn (fun q _ => cap_nonneg β ε q)
    tagU tagL htagU htagL
  rw [physicalCost_sqrt_two] at hbound hlim
  refine ⟨?_, hbound, hlim⟩
  intro N hN
  obtain ⟨hprops, hU, hL⟩ := hgeom N hN
  refine ⟨hprops, ?_⟩
  intro z hz
  exact (hcover hz).elim (fun hu => Or.inl (hU z hu)) (fun hl => Or.inr (hL z hl))

theorem full_square_root_actual : ActualFullStatement := by
  constructor
  · intro β hβ
    obtain ⟨δ, hδ, hcov⟩ := exists_coverage_threshold hβ
    refine ⟨δ, hδ, ?_⟩
    intro ε he hεδ tagU tagL htagU htagL
    exact actual_family (hcov ε he hεδ) tagU tagL htagU htagL
  · intro β hβ hβmax
    obtain ⟨δc, hδc, hcov⟩ := exists_coverage_threshold hβ
    obtain ⟨δs, hδs, hsave⟩ := exists_saving_threshold hβ hβmax
    refine ⟨min δc δs, lt_min hδc hδs, ?_⟩
    intro ε he hεδ tagU tagL htagU htagL
    have hC := actual_family (hcov ε he (lt_of_lt_of_le hεδ (min_le_left _ _)))
      tagU tagL htagU htagL
    have hs := hsave ε he (lt_of_lt_of_le hεδ (min_le_right _ _))
    have hgap : 0 < 2 * Real.sqrt 2 * (1 - cost β ε) := by positivity
    have hevent := hC.2.1 (Real.sqrt 2 * (1 - cost β ε)) (by positivity)
    refine ⟨hC, ?_⟩
    filter_upwards [hevent, eventually_gt_atTop 0] with N hN hNpos
    have hstrict : pairedActualCost (Real.sqrt 2) ε (cap β ε) N (tagU N) (tagL N) <
        2 * Real.sqrt 2 := by nlinarith only [hN, hgap]
    refine ⟨hNpos, ?_, ?_⟩
    · rw [reference_minimum]
      nlinarith only [hstrict]
    · have hprops := (hC.1 N hNpos).1
      apply (actualRelativeCost_le (R := cap β ε) (tagU N) (tagL N)
        (fun i => (hprops i).1.1) (fun i => (hprops i).2.1)).trans_lt
      apply (div_lt_iff₀ (by positivity : 0 < 4 * Real.sqrt 2)).mpr
      nlinarith only [hstrict]

theorem complete_square_root_cap : CompleteStatement :=
  ⟨full_square_root_cap, full_square_root_actual, reference_area, half_cost⟩

end CylinderCovering.RadialSqrtCap

end

end OAI
