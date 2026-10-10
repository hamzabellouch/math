import Mathlib
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarBand
import OAI.Analysis.Conductivity.Geometry.CollarLip

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem exists_smooth_sourceCollar_cutoff {b η : ℝ} (hη : 0<η)
    (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100) :
    ∃ χ : (Fin 3 → ℝ) → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ x,|χ x|≤1) ∧ tsupport χ⊆sourceClosedCollarBand (b-η) (b+η) ∧
      (∀ᶠ x in 𝓝ˢ (sourceClosedCollarBand (b-η/2) (b+η/2)),χ x=1) := by
  have ht := (sourceCollarTime_lipschitz.choose_spec).continuous
  have hbig := isCompact_sourceClosedCollarBand hl hr
  have hsmall := isCompact_sourceClosedCollarBand
    (show -(1:ℝ)/100≤b-η/2 by linarith) (show b+η/2≤(1:ℝ)/100 by linarith)
  have hi : sourceClosedCollarBand (b-η/2) (b+η/2)⊆
      interior (sourceClosedCollarBand (b-η) (b+η)) := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have hxo : sourceCollarTime x∈Ioo (b-η) (b+η) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    exact mem_of_superset (ht.continuousAt (isOpen_Ioo.mem_nhds hxo)) (fun y hy => ⟨hy.1.le,hy.2.le⟩)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hsmall.isClosed hi (n:=↑(⊤:ℕ∞))
  refine ⟨χ,χ.contMDiff.contDiff,HasCompactSupport.intro hbig hχ0,?_,?_,hχ1⟩
  · intro x
    rw [abs_of_nonneg (hχb x).1]
    exact (hχb x).2
  · apply closure_minimal _ hbig.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)

end ScalarConductivity

end
end

end OAI
