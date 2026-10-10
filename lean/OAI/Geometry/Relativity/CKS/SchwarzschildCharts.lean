import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildModel

namespace OAI

noncomputable section
open Set Manifold Bundle Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

attribute [local instance] halfSpaceDimension_neZero

lemma transition_source (a b : Sphere) :
    ((productChart a).symm ≫ₕ productChart b).source =
      (fun z : H3 => dropPlane z.val) ⁻¹' ((chartAt E2 a).symm ≫ₕ chartAt E2 b).source := by
  ext z
  simp only [OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.symm_source,
    mem_inter_iff,mem_preimage,productChart_target,productChart_source,productChart_symm]

lemma transition_maps (a b : Sphere) :
    MapsTo dropPlane (I3.symm ⁻¹' ((productChart a).symm ≫ₕ productChart b).source ∩ range I3)
      ((extChartAt I2 a).symm ≫ extChartAt I2 b).source := by
  intro z hz
  have he : (I3.symm z).val = z := I3.right_inv hz.2
  have h := hz.1
  rw [transition_source] at h
  change dropPlane (I3.symm z).val ∈ ((chartAt E2 a).symm ≫ₕ chartAt E2 b).source at h
  rw [he] at h
  simpa only [I2,extChartAt_model_space_eq_id,mfld_simps] using h

lemma transition_formula (a b : Sphere) {z : E3} (hz : z ∈ range I3) :
    I3 (((productChart a).symm ≫ₕ productChart b) (I3.symm z)) =
      join (z 0,((extChartAt I2 a).symm ≫ extChartAt I2 b) (dropPlane z)) := by
  have he : (I3.symm z).val = z := I3.right_inv hz
  change join ((I3.symm z).val 0,
    chartAt E2 b ((chartAt E2 a).symm (dropPlane (I3.symm z).val))) = _
  rw [he]
  rfl

lemma boundary_iff (p : Exterior) : p ∈ I3.boundary Exterior ↔ p.1.val = 0 := by
  rw [CKSBoundarySurface.boundary_iff_zero p p (mem_chart_source H3 p)]
  rfl
lemma interior_iff (p : Exterior) : p ∈ I3.interior Exterior ↔ 0 < p.1.val := by
  have h := (I3.isBoundaryPoint_iff_not_isInteriorPoint p)
  change p ∈ I3.boundary Exterior ↔ p ∉ I3.interior Exterior at h
  rw [boundary_iff] at h
  have hp := p.1.property
  constructor
  · intro hi
    by_contra hn
    have hz : p.1.val = 0 := le_antisymm (le_of_not_gt hn) hp
    exact h.mp hz hi
  · intro hp0
    by_contra hi
    have hz := h.mpr hi
    linarith

end CKSSchwarzschild

end

end OAI
