import OAI.Geometry.NodalSets.Elliptic.CorrugationLeadingVector

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def frozenPlaneVector (e : Coord ≃L[ℝ] Coord) (α β : ℝ) : Coord :=
  α • e (Pi.single 2 1)+β • e (Pi.single 3 1)

lemma frozenPlaneVector_pair (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (α β γ δ : ℝ) :
    g (frozenPlaneVector e α β) (frozenPlaneVector e γ δ) = α*γ+β*δ := by
  simp [frozenPlaneVector,map_add,map_smul,he,Fin.ext_iff]
  ring

lemma frozenPlaneVector_axis_pair (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (α β : ℝ) (i : Fin 4) (hi : i < 2) :
    g (e (Pi.single i 1)) (frozenPlaneVector e α β) = 0 ∧
    g (frozenPlaneVector e α β) (e (Pi.single i 1)) = 0 := by
  have hi2 : i ≠ 2 := by omega
  have hi3 : i ≠ 3 := by omega
  simp [frozenPlaneVector,map_add,map_smul,he,hi2,hi3,Ne.symm hi2,Ne.symm hi3]

lemma frozenPlaneVector_rotating_frame (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    {α β : ℝ} (hunit : α^2+β^2 = 1) :
    g (frozenPlaneVector e α β) (frozenPlaneVector e α β) = 1 ∧
    g (frozenPlaneVector e (-β) α) (frozenPlaneVector e (-β) α) = 1 ∧
    g (frozenPlaneVector e α β) (frozenPlaneVector e (-β) α) = 0 ∧
    g (frozenPlaneVector e (-β) α) (frozenPlaneVector e α β) = 0 := by
  simp only [frozenPlaneVector_pair g e he]
  constructor
  · nlinarith only [hunit]
  constructor
  · nlinarith only [hunit]
  constructor <;> ring

lemma frozen_radial_covector (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (z : ℝ × ℝ) (r : ℝ) (v : Coord) :
    radialComponent z ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v) r =
      g (frozenPlaneVector e (z.1/r) (z.2/r)) v := by
  simp only [radialComponent,ContinuousLinearMap.prod_apply,frozenPlaneVector,map_add,map_smul,
    add_apply,smul_apply,smul_eq_mul]
  rw [frozenFrameCovector_metric g e he,frozenFrameCovector_metric g e he]
  ring

lemma frozen_angular_covector (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (z : ℝ × ℝ) (r : ℝ) (v : Coord) :
    angularComponent z ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v) r =
      g (frozenPlaneVector e (-(z.2/r)) (z.1/r)) v := by
  simp only [angularComponent,ContinuousLinearMap.prod_apply,frozenPlaneVector,map_add,map_smul,
    add_apply,smul_apply,smul_eq_mul]
  rw [frozenFrameCovector_metric g e he,frozenFrameCovector_metric g e he]
  ring

lemma corrugationFastVector_radial (amp : ℝ) (e : Coord ≃L[ℝ] Coord) (z : ℝ × ℝ)
    (hr : corrugationCellRadius z ≠ 0) :
    corrugationFastVector amp e z = corrugationSlope amp (1/4) (corrugationCellRadius z) •
      frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
        ((corrugationCellPoint z).2/corrugationCellRadius z) := by
  unfold corrugationFastVector
  rw [(corrugationPeriodicWell_global_radial_jets amp z (0,0) (1,0) hr).1,
    (corrugationPeriodicWell_global_radial_jets amp z (0,0) (0,1) hr).1]
  simp [radialComponent,frozenPlaneVector,smul_add,smul_smul]

lemma corrugation_cell_unit_coefficients (z : ℝ × ℝ) (hr : corrugationCellRadius z ≠ 0) :
    ((corrugationCellPoint z).1/corrugationCellRadius z)^2+
      ((corrugationCellPoint z).2/corrugationCellRadius z)^2 = 1 := by
  have hh := (corrugationCellRadius_properties z).2
  field_simp
  nlinarith only [hh]

lemma corrugationLeadingVector_metric_length (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp t : ℝ) (z : ℝ × ℝ) (hr : corrugationCellRadius z ≠ 0) :
    g (corrugationLeadingVector amp t e z) (corrugationLeadingVector amp t e z) =
      1+(t*corrugationSlope amp (1/4) (corrugationCellRadius z))^2 := by
  let u := frozenPlaneVector e ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z)
  have huu : g u u = 1 := (frozenPlaneVector_rotating_frame g e he
    (corrugation_cell_unit_coefficients z hr)).1
  have hu0 := frozenPlaneVector_axis_pair g e he
    ((corrugationCellPoint z).1/corrugationCellRadius z)
    ((corrugationCellPoint z).2/corrugationCellRadius z) 0 (by decide)
  change g (e (Pi.single 0 1)) u = 0 ∧ g u (e (Pi.single 0 1)) = 0 at hu0
  change g (e (Pi.single 0 1)+t • corrugationFastVector amp e z)
    (e (Pi.single 0 1)+t • corrugationFastVector amp e z) = _
  rw [corrugationFastVector_radial amp e z hr]
  change g (e (Pi.single 0 1)+t • (corrugationSlope amp (1/4) (corrugationCellRadius z) • u))
    (e (Pi.single 0 1)+t • (corrugationSlope amp (1/4) (corrugationCellRadius z) • u)) = _
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,huu,hu0.1,hu0.2,he]
  simp
  ring

end
end Yau.Geometry

end OAI
