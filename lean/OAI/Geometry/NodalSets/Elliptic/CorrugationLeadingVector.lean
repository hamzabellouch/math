import OAI.Geometry.NodalSets.Charts.CorrugationFrameBounds
import OAI.Geometry.NodalSets.Elliptic.CorrugationGlobalJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def corrugationFastVector (amp : ℝ) (e : Coord ≃L[ℝ] Coord) (z : ℝ × ℝ) : Coord :=
  fderiv ℝ (corrugationPeriodicWell amp) z (1,0) • e (Pi.single 2 1) +
  fderiv ℝ (corrugationPeriodicWell amp) z (0,1) • e (Pi.single 3 1)

def corrugationLeadingVector (amp t : ℝ) (e : Coord ≃L[ℝ] Coord) (z : ℝ × ℝ) : Coord :=
  e (Pi.single 0 1)+t • corrugationFastVector amp e z

lemma pair_covector_expansion (d : (ℝ × ℝ) →L[ℝ] ℝ) (v : ℝ × ℝ) :
    d v = d (1,0)*v.1+d (0,1)*v.2 := by
  have he : v = v.1 • (1,0)+v.2 • (0,1) := by ext <;> simp
  conv_lhs => rw [he,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

lemma corrugationFastVector_pair (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (amp : ℝ) (z : ℝ × ℝ) (v : Coord) :
    g (corrugationFastVector amp e z) v =
      fderiv ℝ (corrugationPeriodicWell amp) z
        ((frozenFrameCovector e 2).prod (frozenFrameCovector e 3) v) := by
  rw [pair_covector_expansion]
  simp only [corrugationFastVector,map_add,map_smul,add_apply,
    smul_apply,smul_eq_mul,ContinuousLinearMap.prod_apply]
  rw [frozenFrameCovector_metric g e he,frozenFrameCovector_metric g e he]

lemma corrugationFastVector_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c amp : ℝ} (hc : 0 < c) (hg : ∀ v, c*‖v‖^2 ≤ g v v)
    (ha : 0 ≤ amp) (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (z : ℝ × ℝ) :
    ‖corrugationFastVector amp e z‖ ≤
      4*corrugationSlope amp (1/4) (corrugationCellRadius z)*(1+c⁻¹) := by
  have hd := corrugationPeriodicWell_global_derivative_bound ha z
  have h2 := metric_unit_coordinate_bound g hc hg (e (Pi.single 2 1)) (by simpa using he 2 2)
  have h3 := metric_unit_coordinate_bound g hc hg (e (Pi.single 3 1)) (by simpa using he 3 3)
  have hd2 : |fderiv ℝ (corrugationPeriodicWell amp) z (1,0)| ≤
      2*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
    simpa using ((fderiv ℝ (corrugationPeriodicWell amp) z).le_opNorm (1,0)).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg (1,0)))
  have hd3 : |fderiv ℝ (corrugationPeriodicWell amp) z (0,1)| ≤
      2*corrugationSlope amp (1/4) (corrugationCellRadius z) := by
    simpa using ((fderiv ℝ (corrugationPeriodicWell amp) z).le_opNorm (0,1)).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg (0,1)))
  have hl := corrugationSlope_nonneg (R := (1/4:ℝ)) ha (corrugationCellRadius_properties z).1
  calc
    _ ≤ ‖fderiv ℝ (corrugationPeriodicWell amp) z (1,0) • e (Pi.single 2 1)‖+
        ‖fderiv ℝ (corrugationPeriodicWell amp) z (0,1) • e (Pi.single 3 1)‖ := norm_add_le _ _
    _ ≤ (2*corrugationSlope amp (1/4) (corrugationCellRadius z))*(1+c⁻¹)+
        (2*corrugationSlope amp (1/4) (corrugationCellRadius z))*(1+c⁻¹) := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul hd2 h2 (norm_nonneg _) (by positivity))
        (mul_le_mul hd3 h3 (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma corrugationLeadingVector_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c amp t : ℝ} (hc : 0 < c) (hg : ∀ v, c*‖v‖^2 ≤ g v v)
    (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (z : ℝ × ℝ) : ‖corrugationLeadingVector amp t e z‖ ≤ 5*(1+c⁻¹) := by
  have h0 := metric_unit_coordinate_bound g hc hg (e (Pi.single 0 1)) (by simpa using he 0 0)
  have hf := corrugationFastVector_bound g hc hg ha e he z
  have hl := corrugationSlope_le_one ha ha1 (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)
    (corrugationCellRadius_properties z).1
  have hf' : ‖corrugationFastVector amp e z‖ ≤ 4*(1+c⁻¹) := hf.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  calc
    _ ≤ ‖e (Pi.single 0 1)‖+‖t • corrugationFastVector amp e z‖ := norm_add_le _ _
    _ ≤ (1+c⁻¹)+1*(4*(1+c⁻¹)) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
      exact add_le_add h0 (mul_le_mul ht1 hf' (norm_nonneg _) (by norm_num))
    _ = _ := by ring

end
end Yau.Geometry

end OAI
