import OAI.Geometry.CylinderCovering.Ruled.LocalCylinder
import OAI.Geometry.CylinderCovering.Ruled.CellCost
import OAI.Geometry.CylinderCovering.Convexity.CompactProductEigenframes

namespace OAI

noncomputable section
open Set Metric MeasureTheory
namespace CylinderCovering.ProductLocal
open RuledApproximation

lemma hyperbolicAt_trace_det {M : ℝ} (hM : 0 < M)
    {v : Plane → Plane} {p : Plane} (h : HyperbolicAt M v p) :
    LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 ∧
      LinearMap.det (fderiv ℝ v p).toLinearMap < 0 := by
  obtain ⟨lam,hMl,_,hp,hm⟩ := h
  have hlam : 0 < lam := (mul_pos_iff_of_pos_left hM).mp hMl
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly,Polynomial.IsRoot,plane_charpoly] at hp hm
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] at hp hm
  have ht : LinearMap.trace ℝ Plane (fderiv ℝ v p).toLinearMap = 0 := by nlinarith
  refine ⟨ht,?_⟩
  rw [ht] at hp
  nlinarith [sq_pos_of_pos hlam]

lemma hyperbolicAt_exists_unit_eigenframe {M : ℝ} (hM : 0 < M)
    {v : Plane → Plane} {p : Plane} (h : HyperbolicAt M v p) :
    ∃ lam : ℝ, ∃ L : (ℝ × ℝ) ≃L[ℝ] Plane,
      0 < M*lam ∧ M*lam < 1 ∧ IsUnitEigenframe (fderiv ℝ v p) lam L := by
  have htd := hyperbolicAt_trace_det hM h
  obtain ⟨lam,hMl,hMl1,hplus,_⟩ := h
  have hlam : 0 < lam := (mul_pos_iff_of_pos_left hM).mp hMl
  have heq := positive_eigenvalue_eq_sqrt (fderiv ℝ v p) htd.1 htd.2 hlam hplus
  obtain ⟨L,hL⟩ := exists_unit_eigenframe (fderiv ℝ v p) htd.1 htd.2
  exact ⟨lam,L,hMl,hMl1,by simpa only [heq] using hL⟩

theorem local_proof : LocalStatement := by
  intro D v h M hD hDne hh hM hvnear hhyper eta tau gamma heta htau htau1 hgamma hpad hratio
  obtain ⟨U,hU,hDU,hv⟩ := hvnear
  have hder : ContinuousOn (fderiv ℝ v) D := by
    intro p hp
    exact ((hv.contDiffAt (hU.mem_nhds (hDU hp))).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  obtain ⟨N,hN,hNall⟩ := compact_uniform_eigenframe_inverse hD hder
    (fun p hp => (hyperbolicAt_trace_det hM (hhyper p hp)).1)
    (fun p hp => (hyperbolicAt_trace_det hM (hhyper p hp)).2)
  obtain ⟨rA,hrA,hA⟩ := uniform_intercept_containment hD hU hDU hv hM hN htau hgamma
  obtain ⟨rW,hrW,hW⟩ := uniform_weight_on_cells hD (hv.continuousOn.mono hDU) h heta
  refine ⟨min rA rW,lt_min hrA hrW,?_⟩
  intro p hp lam L hL hML0 hML1 rho hrho hrho0 hGD
  have hlam : 0 < lam := (mul_pos_iff_of_pos_left hM).mp hML0
  have hri : rho < rA := hrho0.trans_le (min_le_left _ _)
  have hrw : rho < rW := hrho0.trans_le (min_le_right _ _)
  let G := affineCell p rho L (ProductCells.parameterCell tau)
  let P := affineCell p rho L (ProductCells.interceptCell tau gamma)
  let C := projectedCylinder h (v p) P
  refine ⟨C,rfl,projectedCylinder_carrier h (v p) P,?_,?_,?_⟩
  · exact ProductCells.pair_frame_productCylinder_openBounded L p (v p) hrho hh tau gamma
  · apply ruled_subset_projectedCylinder
    exact hA p hp lam L hL hlam.le hML1.le (hNall p hp lam L hlam hL).2 rho hrho hri
  · apply projectedCylinder_cost (parameter_affineCell_isCompact p rho tau L)
      (hv.continuousOn.mono (hGD.trans hDU)) hh heta.le p hratio
    · exact ProductCells.pair_frame_intercept_area L p hrho htau htau1 hgamma.le hpad
    · exact hW p hp lam rho tau L hL hrho hrw hGD

end CylinderCovering.ProductLocal

end

end OAI
