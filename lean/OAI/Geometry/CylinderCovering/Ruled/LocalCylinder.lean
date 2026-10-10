import OAI.Geometry.CylinderCovering.Ruled.LocalGeometry
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
open Set Metric MeasureTheory
namespace CylinderCovering.ProductLocal
open RuledApproximation

lemma parameter_affineCell_isCompact (p : Plane) (rho tau : ℝ)
    (L : (ℝ × ℝ) ≃L[ℝ] Plane) :
    IsCompact (affineCell p rho L (ProductCells.parameterCell tau)) :=
  (ProductCells.closedCell_isCompact 1 tau).image
    ((L.continuous.const_smul rho).const_add p)

lemma weight_integral_bound {G : Set Plane} (hG : IsCompact G)
    {v : Plane → Plane} (hv : ContinuousOn v G) (h : ℝ) (p : Plane) (eta : ℝ)
    (hratio : ∀ q ∈ G, physicalWeight h (v p) ≤ (1+eta)*physicalWeight h (v q)) :
    physicalWeight h (v p) * volume.real G ≤
      (1+eta)*(∫ q in G, physicalWeight h (v q)) := by
  have hj : ContinuousOn (fun q => physicalWeight h (v q)) G :=
    (physicalWeight_continuous h).comp_continuousOn hv
  have ht := setIntegral_mono_on (μ := volume)
    (integrableOn_const hG.measure_lt_top.ne)
    ((continuousOn_const.mul hj).integrableOn_compact hG)
    hG.measurableSet hratio
  simpa only [Pi.mul_apply,setIntegral_const,smul_eq_mul,integral_const_mul,mul_comm] using ht

lemma projectedCylinder_cost {G U : Set Plane} (hG : IsCompact G)
    {v : Plane → Plane} (hv : ContinuousOn v G) {h eta R : ℝ}
    (hh : 0 < h) (heta : 0 ≤ eta) (p : Plane)
    (hR : R ≤ 1+eta) (harea : volume.real U = R*volume.real G)
    (hratio : ∀ q ∈ G, physicalWeight h (v p) ≤ (1+eta)*physicalWeight h (v q)) :
    (projectedCylinder h (v p) U).area ≤
      h*(1+eta)^2*(∫ q in G,physicalWeight h (v q)) := by
  have hj := physicalWeight_pos h (v p)
  have hvol : 0 ≤ volume.real G := measureReal_nonneg
  have hw := weight_integral_bound hG hv h p eta hratio
  rw [projectedCylinder_area hh,harea]
  calc h*(R*volume.real G)*physicalWeight h (v p)
      = h*R*(physicalWeight h (v p)*volume.real G) := by ring
    _ ≤ h*(1+eta)*(physicalWeight h (v p)*volume.real G) := by gcongr
    _ ≤ h*(1+eta)*((1+eta)*(∫ q in G,physicalWeight h (v q))) := by
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = h*(1+eta)^2*(∫ q in G,physicalWeight h (v q)) := by ring

lemma uniform_weight_on_cells {D : Set Plane} (hD : IsCompact D)
    {v : Plane → Plane} (hv : ContinuousOn v D) (h : ℝ)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ rho0 : ℝ, 0 < rho0 ∧ ∀ p ∈ D,
      ∀ (lam rho tau : ℝ) (L : (ℝ × ℝ) ≃L[ℝ] Plane),
      IsUnitEigenframe (fderiv ℝ v p) lam L →
      0 < rho → rho < rho0 →
      affineCell p rho L (ProductCells.parameterCell tau) ⊆ D →
      ∀ q ∈ affineCell p rho L (ProductCells.parameterCell tau),
        physicalWeight h (v p) ≤ (1+eta)*physicalWeight h (v q) := by
  obtain ⟨r,hr,hratio⟩ := compact_positive_weight_ratio hD
    ((physicalWeight_continuous h).comp_continuousOn hv)
    (fun p _ => physicalWeight_pos h (v p)) heta
  refine ⟨r/3,by positivity,?_⟩
  intro p hp lam rho tau L hL hrho hrhor hGD q hq
  apply hratio p hp q (hGD hq)
  rw [dist_comm,dist_eq_norm]
  have hd := affineCell_distance hL hrho.le hq
  linarith

lemma ruled_subset_projectedCylinder {h M : ℝ} {v : Plane → Plane}
    {p : Plane} {G U : Set Plane}
    (hintercept : ∀ q ∈ G, ∀ x : ℝ, |x| ≤ M → q+x • (v q-v p) ∈ U) :
    physicalRuled h G v M ⊆ (projectedCylinder h (v p) U).carrier := by
  rintro z ⟨q,hq,x,hx,rfl⟩
  exact physicalRuled_mem_projectedCylinder h v q (v p) x (hintercept q hq x hx)

end CylinderCovering.ProductLocal

end

end OAI
