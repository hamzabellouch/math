import OAI.Geometry.IsometricImmersion.Darboux.QContainingRectangle
import OAI.Geometry.IsometricImmersion.Coordinates.BoundedPatchSlabGeometry

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem centralBox_subset_modelOpenSquare : centralBox ⊆ modelOpenSquare := by
  intro p hp
  change p 0 ∈ Ioo (-3 : ℝ) 3 ∧ p 1 ∈ Ioo (-3 : ℝ) 3
  exact ⟨⟨by linarith [hp.1 0],by linarith [hp.2 0]⟩,
    ⟨by linarith [hp.1 1],by linarith [hp.2 1]⟩⟩

theorem actual_patch_closed_strip_Hxx_floor
    {g0 : MetricField} {kappa q0 r b G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa)
    {z : Coord → ℝ} (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 ≤ r) (hb : b ≤ 0)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M))
    {p : Coord} (hp : p ∈ closedRectangle (-(boundedClassWidth kappa M*r))
      (boundedClassWidth kappa M*r) (-r) b) :
    inverseShearCoordinates q0 p ∈ modelOpenSquare ∧
      (boundedClassSpeed kappa M)^2/(2*(M : ℝ)) ≤
        |covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
          (heightInShearCoordinates z q0) p 0 0| := by
  have hx : |p 0| ≤ boundedClassWidth kappa M*r := abs_le.mpr hp.1
  have hy : |p 1| ≤ r := abs_le.mpr ⟨hp.2.1,(hp.2.2.trans hb).trans hr⟩
  have hpC := inverseShear_slab_mem_centralBox
    ((by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M))
    hr hLr hq0 hx hy
  have hpS := centralBox_subset_modelSquare hpC
  have hq := bounded_class_slab_quotient_small_of_cap_radius hclass hG hd hr hq0 hrsmall
    hgB hdet hcenter hpS hx hy
  have hgeom := bounded_class_shear_estimates hclass hkappa hpS (eta.property.2 _ hpC).le hq
  exact ⟨centralBox_subset_modelOpenSquare hpC,hgeom.2.1⟩

theorem exists_actual_patch_Q_rectangle
    {g0 : MetricField} {kappa q0 r b G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa)
    {z : Coord → ℝ} (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 < r)
    (hab : -r ≤ b) (hb : b ≤ 0)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M)) :
    ∃ radius lo hi : ℝ, boundedClassWidth kappa M*r < radius ∧ lo < -r ∧ b < hi ∧
      SmoothPositiveOn (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (coordinateRectangle radius lo hi) ∧
      ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) (coordinateRectangle radius lo hi) ∧
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
          (heightInShearCoordinates z q0) p).det =
            gaussianCurvature (metricInShearCoordinates (perturbedMetric g0 eta.val) q0) p*
              heightEnergy (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
                (heightInShearCoordinates z q0) p) ∧
      (∀ p ∈ coordinateRectangle radius lo hi,
        covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
          (heightInShearCoordinates z q0) p 0 0 ≠ 0) := by
  obtain ⟨U,_,hSU,hg,hz,hD,_,_,_⟩ := hclass.2.1
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (perturbedMetric g0 eta.val) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  let V := inverseShearCoordinates q0 ⁻¹' modelOpenSquare
  have hV : IsOpen V := modelOpenSquare_isOpen.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgs := metricInShearCoordinates_smoothPositive hgO q0
  have hzs := heightInShearCoordinates_contDiffOn hzO q0
  have hgeom (p : Coord) (hp : p ∈ closedRectangle (-(boundedClassWidth kappa M*r))
      (boundedClassWidth kappa M*r) (-r) b) :=
    actual_patch_closed_strip_Hxx_floor eta hclass hG hd hkappa hr.le hb hLr hq0 hrsmall
      hgB hdet hcenter hp
  have hxx : ∀ p ∈ closedRectangle (-(boundedClassWidth kappa M*r))
      (boundedClassWidth kappa M*r) (-r) b,
      covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    intro p hp
    exact abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hclass.1).trans_le (hgeom p hp).2)
  obtain ⟨radius,lo,hi,hradius,hlo,hhi,hrect,hxxrect⟩ :=
    exists_actual_Q_containing_rectangle hgs hzs hV
      (mul_pos (boundedClassWidth_pos kappa M) hr) hab (fun p hp => (hgeom p hp).1) hxx
  refine ⟨radius,lo,hi,hradius,hlo,hhi,
    ⟨fun i j => (hgs.1 i j).mono hrect,fun p hp => hgs.2 p (hrect hp)⟩,
    hzs.mono hrect,?_,hxxrect⟩
  intro p hp
  have hpO : inverseShearCoordinates q0 p ∈ modelOpenSquare := hrect hp
  exact darboux_in_shear_coordinates hgO hzO modelOpenSquare_isOpen q0 hpO
    (hD _ (modelOpenSquare_subset hpO))

end SmoothLocal.Perturbation

end

end OAI
