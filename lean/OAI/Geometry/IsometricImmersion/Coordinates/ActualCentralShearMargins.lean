import OAI.Geometry.IsometricImmersion.Calculus.BoundedClassInitialJet
import OAI.Geometry.IsometricImmersion.Pulses.PulseMomentGeometry

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem actual_central_sheared_solution_margins
    {g0 : MetricField} {kappa q0 r G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 ≤ r)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M))
    {p : Coord} (hx : |p 0| ≤ boundedClassWidth kappa M*r) (ht : |p 1| ≤ r) :
    let g := metricInShearCoordinates (perturbedMetric g0 eta.val) q0
    let zs := heightInShearCoordinates z q0
    inverseShearCoordinates q0 p ∈ modelSquare ∧
      (boundedClassSpeed kappa M)^2/(2*(M : ℝ)) ≤ |covHessian g zs p 0 0| ∧
      1/(M : ℝ) ≤ |covHessian g zs p 1 1| ∧
      1/(M : ℝ) ≤ heightEnergy g zs p ∧
      gaussianCurvature g p ≤ -(kappa/2) ∧
      (covHessian g zs p).det = gaussianCurvature g p*heightEnergy g zs p ∧
      (hessianQuotient g zs p)^2+gaussianCurvature g p*darbouxG g zs p < 0 := by
  dsimp only
  have hpC := inverseShear_slab_mem_centralBox
    ((by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M))
    hr hLr hq0 hx ht
  have hpS := centralBox_subset_modelSquare hpC
  have hq := bounded_class_slab_quotient_small_of_cap_radius hclass hG hd hr hq0 hrsmall
    hgB hdet hcenter hpS hx ht
  have hK : gaussianCurvature (perturbedMetric g0 eta.val) (inverseShearCoordinates q0 p) ≤ -kappa/2 :=
    (eta.property.2 _ hpC).le
  have hgeom := bounded_class_shear_estimates hclass hkappa hpS hK hq
  obtain ⟨hM,hadm,_,hHb,hEb⟩ := hclass
  obtain ⟨U,hU,hSU,hg,hz,hD,_,hyy,_⟩ := hadm
  have hpU := hSU hpS
  have h11 := (covHessian_shear_entries hg hz hU q0 hpU).1
  have hEnergy := heightEnergy_in_shear_coordinates (g := perturbedMetric g0 eta.val) hz hU q0 hpU
  have hCurvature := gaussianCurvature_in_shear_coordinates hg hU q0 hpU
  have hqShear := hessianQuotient_in_shear_coordinates hg hz hU q0 hpU (hyy _ hpS)
  have htimeeq :
      (hessianQuotient (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (heightInShearCoordinates z q0) p)^2+
        gaussianCurvature (metricInShearCoordinates (perturbedMetric g0 eta.val) q0) p*
          darbouxG (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
            (heightInShearCoordinates z q0) p =
        shearTimeFactor (perturbedMetric g0 eta.val) z q0 p := by
    unfold shearTimeFactor darbouxG
    rw [hqShear,hCurvature,hEnergy,h11]
  have htime : shearTimeFactor (perturbedMetric g0 eta.val) z q0 p < 0 := by
    have hv2 := half_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    linarith [hgeom.1]
  refine ⟨hpS,hgeom.2.1,?_,?_,?_,darboux_in_shear_coordinates hg hz hU q0 hpU (hD _ hpS),?_⟩
  · rw [h11]
    exact (hHb _ hpS).1
  · rw [hEnergy]
    exact hEb _ hpS
  · rw [hCurvature]
    simpa only [neg_div] using hK
  · rw [htimeeq]
    exact htime

theorem bounded_class_sheared_C3_on_actual_region
    {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight g M z) (q0 : ℝ) {S : Set Coord}
    (hS : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare) :
    CoordinateBound (heightInShearCoordinates z q0) S 3 ((2*(1+|q0|))^3*(M : ℝ)) := by
  obtain ⟨_,hadm,hjet,_,_⟩ := hclass
  obtain ⟨U,hU,hSU,_,hz,_,_,_,_⟩ := hadm
  have hzB : CoordinateBound z modelSquare 3 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hs := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzB hz hU hSU (Nat.cast_nonneg M) q0
  intro ds hds p hp
  exact hs ds hds p (hS p hp)

end SmoothLocal.Perturbation

end

end OAI
