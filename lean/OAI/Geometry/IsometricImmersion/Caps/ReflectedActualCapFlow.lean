import OAI.Geometry.IsometricImmersion.Caps.BoundedClassReflection
import OAI.Geometry.IsometricImmersion.Caps.VaryingMetricUpperCap

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection SmoothLocal.Model

theorem exists_actual_reflected_capInductionFlow
    {g0 : MetricField} {kappa G Z d c e0 : ℝ} (eta : metricPatchSet g0 kappa)
    {U : Set Coord} {z : Coord → ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hg : SmoothPositiveOn (perturbedMetric g0 eta.val) U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hh : CapInductionHeight (perturbedMetric g0 eta.val) U Z c e0 z)
    (hk : 0 < kappa) (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ (W : Set Coord) (Y : ℝ → ℝ → ℝ),
      CapInductionFlow (reflectedMetric (perturbedMetric g0 eta.val)) (reflectPoint ⁻¹' U)
        G Z d c e0 kappa (reflectedScalar z) Y W := by
  have hsum : reflectedMetric g0+reflectedMetric (perturbationTensor eta.val) =
      reflectedMetric (perturbedMetric g0 eta.val) :=
    (reflectedMetric_add g0 (perturbationTensor eta.val)).symm
  have hgR : SmoothPositiveOn
      (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) (reflectPoint ⁻¹' U) := by
    rw [hsum]
    exact reflectedMetric_smoothPositive hg
  have hhR : CapInductionHeight
      (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val))
      (reflectPoint ⁻¹' U) Z c e0 (reflectedScalar z) := by
    rw [hsum]
    exact reflected_capInductionHeight hg hU hSU hh
  have hBR : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q =>
        (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) q i j) p‖ ≤ G := by
    rw [hsum]
    exact reflectedMetric_C8 hgB
  have hdetR : ∀ p ∈ modelSquare,
      d ≤ |((reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) p).det| := by
    intro p hp
    rw [hsum,reflectedMetric_det]
    exact hdet _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hcentralR : ∀ p ∈ centralBox,
      gaussianCurvature (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) p < -kappa/2 := by
    intro p hp
    have hpr : reflectPoint p ∈ centralBox :=
      (reflectPoint_mem_symmetricSquare (1/5) p).mpr hp
    rw [hsum,reflectedMetric_curvature hg hU (hSU (centralBox_subset_modelSquare hpr))]
    exact eta.property.2 _ hpr
  obtain ⟨W,Y,hflow⟩ := exists_capInductionFlow hgR (reflectedDomain_isOpen hU)
    (reflectedDomain_contains_modelSquare hSU) hG hZ hd hc he0 hBR hdetR hhR hk
    (reflectedMetric_model hg0 hU hbackground)
    (reflectedMetric_support_patch (perturbationTensor_tsupport_subset eta.val)) hcentralR
  exact ⟨W,Y,by simpa only [hsum] using hflow⟩

end SmoothLocal.Perturbation

end

end OAI
