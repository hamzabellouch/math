import OAI.Geometry.IsometricImmersion.Caps.PulseReflection
import OAI.Geometry.IsometricImmersion.Immersions.BoundedHeightClasses
import OAI.Geometry.IsometricImmersion.Metrics.MetricPatchOpen

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.Flow.Reflection

theorem PatchAdmissibleHeight.reflected {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) :
    PatchAdmissibleHeight (reflectedMetric g) (reflectedScalar z) := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := h
  have hmem {p : Coord} (hp : p ∈ modelSquare) : reflectPoint p ∈ U :=
    hSU ((reflectPoint_mem_modelSquare p).mpr hp)
  refine ⟨reflectPoint ⁻¹' U, reflectedDomain_isOpen hU,
    reflectedDomain_contains_modelSquare hSU, reflectedMetric_smoothPositive hg,
    reflectedScalar_contDiffOn hz, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [reflectedMetric_hessian_det hg hz hU (hmem hp),
      reflectedMetric_curvature hg hU (hmem hp), reflectedMetric_energy hz hU (hmem hp)]
    exact hD _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_energy hz hU (hmem hp)]
    exact hE _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_hessian_entry hg hz hU (hmem hp)]
    simpa only [ite_true] using hyy _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_quotient hg hz hU (hmem hp),abs_neg]
    exact hq _ ((reflectPoint_mem_modelSquare p).mpr hp)

theorem BoundedAdmissibleHeight.reflected {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (h : BoundedAdmissibleHeight g M z) :
    BoundedAdmissibleHeight (reflectedMetric g) M (reflectedScalar z) := by
  obtain ⟨hM,ha,hB,hyy,hE⟩ := h
  have har := ha.reflected
  obtain ⟨U,hU,hSU,hg,hz,hD,hpos,hne,hq⟩ := ha
  refine ⟨hM,har,reflectedScalar_C8 hB,?_,?_⟩
  · intro p hp
    have hpr := (reflectPoint_mem_modelSquare p).mpr hp
    rw [reflectedMetric_hessian_entry hg hz hU (hSU hpr)]
    simpa only [ite_true] using hyy _ hpr
  · intro p hp
    have hpr := (reflectPoint_mem_modelSquare p).mpr hp
    rw [reflectedMetric_energy hz hU (hSU hpr)]
    exact hE _ hpr

theorem bounded_class_reflected_center {g : MetricField} {z : Coord → ℝ} {M : ℕ}
    (h : BoundedAdmissibleHeight g M z) (q0 : ℝ) :
    |hessianQuotient (reflectedMetric g) (reflectedScalar z) 0-(-q0)| =
      |hessianQuotient g z 0-q0| := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := h.2.1
  have hzero : (0 : Coord) ∈ modelSquare := by constructor <;> intro i <;> norm_num
  have hrzero : reflectPoint (0 : Coord) = 0 := by ext i; fin_cases i <;> simp
  have hzeroU : reflectPoint (0 : Coord) ∈ U := by
    simpa only [hrzero] using hSU hzero
  rw [reflectedMetric_quotient hg hz hU (p := 0) hzeroU,hrzero]
  have he : -hessianQuotient g z 0-(-q0) = -(hessianQuotient g z 0-q0) := by ring
  rw [he,abs_neg]

end SmoothLocal.Geometry

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection

theorem reflected_actual_metric_zero_patch {g0 : MetricField} {kappa : ℝ}
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z) :
    (0 : SymmetricPerturbation) ∈
      metricPatchSet (reflectedMetric (perturbedMetric g0 eta.val)) kappa := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := hclass.2.1
  apply zero_mem_metricPatchSet
  · intro p hp
    exact (reflectedMetric_smoothPositive hg).2 p
      (hSU ((reflectPoint_mem_modelSquare p).mpr hp))
  · intro p hp
    have hpr : reflectPoint p ∈ centralBox :=
      (reflectPoint_mem_symmetricSquare (1/5) p).mpr hp
    rw [reflectedMetric_curvature hg hU (hSU (centralBox_subset_modelSquare hpr))]
    exact eta.property.2 _ hpr

end SmoothLocal.Perturbation

end

end OAI
