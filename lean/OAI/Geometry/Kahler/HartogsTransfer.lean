import OAI.Geometry.Kahler.HartogsTopologySupport

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology Metric
open scoped ContDiff NNReal
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs

theorem metric_transfer : MetricTransfer := by
  intro c C hc hC
  refine ⟨metricThreshold c C,metricThreshold_pos hc hC,?_⟩
  intro φ hφ hctl hj lam hlam
  have hpsh := chartControl_psh hφ hc.le hctl
  have hlp := (metricThreshold_pos hc hC).trans_le hlam
  exact ⟨hartogs_contractible φ hφ.continuousOn, hartogsMetric_isKahler hφ hpsh hlp,
    hartogsMetric_geodesicallyComplete hφ hpsh hlp,
    hartogsMetric_uniform_pinching hφ hc hC hctl hj hlam⟩

theorem main_of_controlledPotential (h : ControlledPotential) : MainTheorem := by
  obtain ⟨φ,C,hφ,hctl,hj,hn⟩ := h
  have hC : (1:ℝ) ≤ C := by
    have hb := hctl 0 (by norm_num) (by norm_num) (LinearIsometryEquiv.refl ℂ Base)
      (EuclideanSpace.single 0 1)
    have hv : ‖(EuclideanSpace.single 0 (1:ℂ) : Base)‖ = 1 := by simp
    rw [hv] at hb
    simpa using hb.1.trans hb.2
  obtain ⟨lam0,hlam0,hm⟩ := metric_transfer 1 C (by norm_num) hC
  obtain ⟨hcon,hkah,hcomplete,A,B,hpinch⟩ := hm φ hφ hctl hj lam0 le_rfl
  obtain ⟨hopen,hne,_,hno,hb⟩ := hartogs_obstruction φ hφ hn
  exact ⟨hartogs φ,hartogsMetric φ lam0,A,B,hopen,hne,hcon,hkah,hcomplete,hpinch,hno,hb⟩

end PinchedHartogs

end

end OAI
