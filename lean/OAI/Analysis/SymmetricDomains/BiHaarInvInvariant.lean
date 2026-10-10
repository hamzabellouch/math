import Mathlib
import OAI.Analysis.SymmetricDomains.ProjectedChartLeftDifferential

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph
open Set Filter Topology
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
include hU

theorem projected_chart_left_determinant_continuous
    (p : U) (P : (Affine n × (Affine n →L[ℂ] Affine n)) →L[ℝ] E)
    (e : OpenPartialHomeomorph (Biholomorph U U) E)
    (he : (e : Biholomorph U U → E)=(fun a => P (ambientFirstJet p a)))
    (he1 : 1∈e.source)
    (L : E →L[ℝ] (Affine n × (Affine n →L[ℂ] Affine n)))
    (hL : HasStrictFDerivAt (fun t => ambientFirstJet p (e.symm t)) L (e 1)) :
    Continuous (fun g : Biholomorph U U => (fderiv ℝ (chartLeftMap e g) (e 1)).det) := by
  classical
  have hd : Continuous (fun g : Biholomorph U U => g.derivativeAt p) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    exact (ambientAut_derivative_joint_continuousAt hU (q := (g,p.val)) p.property).comp (x := g)
      (show ContinuousAt (fun a : Biholomorph U U => (a,p.val)) g from
        continuousAt_id.prodMk continuousAt_const)
  have hdd : Continuous (fun g : Biholomorph U U => fderiv ℂ (fderiv ℂ g.ambientAut) p.val) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    exact (ambientAut_second_derivative_joint_continuousAt hU (q := (g,p.val)) p.property).comp (x := g)
      (show ContinuousAt (fun a : Biholomorph U U => (a,p.val)) g from
        continuousAt_id.prodMk continuousAt_const)
  have heval (v : E) : Continuous (fun g : Biholomorph U U =>
      (fderiv ℝ (chartLeftMap e g) (e 1)) v) := by
    simp_rw [projected_chart_left_differential_apply hU p P e he he1 L hL]
    exact P.continuous.comp ((hd.clm_apply continuous_const).prodMk
      ((hdd.clm_apply continuous_const).add (hd.clm_comp continuous_const)))
  let b := Module.finBasis ℝ E
  have hm : Continuous (fun g : Biholomorph U U =>
      LinearMap.toMatrix b b (fderiv ℝ (chartLeftMap e g) (e 1)).toLinearMap) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [LinearMap.toMatrix_apply,ContinuousLinearMap.coe_coe]
    exact (continuous_apply i).comp ((continuous_equivFun_basis b).comp (heval (b j)))
  have hh := hm.matrix_det
  simpa only [LinearMap.det_toMatrix,ContinuousLinearMap.det] using hh
end Release061.Biholomorph

namespace Release061
open TopologicalSpace Set MeasureTheory MeasureTheory.Measure Function
open scoped ENNReal NNReal

theorem biHaar_isInvInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [μ.Regular] :
    μ.IsInvInvariant := by
  constructor
  let c : ℝ≥0∞ := haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have hh : map Inv.inv (map Inv.inv μ) = c ^ 2 • μ := by
    rw [← inv_def μ,hc,Measure.map_smul c continuous_inv.measurable.aemeasurable,
      ← inv_def μ,hc,smul_smul,pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [map_map continuous_inv.measurable continuous_inv.measurable] at hh
    simpa only [inv_involutive,Involutive.comp_self,Measure.map_id] using hh
  have K : PositiveCompacts G := Classical.arbitrary _
  have hh : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have hcp : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 hh
  have hc1 : c=1 := (ENNReal.pow_right_strictMono two_ne_zero).injective hcp
  rw [hc,hc1,one_smul]
end Release061

end

end OAI
