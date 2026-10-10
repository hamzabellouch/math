import Mathlib
import OAI.Analysis.Conductivity.Variational.ContDiffClmDet

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

def inverseChartPiolaOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (y : E) : E →L[ℝ] E :=
  |(fderiv ℝ X.symm (X y)).det|⁻¹ • fderiv ℝ X.symm (X y)

lemma localPiolaFlux_inverse_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E) (F : E → E) {y : E} (hy : y ∈ X.source) :
    localPiolaFlux X.symm F y = inverseChartPiolaOperator X y (F (X y)) := by
  simp only [localPiolaFlux, X.symm_symm, show y ∈ X.symm.target from hy, ite_eq_left,
    inverseChartPiolaOperator, _root_.smul_apply]

lemma inverseChartPiolaOperator_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a : E} (ha : a ∈ X.source) : ContinuousAt (inverseChartPiolaOperator X) a := by
  have hca : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fderiv ℝ X.symm) (X a) :=
    ((hXi _ (X.map_source ha)).contDiffAt
    (X.open_target.mem_nhds (X.map_source ha))).fderiv_right (by simp)
  have hda := ((hX a ha).contDiffAt (X.open_source.mem_nhds ha)).continuousAt
  have hd : ContinuousAt (fun y => fderiv ℝ X.symm (X y)) a := hca.continuousAt.comp hda
  have hdet0 := local_fderiv_det_ne_zero X.symm (hXi.differentiableOn (by simp))
    (hX.differentiableOn (by simp)) (X.map_source ha)
  have hc : ContinuousAt (fun y => (fderiv ℝ X.symm (X y)).det) a :=
    ((contDiff_clm_det (E := E) (↑(⊤ : ℕ∞))).continuous.continuousAt).comp hd
  exact (hc.abs.inv₀ (abs_ne_zero.mpr hdet0)).smul hd

lemma inverseChartPiolaOperator_eq_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : OpenPartialHomeomorph E E)
    (hX : DifferentiableOn ℝ X X.source) (hXi : DifferentiableOn ℝ X.symm X.target)
    {a : E} (ha : a ∈ X.source) (hDa : fderiv ℝ X a = ContinuousLinearMap.id ℝ E) :
    inverseChartPiolaOperator X a = ContinuousLinearMap.id ℝ E := by
  have hdi := local_fderiv_symm_comp X hX hXi ha
  rw [hDa, ContinuousLinearMap.comp_id] at hdi
  simp only [inverseChartPiolaOperator, hdi, ContinuousLinearMap.det,
    ContinuousLinearMap.coe_id, LinearMap.det_id, abs_one, inv_one, one_smul]

theorem inverseChartPiola_freezing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E)
    (hX : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X X.source)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {a : E} (ha : a ∈ X.source) (hDa : fderiv ℝ X a = ContinuousLinearMap.id ℝ E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ X.source ∧
      ∀ (χ h : E → ℝ) (R : E) (y : E), y ∈ V →
        ‖localPiolaFlux X.symm (fun z => (χ (X.symm z) * h z) • R) y -
          (χ y * h (X y)) • R‖ ≤ ε * (|χ y * h (X y)| * ‖R‖) := by
  have heq := inverseChartPiolaOperator_eq_id X (hX.differentiableOn (by simp))
    (hXi.differentiableOn (by simp)) ha hDa
  have hc : ContinuousAt (fun y => inverseChartPiolaOperator X y -
      ContinuousLinearMap.id ℝ E) a :=
    (inverseChartPiolaOperator_continuousAt X hX hXi ha).sub continuousAt_const
  have hevent : ∀ᶠ y in 𝓝 a,
      ‖inverseChartPiolaOperator X y - ContinuousLinearMap.id ℝ E‖ < ε := by
    have ht := hc.norm.eventually (gt_mem_nhds (show
      ‖inverseChartPiolaOperator X a - ContinuousLinearMap.id ℝ E‖ < ε by
      rw [heq, sub_self, norm_zero]; exact hε))
    exact ht
  obtain ⟨V, hVsub, hV, haV⟩ := mem_nhds_iff.mp (hevent.and (X.open_source.mem_nhds ha))
  refine ⟨V, hV, haV, fun y hy => (hVsub hy).2, ?_⟩
  intro χ h R y hy
  rw [localPiolaFlux_inverse_eq X _ (hVsub hy).2, X.left_inv (hVsub hy).2]
  rw [map_smul]
  have hid : (χ y * h (X y)) • (inverseChartPiolaOperator X y R) -
      (χ y * h (X y)) • R =
      (χ y * h (X y)) • ((inverseChartPiolaOperator X y - ContinuousLinearMap.id ℝ E) R) := by
    simp only [_root_.sub_apply, ContinuousLinearMap.id_apply, smul_sub]
  rw [hid, norm_smul, Real.norm_eq_abs]
  calc
    |χ y * h (X y)| * ‖(inverseChartPiolaOperator X y - ContinuousLinearMap.id ℝ E) R‖ ≤
        |χ y * h (X y)| * (ε * ‖R‖) :=
      mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hVsub hy).1.le (norm_nonneg _))) (abs_nonneg _)
    _ = ε * (|χ y * h (X y)| * ‖R‖) := by ring

end ScalarConductivity

end

end OAI
