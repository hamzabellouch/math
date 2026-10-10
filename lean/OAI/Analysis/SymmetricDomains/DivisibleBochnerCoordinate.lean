import Mathlib
import OAI.Analysis.SymmetricDomains.IsotropyRepresentationUnitsCompact

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
namespace Release061

section
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem compact_holomorphic_average_derivative {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] {n m : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (F : K → Affine n → Affine m)
    (ha : ∀ a, AnalyticOnNhd ℂ (F a) U)
    (hc : ∀ x ∈ U, Continuous (fun a => F a x))
    (hdc : ∀ x ∈ U, Continuous (fun a => fderiv ℂ (F a) x))
    {M : ℝ} (hM : ∀ a, ∀ x ∈ U, ‖F a x‖ ≤ M)
    {p : Affine n} (hp : p ∈ U) :
    HasFDerivAt (fun x => ∫ a, F a x ∂μ) (∫ a, fderiv ℂ (F a) p ∂μ) p := by
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  have hsub : ∀ x ∈ ball p (R/2), ball x (R/2) ⊆ U := by
    intro x hx y hy
    apply hball
    rw [mem_ball] at *
    exact (dist_triangle y x p).trans_lt (by linarith)
  have hbound : ∀ a, ∀ x ∈ ball p (R/2), ‖fderiv ℂ (F a) x‖ ≤ (2*M)/(R/2) := by
    intro a x hx
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((ha a).differentiableOn.mono (hsub x hx)) _ (by linarith)
    intro y hy
    rw [mem_closedBall,dist_eq_norm]
    have hxU := hsub x hx (mem_ball_self (by linarith))
    exact (norm_sub_le _ _).trans (by linarith [hM a y (hsub x hx hy),hM a x hxU])
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => (2*M)/(R/2))
    (ball_mem_nhds p (by linarith : 0<R/2))
  · filter_upwards [hU.mem_nhds hp] with x hx
    exact (hc x hx).aestronglyMeasurable
  · apply (hc p hp).integrable_of_hasCompactSupport
    exact (isClosed_tsupport _).isCompact
  · exact (hdc p hp).aestronglyMeasurable
  · exact ae_of_all μ hbound
  · exact integrable_const _
  · exact ae_of_all μ (fun a x hx => (ha a _ (hsub x hx (mem_ball_self (by linarith)))).differentiableAt.hasFDerivAt)

theorem compact_holomorphic_average_analytic {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] {n m : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (F : K → Affine n → Affine m)
    (ha : ∀ a, AnalyticOnNhd ℂ (F a) U)
    (hc : ∀ x ∈ U, Continuous (fun a => F a x))
    (hdc : ∀ x ∈ U, Continuous (fun a => fderiv ℂ (F a) x))
    {M : ℝ} (hM : ∀ a, ∀ x ∈ U, ‖F a x‖ ≤ M) :
    AnalyticOnNhd ℂ (fun x => ∫ a, F a x ∂μ) U := by
  apply analyticOnNhd_of_differentiableOn_affine hU
  intro p hp
  exact (compact_holomorphic_average_derivative μ hU F ha hc hdc hM hp).differentiableAt.differentiableWithinAt

end

open Set Filter Topology Metric MeasureTheory
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) (p : U)

def bochnerIntegrand (a : isotropySubgroup p) (x : Affine n) : Affine n :=
  (((isotropyRepresentationUnits hU p a)⁻¹ : (Affine n →L[ℂ] Affine n)ˣ) :
    Affine n →L[ℂ] Affine n) (a.val.ambientAut x-p.val)

variable [LocallyCompactSpace U]

theorem bochnerIntegrand_continuous {x : Affine n} (hx : x ∈ U) :
    Continuous (fun a => bochnerIntegrand hU p a x) := by
  have hA : Continuous (fun a : isotropySubgroup p =>
      ((isotropyRepresentationUnits hU p a)⁻¹).val) :=
    Units.continuous_val.comp (isotropyRepresentationUnits_continuous hU p).inv
  apply hA.clm_apply
  change Continuous (fun a : isotropySubgroup p => a.val.ambientAut x-p.val)
  have h : Continuous (fun a : isotropySubgroup p => (a.val.toHomeomorph ⟨x,hx⟩).val) :=
    continuous_subtype_val.comp ((continuous_evaluation (⟨x,hx⟩ : U)).comp continuous_subtype_val)
  have h' : Continuous (fun a : isotropySubgroup p => a.val.ambientAut x) := by
    simpa only [← ambientAut_apply] using h
  exact h'.sub continuous_const

omit [LocallyCompactSpace U] in
theorem bochnerIntegrand_hasFDerivAt (a : isotropySubgroup p) {x : Affine n} (hx : x ∈ U) :
    HasFDerivAt (bochnerIntegrand hU p a)
      ((((isotropyRepresentationUnits hU p a)⁻¹).val).comp
        (a.val.derivativeAt ⟨x,hx⟩)) x := by
  exact ContinuousLinearMap.hasFDerivAt _ |>.comp x
    ((a.val.ambientAut_analytic hU x hx).differentiableAt.hasFDerivAt.sub_const p.val)

omit [LocallyCompactSpace U] in
theorem bochnerIntegrand_analytic (a : isotropySubgroup p) :
    AnalyticOnNhd ℂ (bochnerIntegrand hU p a) U := by
  apply analyticOnNhd_of_differentiableOn_affine hU
  intro x hx
  exact (bochnerIntegrand_hasFDerivAt hU p a hx).differentiableAt.differentiableWithinAt

theorem bochnerIntegrand_derivative_continuous {x : Affine n} (hx : x ∈ U) :
    Continuous (fun a => fderiv ℂ (bochnerIntegrand hU p a) x) := by
  have hA : Continuous (fun a : isotropySubgroup p =>
      ((isotropyRepresentationUnits hU p a)⁻¹).val) :=
    Units.continuous_val.comp (isotropyRepresentationUnits_continuous hU p).inv
  have he : (fun a => fderiv ℂ (bochnerIntegrand hU p a) x) =
      (fun a : isotropySubgroup p =>
        ((isotropyRepresentationUnits hU p a)⁻¹).val.comp
          (a.val.derivativeAt ⟨x,hx⟩)) := funext (fun a => (bochnerIntegrand_hasFDerivAt hU p a hx).fderiv)
  rw [he]
  exact hA.clm_comp ((derivativeAt_continuous hU ⟨x,hx⟩).comp continuous_subtype_val)

theorem bochnerIntegrand_uniform_bound [CompactSpace (isotropySubgroup p)]
    (hb : Bornology.IsBounded U) :
    ∃ M : ℝ, ∀ a : isotropySubgroup p, ∀ x ∈ U, ‖bochnerIntegrand hU p a x‖ ≤ M := by
  have hA : Continuous (fun a : isotropySubgroup p =>
      ((isotropyRepresentationUnits hU p a)⁻¹).val) :=
    Units.continuous_val.comp (isotropyRepresentationUnits_continuous hU p).inv
  obtain ⟨C,hC,hCb⟩ := (isCompact_range hA).isBounded.exists_pos_norm_le
  obtain ⟨M,hM,hMb⟩ := hb.exists_pos_norm_le
  refine ⟨C*(M+‖p.val‖),?_⟩
  intro a x hx
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  have hb' : ‖a.val.ambientAut x-p.val‖ ≤ M+‖p.val‖ := by
    apply (norm_sub_le _ _).trans
    gcongr
    simpa only [ambientAut_apply a.val ⟨x,hx⟩] using hMb _ (a.val.toHomeomorph ⟨x,hx⟩).property
  exact mul_le_mul (hCb _ ⟨a,rfl⟩) hb' (norm_nonneg _) hC.le

variable [CompactSpace (isotropySubgroup p)]
variable [MeasurableSpace (isotropySubgroup p)] [BorelSpace (isotropySubgroup p)]

def bochnerMap (μ : Measure (isotropySubgroup p)) (x : Affine n) : Affine n :=
  ∫ a, bochnerIntegrand hU p a x ∂μ

theorem bochnerMap_analytic (hb : Bornology.IsBounded U)
    (μ : Measure (isotropySubgroup p)) [IsFiniteMeasure μ] :
    AnalyticOnNhd ℂ (bochnerMap hU p μ) U := by
  obtain ⟨M,hM⟩ := bochnerIntegrand_uniform_bound hU p hb
  exact compact_holomorphic_average_analytic μ hU (bochnerIntegrand hU p)
    (bochnerIntegrand_analytic hU p) (fun _ hx => bochnerIntegrand_continuous hU p hx)
    (fun _ hx => bochnerIntegrand_derivative_continuous hU p hx) hM

omit [LocallyCompactSpace U] [CompactSpace (isotropySubgroup p)] [BorelSpace (isotropySubgroup p)] in
@[simp] theorem bochnerMap_center (μ : Measure (isotropySubgroup p)) :
    bochnerMap hU p μ p.val=0 := by
  unfold bochnerMap
  have he : ∀ a : isotropySubgroup p, bochnerIntegrand hU p a p.val=0 := by
    intro a
    have ha : a.val.toHomeomorph p=p := a.property
    simp only [bochnerIntegrand,ambientAut_apply,ha,sub_self,map_zero]
  simp only [he,integral_zero]

omit [LocallyCompactSpace U] [CompactSpace (isotropySubgroup p)]
  [MeasurableSpace (isotropySubgroup p)] [BorelSpace (isotropySubgroup p)] in
theorem bochnerIntegrand_center_fderiv (a : isotropySubgroup p) :
    fderiv ℂ (bochnerIntegrand hU p a) p.val=1 := by
  rw [(bochnerIntegrand_hasFDerivAt hU p a p.property).fderiv]
  change ((isotropyRepresentationUnits hU p a)⁻¹).val *
    (isotropyRepresentationUnits hU p a : Affine n →L[ℂ] Affine n) = 1
  exact Units.inv_mul _

theorem bochnerMap_center_derivative (hb : Bornology.IsBounded U)
    (μ : Measure (isotropySubgroup p)) [IsProbabilityMeasure μ] :
    HasStrictFDerivAt (bochnerMap hU p μ) (1 : Affine n →L[ℂ] Affine n) p.val := by
  obtain ⟨M,hM⟩ := bochnerIntegrand_uniform_bound hU p hb
  have hd := compact_holomorphic_average_derivative μ hU (bochnerIntegrand hU p)
    (bochnerIntegrand_analytic hU p) (fun _ hx => bochnerIntegrand_continuous hU p hx)
    (fun _ hx => bochnerIntegrand_derivative_continuous hU p hx) hM p.property
  have he : fderiv ℂ (bochnerMap hU p μ) p.val=1 := by
    unfold bochnerMap
    rw [hd.fderiv]
    simp only [bochnerIntegrand_center_fderiv,integral_const,probReal_univ,one_smul]
  exact he ▸ (bochnerMap_analytic hU p hb μ _ p.property).hasStrictFDerivAt

omit [LocallyCompactSpace U] [CompactSpace (isotropySubgroup p)]
  [MeasurableSpace (isotropySubgroup p)] [BorelSpace (isotropySubgroup p)] in
theorem bochnerIntegrand_mul (a b : isotropySubgroup p) (x : U) :
    bochnerIntegrand hU p a (b.val.toHomeomorph x).val =
      b.val.derivativeAt p (bochnerIntegrand hU p (a*b) x.val) := by
  let ρ := isotropyRepresentationUnits hU p
  have hL : (ρ b : Affine n →L[ℂ] Affine n) *
      ((ρ (a*b))⁻¹).val =
      ((ρ a)⁻¹).val := by
    rw [map_mul,mul_inv_rev,Units.val_mul,← mul_assoc,Units.mul_inv,one_mul]
  have hp : (a*b).val.toHomeomorph x = a.val.toHomeomorph (b.val.toHomeomorph x) := rfl
  dsimp only [bochnerIntegrand]
  rw [ambientAut_apply a.val (b.val.toHomeomorph x),ambientAut_apply (a*b).val x,hp]
  exact (congrArg (fun L : Affine n →L[ℂ] Affine n =>
    L ((a.val.toHomeomorph (b.val.toHomeomorph x)).val-p.val)) hL).symm

theorem bochnerMap_equivariant (μ : Measure (isotropySubgroup p))
    [IsFiniteMeasure μ] [μ.IsMulRightInvariant] (b : isotropySubgroup p) (x : U) :
    bochnerMap hU p μ (b.val.toHomeomorph x).val =
      b.val.derivativeAt p (bochnerMap hU p μ x.val) := by
  unfold bochnerMap
  simp_rw [bochnerIntegrand_mul hU p]
  rw [ContinuousLinearMap.integral_comp_comm]
  · rw [integral_mul_right_eq_self (μ := μ) (fun a => bochnerIntegrand hU p a x.val) b]
  · apply ((bochnerIntegrand_continuous hU p x.property).comp (continuous_mul_const b)).integrable_of_hasCompactSupport
    exact (isClosed_tsupport _).isCompact

omit [MeasurableSpace (isotropySubgroup p)] [BorelSpace (isotropySubgroup p)] in

theorem exists_bochner_coordinate (hU : IsOpen U) (hb : Bornology.IsBounded U) :
    ∃ (f : Affine n → Affine n) (W : Set (Affine n)),
      IsOpen W ∧ p.val ∈ W ∧ W ⊆ U ∧ AnalyticOnNhd ℂ f U ∧ f p.val=0 ∧
      HasStrictFDerivAt f (1 : Affine n →L[ℂ] Affine n) p.val ∧
      Set.InjOn f W ∧
      (∀ a : isotropySubgroup p, ∀ x : U,
        f (a.val.toHomeomorph x).val = a.val.derivativeAt p (f x.val)) := by
  let : MeasurableSpace (isotropySubgroup p) := borel (isotropySubgroup p)
  let : BorelSpace (isotropySubgroup p) := ⟨rfl⟩
  let K : TopologicalSpace.PositiveCompacts (isotropySubgroup p) :=
    ⟨⟨univ,isCompact_univ⟩,by simp⟩
  let μ := (Measure.haarMeasure K).inv
  have hm : μ univ=1 := by
    rw [Measure.inv_apply]
    simpa only [Set.inv_univ] using (show (Measure.haarMeasure K) univ=1 from Measure.haarMeasure_self)
  let : IsProbabilityMeasure μ := ⟨hm⟩
  let f := bochnerMap hU p μ
  have hf : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℂ (Affine n)) : Affine n →L[ℂ] Affine n) p.val :=
    bochnerMap_center_derivative hU p hb μ
  let e := hf.toOpenPartialHomeomorph f
  refine ⟨f,e.source ∩ U,e.open_source.inter hU,
    ⟨hf.mem_toOpenPartialHomeomorph_source,p.property⟩,inter_subset_right,
    bochnerMap_analytic hU p hb μ,bochnerMap_center hU p μ,hf,?_,?_⟩
  · exact e.injOn.mono inter_subset_left
  · exact bochnerMap_equivariant hU p μ

omit [CompactSpace (isotropySubgroup p)] [MeasurableSpace (isotropySubgroup p)]
  [BorelSpace (isotropySubgroup p)] in

theorem divisible_bochner_coordinate (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (f : Affine n → Affine n) (W : Set (Affine n)),
      IsOpen W ∧ p.val ∈ W ∧ W ⊆ U ∧ AnalyticOnNhd ℂ f U ∧ f p.val=0 ∧
      HasStrictFDerivAt f (1 : Affine n →L[ℂ] Affine n) p.val ∧
      Set.InjOn f W ∧
      (∀ a : isotropySubgroup p, ∀ x : U,
        f (a.val.toHomeomorph x).val = a.val.derivativeAt p (f x.val)) := by
  let : CompactSpace (isotropySubgroup p) :=
    (isotropyRepresentationUnits_compact_embedding hU hc hb Γ hhol p).1
  exact exists_bochner_coordinate p hU hb

end Biholomorph
end Release061

end

end OAI
