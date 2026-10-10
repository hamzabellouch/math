import Mathlib
import OAI.Analysis.BiholderTransport.MinimizingVectors
import OAI.Analysis.BiholderTransport.Geodesics.MetricGeodesicLift

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

omit [IsRiemannianManifold 𝓘(ℝ,E) M] in
lemma sprayFlow_pathELength (z : TangentBundle 𝓘(ℝ,E) M) (s t : ℝ) :
    pathELength 𝓘(ℝ,E) (fun u => (sprayFlow u z).1) s t =
      ENNReal.ofReal ((t-s)*‖z.2‖) := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ = ∫⁻ _ in Icc s t, ENNReal.ofReal ‖z.2‖ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u _
      have H := congrArg (fun v : TangentSpace 𝓘(ℝ,E) (sprayFlow u z).1 => ENNReal.ofReal ‖v‖)
        (spray_velocity_eq_mfderiv ((sprayFlow_curve z).isMIntegralCurveAt u))
      have H' := H.trans (congrArg ENNReal.ofReal (sprayFlow_speed u z))
      convert! H' using 1
      exact (ofReal_norm _).symm
    _ = _ := by
      rw [setLIntegral_const,Real.volume_Icc,ENNReal.ofReal_mul' (norm_nonneg _),mul_comm]

lemma dist_sprayFlow_le (z : TangentBundle 𝓘(ℝ,E) M) (s t : ℝ) :
    dist (sprayFlow s z).1 (sprayFlow t z).1 ≤ |s-t| * ‖z.2‖ := by
  have hsm : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun u => (sprayFlow u z).1) :=
    (Bundle.contMDiff_proj (fun x : M => TangentSpace 𝓘(ℝ,E) x)).comp
      (contMDiff_sprayFlow.comp (contMDiff_id.prodMk contMDiff_const))
  have H : ∀ s t : ℝ, s ≤ t → dist (sprayFlow s z).1 (sprayFlow t z).1 ≤ (t-s)*‖z.2‖ := by
    intro s t hst
    have he := riemannianEDist_le_pathELength (I := 𝓘(ℝ,E))
      (hsm.of_le (by simp)).contMDiffOn rfl rfl hst
    rw [←IsRiemannianManifold.out,sprayFlow_pathELength,edist_dist] at he
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sub_nonneg.mpr hst) (norm_nonneg _))).mp he
  rcases le_total s t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    simpa only [neg_sub] using H s t hst
  · rw [dist_comm,abs_of_nonneg (sub_nonneg.mpr hts)]
    exact H t s hts

end

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma continuous_riemannianExp (x : M) : Continuous (riemannianExp (n := n) x) :=
  contMDiff_riemannianExp.continuous.comp (FiberBundle.continuous_totalSpaceMk _ _ x)

lemma dist_riemannianExp_smul_le (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) (s t : ℝ) :
    dist (riemannianExp x (s • v)) (riemannianExp x (t • v)) ≤ |s - t| * ‖v‖ := by
  simp only [riemannianExp_smul]
  exact dist_sprayFlow_le ⟨x,v⟩ s t

lemma dist_riemannianExp_le (x : M) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    dist x (riemannianExp x v) ≤ ‖v‖ := by
  have H := dist_sprayFlow_le (⟨x,v⟩ : TangentBundle 𝓘(ℝ,Model n) M) 0 1
  simpa only [sprayFlow_zero,riemannianExp_eq_sprayFlow,zero_sub,abs_neg,abs_one,one_mul] using H

lemma minimizingVectors_smul {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • p ∈ minimizingVectors x := by
  change dist x (riemannianExp x (t • p)) = ‖t • p‖
  apply le_antisymm (dist_riemannianExp_le _ _)
  have H := dist_triangle x (riemannianExp x (t • p)) (riemannianExp x p)
  have Hb := dist_riemannianExp_smul_le x p t 1
  rw [one_smul,abs_of_nonpos (sub_nonpos.mpr ht1)] at Hb
  change dist x (riemannianExp x p) = ‖p‖ at hp
  rw [hp] at H
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
  nlinarith

lemma injectivityDomain_subset_minimizingVectors (x : M) :
    injectivityDomain (n := n) x ⊆ minimizingVectors x := by
  rintro p ⟨a,ha,he⟩
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hmin : a • p ∈ minimizingVectors x := by
    change dist x (riemannianExp x (a • p)) = ‖a • p‖
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
  have H := minimizingVectors_smul hmin (inv_nonneg.mpr ha0.le)
    (inv_le_one_of_one_le₀ ha.le)
  simpa only [smul_smul,inv_mul_cancel₀ ha0.ne',one_smul] using H

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma contracted_minimizer_mem_injectivityDomain {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ minimizingVectors x)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : t • p ∈ injectivityDomain x := by
  refine ⟨t⁻¹,(one_lt_inv₀ ht0).mpr ht1,?_⟩
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul]
  rw [hp,norm_smul,Real.norm_eq_abs,abs_of_pos ht0,←mul_assoc,inv_mul_cancel₀ ht0.ne',one_mul]

lemma isClosed_minimizingVectors (x : M) : IsClosed (minimizingVectors (n := n) x) :=
  isClosed_eq (continuous_const.dist (continuous_riemannianExp x)) continuous_norm

lemma isCompact_minimizingVectors (x : M) : IsCompact (minimizingVectors (n := n) x) := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Model n))
  apply (isCompact_closedBall (0 : TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
    (isClosed_minimizingVectors x)
  intro p hp
  rw [Metric.mem_closedBall,dist_zero_right,←hp]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ _)

lemma closure_injectivityDomain (x : M) :
    closure (injectivityDomain (n := n) x) = minimizingVectors x := by
  apply subset_antisymm
  · exact closure_minimal (injectivityDomain_subset_minimizingVectors x) (isClosed_minimizingVectors x)
  · intro p hp
    apply closure_mono (s := openSegment ℝ 0 p) ?_ (segment_subset_closure_openSegment (right_mem_segment ℝ 0 p))
    rintro q ⟨a,b,ha,hb,hab,rfl⟩
    rw [smul_zero,zero_add]
    exact contracted_minimizer_mem_injectivityDomain hp hb (by linarith)

lemma isCompact_total_minimizingVectors :
    IsCompact {z : TangentBundle 𝓘(ℝ,Model n) M | z.2 ∈ minimizingVectors z.1} := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  apply (isCompact_bundle_disk (F := Model n)
    (E := fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (Metric.diam (univ : Set M))).of_isClosed_subset
  · exact isClosed_eq ((FiberBundle.continuous_proj _ _).dist contMDiff_riemannianExp.continuous)
      continuous_bundle_norm
  · intro z hz
    change ‖z.2‖ ≤ _
    rw [←hz]
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)

end WeakMTWTransport

end

end OAI
