import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ManifoldLipschitz
import OAI.Analysis.BiholderTransport.Geodesics.MinimizingChartParameters
import OAI.Analysis.BiholderTransport.Regularity.RayAnchor
import OAI.Analysis.BiholderTransport.Regularity.CompactUniformSecondRemainder

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma half_cost_taylor_near_base (a : M) :
    ∃ C>0, ∃ d>0, ∃ K∈𝓝 a, ∀ x∈K, ∀ p v : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖v‖<d →
      |normalCost x ((1/2:ℝ) • p) v-normalCost x ((1/2:ℝ) • p) 0+
        inner ℝ ((1/2:ℝ) • p) v|≤C*‖v‖^2 := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨B,hB,hbound⟩ := eventually_norm_trivializationAt_lt (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) a
  obtain ⟨K,hKn,hKs,hKc⟩ := local_compact_nhds
    (inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) a) hbound)
  let χ := extChartAt 𝓘(ℝ,Model n) a
  let e := trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a
  let P := minimizingChartParameters (n := n) a K
  let F : (Model n×Model n) → Model n → ℝ :=
    fun q z => movingNormalCost a q.1 ((1/2:ℝ) • q.2) z
  have hF : ∀ q∈P, ContDiffAt ℝ ∞ (Function.uncurry F) (q,0) := by
    intro q hq
    have H := mem_minimizingChartParameters (fun x hx => (hKs hx).1) hq
    have hp := contracted_minimizer_mem_injectivityDomain H.2.2
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
    have hp' : e.symmL ℝ (χ.symm q.1) ((1/2:ℝ) • q.2)∈injectivityDomain (χ.symm q.1) :=
      by simpa only [map_smul] using hp
    exact (movingNormalCost_contDiffAt H.1 hp').comp (q,(0 : Model n))
      ((contDiffAt_fst.fst.prodMk ((contDiffAt_const (c := (1/2:ℝ))).smul contDiffAt_fst.snd)).prodMk contDiffAt_snd)
  obtain ⟨L,hL,d,hd,H⟩ := compact_uniform_second_remainder
    (isCompact_minimizingChartParameters hKc (fun x hx => (hKs hx).1)) hF
  refine ⟨L*B^2,by positivity,d/B,by positivity,K,hKn,?_⟩
  intro x hx p v hp hv
  let A := e.continuousLinearMapAt ℝ x
  have hpP : (χ x,A p)∈P :=
    trivialization_mem_minimizingChartParameters (fun x hx => (hKs hx).1) hx hp
  have hAv : ‖A v‖≤B*‖v‖ :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right (hKs hx).2.le (norm_nonneg _))
  have he : normalCost x ((1/2:ℝ) • p) = fun z => F (χ x,A p) (A z) := by
    funext z
    dsimp only [normalCost,F,movingNormalCost]
    rw [←map_smul,movingNormal_trivialization_exp (hKs hx).1,
      movingNormal_trivialization_exp (hKs hx).1]
  have hD : DifferentiableAt ℝ (F (χ x,A p)) 0 :=
    ((hF _ hpP).comp 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hder : fderiv ℝ (F (χ x,A p)) 0 (A v) = -inner ℝ ((1/2:ℝ) • p) v := by
    have hd0 : HasFDerivAt (F (χ x,A p)) (fderiv ℝ (F (χ x,A p)) 0) (A 0) := by
      simpa only [map_zero] using hD.hasFDerivAt
    have HD := hd0.comp 0 A.hasFDerivAt
    dsimp only [Function.comp_def] at HD
    rw [←he] at HD
    have HR := congrArg (fun L : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ => L v) HD.fderiv.symm
    rw [normalCost_fderiv_zero (contracted_minimizer_mem_injectivityDomain hp
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1))] at HR
    exact HR
  have havd : ‖A v‖<d := hAv.trans_lt (by rw [mul_comm B]; exact (lt_div_iff₀ hB).mp hv)
  have HR := H _ hpP (A v) havd
  rw [hder] at HR
  have he0 := congrFun he 0
  have hev := congrFun he v
  simp only [map_zero] at he0
  rw [←he0,←hev,sub_neg_eq_add] at HR
  apply HR.trans
  calc
    L*‖A v‖^2≤L*(B*‖v‖)^2 := by gcongr
    _=(L*B^2)*‖v‖^2 := by ring

lemma exists_uniform_half_cost_taylor [Nonempty M] :
    ∃ C>0, ∃ d>0, ∀ x : M, ∀ p v : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖v‖<d →
      |normalCost x ((1/2:ℝ) • p) v-normalCost x ((1/2:ℝ) • p) 0+
        inner ℝ ((1/2:ℝ) • p) v|≤C*‖v‖^2 := by
  classical
  choose C hC d hd K hKn H using half_cost_taylor_near_base (n := n) (M := M)
  obtain ⟨s,hs⟩ := finite_cover_nhds hKn
  have hsn : s.Nonempty := by
    have hx : Classical.arbitrary M∈ ⋃ a∈s,K a := by rw [hs]; trivial
    obtain ⟨a,ha,_⟩ := mem_iUnion₂.mp hx
    exact ⟨a,ha⟩
  refine ⟨s.sup' hsn C,?_,s.inf' hsn d,?_,?_⟩
  · obtain ⟨a,ha⟩ := hsn
    exact (hC a).trans_le (Finset.le_sup' C ha)
  · exact (Finset.lt_inf'_iff hsn).mpr (fun a _ => hd a)
  · intro x p v hp hv
    have hx : x∈ ⋃ a∈s,K a := by rw [hs]; trivial
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp hx
    exact (H a x hxa p v hp (hv.trans_le (Finset.inf'_le d ha))).trans
      (mul_le_mul_of_nonneg_right (Finset.le_sup' C ha) (sq_nonneg _))

lemma exists_uniform_cost_upper_taylor [Nonempty M] :
    ∃ C>0, ∃ d>0, ∀ x : M, ∀ p v : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ‖v‖<d →
      cost (riemannianExp x v) (riemannianExp x p)≤
        cost x (riemannianExp x p)-inner ℝ p v+C*‖v‖^2 := by
  obtain ⟨C,hC,d,hd,H⟩ := exists_uniform_half_cost_taylor (n := n) (M := M)
  refine ⟨2*C,by positivity,d,hd,?_⟩
  intro x p v hp hv
  have hrem := (abs_le.mp (H x p v hp hv)).2
  have hsplit := divided_cost_triangle (riemannianExp x v)
    (riemannianExp x ((1/2:ℝ) • p)) (riemannianExp x p)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have htail := minimizing_ray_tail_cost (z := ⟨x,p⟩) hp
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
  have hmid : cost x (riemannianExp x ((1/2:ℝ) • p))=‖p‖^2/8 := by
    rw [cost,show dist x (riemannianExp x ((1/2:ℝ) • p))=‖(1/2:ℝ) • p‖ from
      minimizingVectors_smul hp (by norm_num) (by norm_num),norm_smul]
    norm_num; ring
  have hfull : cost x (riemannianExp x p)=‖p‖^2/2 := by
    rw [cost,show dist x (riemannianExp x p)=‖p‖ from hp]
  have hflow : (sprayFlow (1/2) (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)).1=
      riemannianExp x ((1/2:ℝ) • p) := (riemannianExp_smul x p (1/2)).symm
  rw [hflow] at htail
  norm_num at htail hsplit
  dsimp only [normalCost] at hrem
  rw [riemannianExp_zero,hmid,real_inner_smul_left] at hrem
  rw [htail] at hsplit
  rw [hfull]
  nlinarith only [hrem,hsplit]

end WeakMTWTransport

end

end OAI
