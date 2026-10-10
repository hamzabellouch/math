import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions
import OAI.Analysis.BiholderTransport.Coordinates.LogActionMixed
import OAI.Analysis.BiholderTransport.Calculus.SliceDerivatives

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma normalCost_log_contDiffAt {x : M} {e : F → TangentSpace 𝓘(ℝ,Model n) x}
    {b : F} (he : ContDiffAt ℝ ∞ e b) (hp : e b∈injectivityDomain x) :
    ContDiffAt ℝ ∞ (fun q : F×TangentSpace 𝓘(ℝ,Model n) x => normalCost x (e q.1) q.2) (b,0) := by
  have H := logJoinAction_contDiffAt hp (contDiffAt_const (c := (0:ℝ)))
    (contDiffAt_id (𝕜 := ℝ)) rfl (a := 1)
  have HH := H.comp (b,0) ((he.comp (b,0) contDiffAt_fst).prodMk contDiffAt_snd)
  simpa only [logJoinAction,zero_add,one_mul,Function.comp_def,id_eq] using HH

lemma normalCost_log_mixed {x : M} {e : F → TangentSpace 𝓘(ℝ,Model n) x}
    {b : F} (he : ContDiffAt ℝ ∞ e b) (hp : e b∈injectivityDomain x)
    (d : F) (k : TangentSpace 𝓘(ℝ,Model n) x) :
    fderiv ℝ (fderiv ℝ (fun q : F×TangentSpace 𝓘(ℝ,Model n) x =>
      normalCost x (e q.1) q.2)) (b,0) (d,0) (0,k) = -inner ℝ (fderiv ℝ e b d) k := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let B := logJoinAction x (1:ℝ) (fun _:V => (0:ℝ)) (id:V→V)
  have hB : ContDiffAt ℝ ∞ B (e b,0) :=
    logJoinAction_contDiffAt hp contDiffAt_const contDiffAt_id rfl
  have heq : (fun q : F×V => normalCost x (e q.1) q.2)=(fun q => B (e q.1,q.2)) := by
    ext q; simp only [B,logJoinAction,zero_add,one_mul,id_eq]
  rw [heq,second_fderiv_map_fst
    (hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (he.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  have H := logJoinAction_mixed hp (contDiffAt_const (c := (0:ℝ)))
    (contDiffAt_id (𝕜 := ℝ)) rfl (a := 1) (fderiv ℝ e b d) k
  simpa only [B,fderiv_id,ContinuousLinearMap.id_apply,neg_one_mul] using H

lemma normal_log_derivatives_adjoint {x y : M}
    {e : TangentSpace 𝓘(ℝ,Model n) y → TangentSpace 𝓘(ℝ,Model n) x}
    {f : TangentSpace 𝓘(ℝ,Model n) x → TangentSpace 𝓘(ℝ,Model n) y}
    (he : ContDiffAt ℝ ∞ e 0) (hf : ContDiffAt ℝ ∞ f 0)
    (hep : e 0∈injectivityDomain x) (hfq : f 0∈injectivityDomain y)
    (hei : ∀ᶠ v in 𝓝 0, riemannianExp x (e v)=riemannianExp y v)
    (hfi : ∀ᶠ u in 𝓝 0, riemannianExp y (f u)=riemannianExp x u)
    (d : TangentSpace 𝓘(ℝ,Model n) y) (k : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (fderiv ℝ e 0 d) k=inner ℝ d (fderiv ℝ f 0 k) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let W := TangentSpace 𝓘(ℝ,Model n) y
  let A : W×V → ℝ := fun q => normalCost x (e q.1) q.2
  let B : V×W → ℝ := fun q => normalCost y (f q.1) q.2
  have hA := normalCost_log_contDiffAt he hep
  have hB := normalCost_log_contDiffAt hf hfq
  have hA2 := hA.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB2 := hB.of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have heq : A =ᶠ[𝓝 (0,0)] (fun q => B q.swap) := by
    filter_upwards [continuousAt_fst.eventually hei,continuousAt_snd.eventually hfi] with q hqe hqf
    change cost (riemannianExp x q.2) (riemannianExp x (e q.1))=
      cost (riemannianExp y q.1) (riemannianExp y (f q.2))
    rw [hqe,hqf]
    exact cost_symm _ _
  let S := (ContinuousLinearEquiv.prodComm ℝ W V).toContinuousLinearMap
  have HS := second_fderiv_comp_affine (f := B) S 0 (0:W×V)
    (by simpa [S,B,Prod.swap] using hB2) (d,0) (0,k)
  have H : fderiv ℝ (fderiv ℝ A) (0,0) (d,0) (0,k)=
      fderiv ℝ (fderiv ℝ B) (0,0) (0,d) (k,0) := by
    rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    simp only [S,zero_add,map_zero,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.prodComm_apply,Prod.swap_prod_mk,zero_add] at HS
    simpa only [Prod.zero_eq_mk] using HS
  have Hsym := (hB2.isSymmSndFDerivAt (by norm_num)).eq (0,d) (k,0)
  rw [Hsym] at H
  change fderiv ℝ (fderiv ℝ A) (0,0) (d,0) (0,k)=
    fderiv ℝ (fderiv ℝ B) (0,0) (k,0) (0,d) at H
  rw [normalCost_log_mixed he hep,normalCost_log_mixed hf hfq] at H
  exact (neg_injective H).trans (real_inner_comm _ _)

end WeakMTWTransport

end



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_smooth_two_sided_fiber_log {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈injectivityDomain x) :
    ∃ L : M → TangentSpace 𝓘(ℝ,Model n) x,
      ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) ∞ L
        (riemannianExp x p) ∧
      L (riemannianExp x p)=p ∧
      (∀ᶠ y in 𝓝 (riemannianExp x p), riemannianExp x (L y)=y) ∧
      (∀ᶠ v in 𝓝 p, L (riemannianExp x v)=v) := by
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let y := riemannianExp x p
  let d := extChartAt 𝓘(ℝ,Model n) y
  obtain ⟨e,he,hpe,hei⟩ := exists_coordinate_exp_inverse hp
  have hep : e p=d y := by rw [he]
  let L : M → V := fun z => e.symm (d z)
  have hL : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,V) ∞ L y :=
    (show ContDiffAt ℝ ∞ e.symm (d y) from hep ▸ hei).contMDiffAt.comp y
      (show ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ d y from contMDiffAt_extChartAt)
  have hLy : L y=p := by dsimp [L]; rw [←hep,e.left_inv hpe]
  refine ⟨L,hL,hLy,?_,?_⟩
  · have ht : ∀ᶠ z in 𝓝 y, d z∈e.target :=
      (continuousAt_extChartAt y).eventually (e.open_target.mem_nhds (hep ▸ e.map_source hpe))
    have hcont : ContinuousAt (fun z => riemannianExp x (L z)) y :=
      (continuous_riemannianExp x).continuousAt.comp hL.continuousAt
    have hs : ∀ᶠ z in 𝓝 y, riemannianExp x (L z)∈d.source := by
      have H := hcont.eventually (show d.source∈𝓝 (riemannianExp x (L y)) from by
        rw [hLy]; exact extChartAt_source_mem_nhds y)
      exact H
    filter_upwards [ht,hs,extChartAt_source_mem_nhds (I := 𝓘(ℝ,Model n)) y] with z hzt hzs hsz
    apply d.injOn hzs hsz
    have HR := e.right_inv hzt
    rw [he] at HR
    exact HR
  · filter_upwards [e.open_source.mem_nhds hpe] with v hv
    change e.symm (d (riemannianExp x v))=v
    rw [←show e v=d (riemannianExp x v) from congrFun he v]
    exact e.left_inv hv

end WeakMTWTransport

end

end OAI
