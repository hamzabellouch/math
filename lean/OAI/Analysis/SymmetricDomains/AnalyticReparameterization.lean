import Mathlib
import OAI.Analysis.SymmetricDomains.HorizontalGraphComplexification

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
namespace Release061.Flatten
open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def shearEquiv (b : E) : (E × ℝ) ≃L[ℝ] (E × ℝ) := by
  let X := ContinuousLinearMap.fst ℝ E ℝ
  let u := ContinuousLinearMap.snd ℝ E ℝ
  exact ContinuousLinearEquiv.equivOfInverse
    ((X + u.smulRight b).prod u) ((X - u.smulRight b).prod u)
    (by intro q; ext <;> simp [X,u]) (by intro q; ext <;> simp [X,u])

lemma shearEquiv_apply (b : E) (q : E × ℝ) : shearEquiv b q = (q.1+q.2•b,q.2) := rfl

theorem analytic_reparameterization [CompleteSpace E] {f : E × ℝ → E}
    (hf : AnalyticAt ℝ f 0) (hzero : ∀ᶠ x in 𝓝 (0 : E), f (x,0) = x) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) (E × ℝ),
      (∀ q, e q = (f q,q.2)) ∧ (0 : E × ℝ) ∈ e.source ∧ e 0 = 0 ∧
      AnalyticAt ℝ e.symm 0 ∧
      (∀ᶠ q in 𝓝 (0 : E × ℝ), (e.symm q).2 = q.2) ∧
      (∀ᶠ x in 𝓝 (0 : E), e.symm (x,0) = (x,0)) := by
  let L := fderiv ℝ f 0
  have hd : HasFDerivAt f L 0 := hf.differentiableAt.hasFDerivAt
  have hinl : L ∘L (ContinuousLinearMap.inl ℝ E ℝ) = ContinuousLinearMap.id ℝ E := by
    have h := hd.comp (0 : E) (ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt
    have h' : HasFDerivAt (fun x : E => x) (L ∘L ContinuousLinearMap.inl ℝ E ℝ) 0 :=
      h.congr_of_eventuallyEq (hzero.mono fun x hx => hx.symm)
    exact h'.unique (hasFDerivAt_id 0)
  have hL (x : E) (u : ℝ) : L (x,u) = x+u•L (0,1) := by
    have he : (x,u) = (x,0)+u•(0,(1:ℝ)) := by simp
    rw [he,map_add,map_smul]
    have h := congrArg (fun A : E →L[ℝ] E => A x) hinl
    change L (x,0) = x at h
    rw [h]
  let H : E × ℝ → E × ℝ := fun q => (f q,q.2)
  have hH : AnalyticAt ℝ H 0 := hf.prod ((ContinuousLinearMap.snd ℝ E ℝ).analyticAt 0)
  have hHd : HasFDerivAt H (shearEquiv (L (0,1))).toContinuousLinearMap 0 := by
    have he : L.prod (ContinuousLinearMap.snd ℝ E ℝ) = (shearEquiv (L (0,1))).toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro q
      exact Prod.ext (hL q.1 q.2) rfl
    rw [← he]
    exact hd.prodMk hasFDerivAt_snd
  have hH0 : H 0 = 0 := by
    have h := hzero.self_of_nhds
    change f (0,0) = 0 at h
    exact Prod.ext h rfl
  obtain ⟨e,he,hem,hia⟩ := real_analytic_local_inverse hH (shearEquiv (L (0,1))) hHd
  have he0 : e 0 = 0 := by rw [he,hH0]
  refine ⟨e,(fun q => congrFun he q),hem,he0,by simpa only [hH0] using hia,?_,?_⟩
  · have htar : (0 : E × ℝ) ∈ e.target := he0 ▸ e.map_source hem
    filter_upwards [e.open_target.mem_nhds htar] with q hq
    have h := congrArg Prod.snd (e.right_inv hq)
    simpa only [he,H] using h
  · have ht : Tendsto (fun x : E => (x,(0:ℝ))) (𝓝 0) (𝓝 (0 : E × ℝ)) := by
      change Tendsto _ (𝓝 0) (𝓝 (0,(0:ℝ)))
      exact (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [hzero,ht (e.open_source.mem_nhds hem)] with x hx hxsrc
    have h : e (x,0) = (x,0) := by rw [he]; exact Prod.ext hx rfl
    calc
      e.symm (x,0) = e.symm (e (x,0)) := congrArg e.symm h.symm
      _ = (x,0) := e.left_inv hxsrc

end Release061.Flatten

end

end OAI
