import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_of_uniform_jets (u : ℕ → E → F) (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (G : (m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F))
    (hG : ∀ m, TendstoUniformly (fun j => iteratedFDeriv ℝ m (u j)) (G m) atTop) :
    ∃ f : E → F, ContDiff ℝ ∞ f ∧
      ∀ m, iteratedFDeriv ℝ m f = G m := by
  let f : E → F := fun x => (G 0 x).curry0
  let p : E → FormalMultilinearSeries ℝ E F := fun x m => G m x
  have hp : HasFTaylorSeriesUpTo ∞ f p := by
    refine ⟨fun _ => rfl, ?_, fun m _ => (G m).continuous⟩
    intro m hm x
    have ht : TendstoUniformly
      (fun j y => (iteratedFDeriv ℝ (m+1) (u j) y).curryLeft)
      (fun y => (G (m+1) y).curryLeft) atTop := by
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E) F).isometry.uniformContinuous
        |>.comp_tendstoUniformly (hG (m+1))
    exact hasFDerivAt_of_tendstoUniformly ht
      (fun j y => (hu j).ftaylorSeries.fderiv m hm y)
      (fun y => (hG m).tendsto_at y) x
  refine ⟨f,hp.contDiff,fun m => ?_⟩
  funext x
  exact (hp.eq_iteratedFDeriv (m:=m) (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) x).symm


end

open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
open Set Filter Function Metric TopologicalSpace
open scoped Topology ContDiff Distributions BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Compacts E)

def compactSmoothJetMap : 𝓓_{K}(E,F) →L[ℝ] ((m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F)) :=
  ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤)

theorem compactSmoothJetMap_isClosed : IsClosed (range (compactSmoothJetMap (F:=F) K)) := by
  let : ∀ m : ℕ, FirstCountableTopology (E →ᵇ (E [×m]→L[ℝ] F)) := fun _ => inferInstance
  let : FirstCountableTopology ((m : ℕ) → E →ᵇ (E [×m]→L[ℝ] F)) := inferInstance
  apply IsSeqClosed.isClosed
  intro v G hv hlim
  choose u hu using hv
  have hG : ∀ m, TendstoUniformly (fun j => iteratedFDeriv ℝ m (u j)) (G m) atTop := by
    intro m
    have ht := (continuous_apply m).tendsto G |>.comp hlim
    have htu : Tendsto (fun j => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ m (u j))
        atTop (𝓝 (G m)) := by
      convert ht using 1
      funext j
      exact congrArg (fun w => w m) (hu j)
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htu
  obtain ⟨f,hf,hfj⟩ := smooth_of_uniform_jets (fun j => u j) (fun j => (u j).contDiff) G hG
  have hzero : EqOn f 0 Kᶜ := by
    intro x hx
    have hconst : ∀ j, iteratedFDeriv ℝ 0 (u j) x = 0 := by
      intro j
      ext z
      simp only [iteratedFDeriv_zero_apply]
      exact (u j).zero_on_compl hx
    have hGX : G 0 x = 0 := tendsto_nhds_unique ((hG 0).tendsto_at x)
      (by simpa only [hconst] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E [×0]→L[ℝ] F)) atTop (𝓝 0)))
    have hh := congrArg (fun h : E → E [×0]→L[ℝ] F => h x) (hfj 0)
    rw [hGX] at hh
    have he := congrArg (fun p : E [×0]→L[ℝ] F => p (fun _ => 0)) hh
    simpa using he
  refine ⟨⟨f,hf,hzero⟩,?_⟩
  funext m
  apply BoundedContinuousFunction.ext
  intro x
  rw [compactSmoothJetMap, ContinuousLinearMap.pi_apply,
    ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact congrArg (fun h : E → E [×m]→L[ℝ] F => h x) (hfj m)

variable [CompleteSpace F]

theorem compactSmooth_complete : CompleteSpace 𝓓_{K}(E,F) := by
  apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (𝕜:=ℝ)
    (n:=⊤) (K:=K)).isUniformInducing.completeSpace
  exact (compactSmoothJetMap_isClosed (F:=F) K).isComplete



end YauCounterexamples
end

end OAI
