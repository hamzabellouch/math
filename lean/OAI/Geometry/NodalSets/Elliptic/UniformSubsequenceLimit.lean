import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

namespace OAI

namespace Yau.Analysis
open Filter Set
open scoped Topology UniformConvergence

theorem uniformOn_of_subsequence_limits {X E : Type*} [UniformSpace E]
    (F : ℕ → X → E) (f : X → E) (Q : Set X)
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      TendstoUniformlyOn (fun j ↦ F (ns (ms j))) f atTop Q) :
    TendstoUniformlyOn F f atTop Q := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
    (show Tendsto (fun j ↦ UniformFun.ofFun (fun x : Q ↦ F j x)) atTop
      (𝓝 (UniformFun.ofFun (fun x : Q ↦ f x))) from ?_)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,hms⟩ := h ns hns
  exact ⟨ms,UniformFun.tendsto_iff_tendstoUniformly.mpr
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hms)⟩

end Yau.Analysis

end OAI
