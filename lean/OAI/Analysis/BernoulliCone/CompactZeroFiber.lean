import OAI.Analysis.BernoulliCone.PositiveTrace

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Foliation
variable {E : Type uE} [TopologicalSpace E]
/-- Compact zero-fiber control. No convergence of the selected root is needed. -/
lemma eventually_near_zero_fiber {K:Set E} (hK:IsCompact K) {f g:E→ℝ} {C:ℝ}
    (hf:∀x∈K,ContinuousAt f x) (hg:∀x∈K,ContinuousAt g x)
    (hzero:∀x∈K,f x=0 → g x<C) :
    ∀ᶠ t:ℝ in 𝓝 0,∀x∈K,f x=t → g x<C := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  by_cases hz:f x=0
  · have hh:∀ᶠ p:ℝ×E in 𝓝 (0,x),g p.2<C:=
      ((hg x hx).comp continuous_snd.continuousAt).eventually (gt_mem_nhds (hzero x hx hz))
    exact hh.mono fun p hp _=>hp
  · have hn:f x-(0:ℝ)≠0:=by simpa using hz
    have hh:∀ᶠ p:ℝ×E in 𝓝 (0,x),f p.2-p.1≠0:=
      (((hf x hx).comp continuous_snd.continuousAt).sub continuous_fst.continuousAt).eventually_ne hn
    exact hh.mono fun p hp he=>False.elim (hp (sub_eq_zero.mpr he))
end Bernoulli.Foliation

end
end

end OAI
