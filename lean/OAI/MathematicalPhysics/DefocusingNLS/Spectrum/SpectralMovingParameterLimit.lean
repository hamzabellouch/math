import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialParameterSubsequence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

namespace OAI

/-! Moving-parameter convergence detects the joint spectral-parameter limit. -/

open Filter Topology
namespace DefocusingNLS

theorem spectral_joint_of_moving_parameters {E : Type*} [TopologicalSpace E]
    (F : ℕ → ℂ → E) (z : ℂ) (v : E)
    (h : ∀ lam : ℕ → ℂ, Tendsto lam atTop (𝓝 z) →
      Tendsto (fun n => F n (lam n)) atTop (𝓝 v)) :
    Tendsto (fun p : ℕ × ℂ => F p.1 p.2) (atTop ×ˢ 𝓝 z) (𝓝 v) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hN : Tendsto (fun n => (ns n).1) atTop atTop := tendsto_fst.comp hns
  have hz : Tendsto (fun n => (ns n).2) atTop (𝓝 z) := tendsto_snd.comp hns
  obtain ⟨φ,hφ,hNφ⟩ := strictMono_subseq_of_tendsto_atTop hN
  let N := fun n => (ns (φ n)).1
  let lam := fun n => (ns (φ n)).2
  let le := radialParameterExtension N lam z
  have hle : Tendsto le atTop (𝓝 z) :=
    radialParameterExtension_tendsto N hNφ lam z (hz.comp hφ.tendsto_atTop)
  refine ⟨φ,?_⟩
  have hh := (h le hle).comp hNφ.tendsto_atTop
  simpa only [Function.comp_def,le,radialParameterExtension_apply N hNφ,lam,N] using hh

end DefocusingNLS

end OAI
