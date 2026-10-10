import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Sequences

namespace OAI

/-! Normalized kernel vectors persist under operator-norm convergence to a compact operator. -/

open Set Filter Topology
namespace DefocusingNLS

theorem compact_kernel_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : ℕ → E →L[ℂ] E) (K₀ : E →L[ℂ] E)
    (hK : Tendsto K atTop (𝓝 K₀)) (hc : IsCompactOperator K₀)
    (v : ℕ → E) (hv : ∀ n, ‖v n‖=1) (he : ∀ n, K n (v n)=v n) :
    ∃ v₀ : E, ‖v₀‖=1 ∧ K₀ v₀=v₀ := by
  have hb (n : ℕ) : v n ∈ Metric.closedBall (0 : E) 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right,hv n] using (le_refl (1 : ℝ))
  have hcomp := hc.isCompact_closure_image_closedBall 1
  obtain ⟨v₀,_,φ,hφ,ht⟩ := hcomp.tendsto_subseq
    (fun n => subset_closure (mem_image_of_mem K₀ (hb n)))
  have hzero : Tendsto (fun n => v n-K₀ (v n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => ‖K n-K₀‖)
    · intro n
      have hn := (K n-K₀).le_opNorm (v n)
      simpa only [FunLike.coe_sub,Pi.sub_apply,he n,hv n,mul_one] using hn
    · have hconst : Tendsto (fun _ : ℕ => K₀) atTop (𝓝 K₀) := tendsto_const_nhds
      simpa only [sub_self,norm_zero] using (hK.sub hconst).norm
  have ht' : Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) := by
    have hs := (hzero.comp hφ.tendsto_atTop).add ht
    simpa only [Function.comp_def,sub_add_cancel,zero_add] using hs
  have hn : ‖v₀‖=1 := by
    apply tendsto_nhds_unique ht'.norm
    simpa only [hv] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hfix : K₀ v₀=v₀ :=
    tendsto_nhds_unique (K₀.continuous.continuousAt.tendsto.comp ht') ht
  exact ⟨v₀,hn,hfix⟩

end DefocusingNLS

end OAI
