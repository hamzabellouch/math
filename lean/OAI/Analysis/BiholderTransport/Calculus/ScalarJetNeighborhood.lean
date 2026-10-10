import Mathlib

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma scalar_jet_neighborhood {E:Type*} [TopologicalSpace E]
    {f:E → ℝ} {x:E} (hf:ContinuousAt f x)
    {A B:ℝ×ℝ → ℝ} (hA:Continuous A) (hB:Continuous B) {β:ℝ}
    {U:Set (E×ℝ)} (hU:U∈𝓝 (x,A (β,f x)))
    (hcurve:B (β,f x) < 0) :
    ∃V:Set (E×ℝ),V∈𝓝 (x,β) ∧ ∀q∈V,
      (q.1,A (q.2,f q.1))∈U ∧
      B (q.2,f q.1) < 0 := by
  let Q:=fun q:E×ℝ=>(q.2,f q.1)
  have hQ:ContinuousAt Q (x,β) := continuousAt_snd.prodMk (hf.comp continuousAt_fst)
  let J:=fun q:E×ℝ=>(q.1,A (q.2,f q.1))
  have hJ:ContinuousAt J (x,β) := continuousAt_fst.prodMk
    (hA.continuousAt.comp hQ)
  have hJU:J ⁻¹' U∈𝓝 (x,β) := hJ.preimage_mem_nhds hU
  have hK:ContinuousAt (fun q:E×ℝ=>B (q.2,f q.1)) (x,β) :=
    hB.continuousAt.comp hQ
  exact ⟨{q|J q∈U ∧ B (q.2,f q.1) < 0},
    inter_mem hJU (hK.eventually (gt_mem_nhds hcurve)),fun q hq=>hq⟩

end WeakMTWTransport

end

end OAI
