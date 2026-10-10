import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.Composition

namespace OAI

/-! # Restricting an analytic inverse chart to its analytic domain -/

noncomputable section
namespace PolycyclicRecognition
open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_analytic_inverse_chart {f : E → E}
    (hf : ContDiffAt ℝ ω f 0) (h0 : f 0 = 0)
    (hd : HasFDerivAt f (ContinuousLinearMap.id ℝ E) 0) :
    ∃ q : OpenPartialHomeomorph E E,
      (0 : E) ∈ q.source ∧ q 0 = 0 ∧ (q : E → E) = f ∧
        ContDiffOn ℝ ω q.symm q.target := by
  let d := ContinuousLinearEquiv.refl ℝ E
  let q : OpenPartialHomeomorph E E := hf.toOpenPartialHomeomorph f (f' := d) hd (by simp)
  have hq0 : (0 : E) ∈ q.source := hf.mem_toOpenPartialHomeomorph_source (f' := d) hd (by simp)
  have hi : ContDiffAt ℝ ω q.symm 0 := by
    change ContDiffAt ℝ ω (hf.localInverse (f' := d) hd (by simp)) 0
    simpa only [h0] using hf.to_localInverse (f' := d) hd (by simp)
  obtain ⟨s,hs,hsi⟩ := hi.contDiffOn le_rfl (by intro _; rfl)
  obtain ⟨u,hus,hu,hu0⟩ := mem_nhds_iff.mp hs
  let r := OpenPartialHomeomorph.trans q (OpenPartialHomeomorph.ofSet u hu)
  refine ⟨r, ?_, ?_, rfl, ?_⟩
  · refine ⟨hq0, ?_⟩
    change f 0 ∈ u
    rwa [h0]
  · exact h0
  · change ContDiffOn ℝ ω (fun x => q.symm x) _
    apply hsi.mono
    intro x hx
    exact hus hx.1

end PolycyclicRecognition

end

end OAI
