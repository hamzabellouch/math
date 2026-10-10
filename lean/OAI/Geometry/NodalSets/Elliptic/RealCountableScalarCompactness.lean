import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences

namespace OAI

namespace Yau.Geometry
open Set Filter
open scoped Topology
noncomputable section

theorem real_countable_bounded_subsequence {I : Type*} [Countable I]
    (a : ℕ → I → ℝ) (B : I → ℝ) (hb : ∀ j i, |a j i| ≤ B i) :
    ∃ f : I → ℝ, ∃ nu : ℕ → ℕ, StrictMono nu ∧
      ∀ i, Tendsto (fun j ↦ a (nu j) i) atTop (𝓝 (f i)) := by
  have hc : IsCompact (univ.pi (fun i ↦ Icc (-B i) (B i))) :=
    isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hmem (j : ℕ) : a j ∈ univ.pi (fun i ↦ Icc (-B i) (B i)) := by
    intro i _
    exact abs_le.mp (hb j i)
  obtain ⟨f,_,nu,hnu,ht⟩ := hc.tendsto_subseq hmem
  exact ⟨f,nu,hnu,fun i ↦ ((continuous_apply i).tendsto f).comp ht⟩

end
end Yau.Geometry

end OAI
