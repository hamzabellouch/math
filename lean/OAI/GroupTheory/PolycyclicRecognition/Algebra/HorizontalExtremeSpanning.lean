import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChamberExtremeDirections
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace OAI

/-! # Finitely many extreme and kernel directions span the horizontal layer -/

noncomputable section

namespace PolycyclicRecognition

open Set

theorem exists_finite_spanning_horizontal_directions
    {V W I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I]
    (π : V →L[ℝ] W) (hπ : Function.Surjective π)
    (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    (hne : (weightChamber α σ).Nonempty) :
    ∃ S : Finset V, Submodule.span ℝ (S : Set V) = ⊤ ∧
      ∀ v ∈ S, π v = 0 ∨ π v ∈ chamberExtremeDirections α σ := by
  let D := chamberExtremeDirections α σ
  let E : Set V := {v | π v = 0 ∨ π v ∈ D}
  let P := Submodule.span ℝ E
  have hker : π.ker ≤ P := by
    intro v hv
    exact Submodule.subset_span (Or.inl hv)
  have himage : Submodule.span ℝ D ≤ P.map π.toLinearMap := by
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨v, hv⟩ := hπ w
    refine ⟨v, Submodule.subset_span (Or.inr ?_), hv⟩
    rwa [hv]
  have hDtop : Submodule.span ℝ D = ⊤ := span_chamberExtremeDirections_eq_top α σ hsep hne
  have hPtop : P = ⊤ := by
    apply top_unique
    intro v _hv
    have hvimage : π v ∈ P.map π.toLinearMap := himage (hDtop ▸ Submodule.mem_top)
    obtain ⟨u, hu, he⟩ := hvimage
    change π u = π v at he
    have hdiff : v - u ∈ π.ker := by
      change π (v - u) = 0
      rw [map_sub, he, sub_self]
    have hsum := P.add_mem (hker hdiff) hu
    simpa only [sub_add_cancel] using hsum
  obtain ⟨S, hSE, _hcard, hspan, _hindep⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ E
  refine ⟨S, hspan.trans hPtop, ?_⟩
  intro v hv
  exact hSE hv

end PolycyclicRecognition

end

end OAI
