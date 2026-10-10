import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseRealLaw
import OAI.Combinatorics.KMedian.Sparse.SparseEnumeratedGraph

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedGraph
open Finset
variable {I : Type} [DecidableEq I] [Fintype I] {n : ℕ}

omit [Fintype I] [DecidableEq I] in
theorem fixed (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ))
    (a : Fin (law enum q).length) (h i : I) :
    (q h i=1 → h∈(law enum q).states[a.val] i) ∧
    (q h i=0 → h∉(law enum q).states[a.val] i) := by
  have he := SparseIntegerLaw.map_states (SparseGraph.law (fun h i => q (enum h) (enum i))) (lift enum) a
  change (law enum q).states[a.val]=_ at he
  rw [he]
  simp only [mem_lift]
  have hh := SparseGraph.law_fixed (fun h i => q (enum h) (enum i)) Δ
    (fun h i => hq (enum h) (enum i)) (fun i => hs (enum i)) a (enum.symm h) (enum.symm i)
  simpa only [Equiv.apply_symm_apply] using hh

theorem real_spec (enum : Fin n ≃ I) (q : I → I → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1)
    (hs : ∀ i, (∑ h : Fin n, q (enum h) i)=(Δ:ℚ)) :
    (∀ G, 0 < (law enum q).real.weight G → ∀ i, (G i).card=Δ) ∧
    (∀ h i, (law enum q).real.expect (fun G => GraphLaw.edge G h i)=(q h i:ℝ)) ∧
    (∀ h l i j, i≠j → (law enum q).real.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=
      (q h i:ℝ)*(q l j:ℝ)) ∧
    (∀ G, 0 < (law enum q).real.weight G → ∀ h i, q h i=1 → h∈G i) ∧
    (∀ G, 0 < (law enum q).real.weight G → ∀ h i, q h i=0 → h∉G i) := by
  refine ⟨(law enum q).real_property _ (columns_card enum q Δ hq hs),?_,?_,?_,?_⟩
  · intro h i
    have he : (fun G : I → Finset I => GraphLaw.edge G h i)=
        (fun G => ((if h∈G i then 1 else 0:ℚ):ℝ)) := by
      funext G
      by_cases hh : h∈G i <;> simp [GraphLaw.edge,hh]
    rw [he,SparseIntegerLaw.real_expect,single enum q Δ hq hs]
  · intro h l i j hij
    have he : (fun G : I → Finset I => GraphLaw.edge G h i*GraphLaw.edge G l j)=
        (fun G => (((if h∈G i then 1 else 0)*(if l∈G j then 1 else 0):ℚ):ℝ)) := by
      funext G
      by_cases hh : h∈G i <;> by_cases hl : l∈G j <;> simp [GraphLaw.edge,hh,hl]
    rw [he,SparseIntegerLaw.real_expect,pair enum q Δ hq hs h l i j hij,Rat.cast_mul]
  · exact (law enum q).real_property _ (fun a h i => (fixed enum q Δ hq hs a h i).1)
  · exact (law enum q).real_property _ (fun a h i => (fixed enum q Δ hq hs a h i).2)

end MetricKMedian.SparseEnumeratedGraph
end
end

end OAI
