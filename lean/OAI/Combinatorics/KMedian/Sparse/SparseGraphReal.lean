import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseGraphLaw
import OAI.Combinatorics.KMedian.Sparse.SparseRealLaw

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

@[simp] theorem cast_edge (G : Graph n m) (h : Fin n) (i : Fin m) :
    (edge G h i:ℝ)=GraphLaw.edge G h i := by
  by_cases he : h∈G i <;> simp [edge,GraphLaw.edge,he]

theorem real_law_spec (q : Fin n → Fin m → ℚ) (Δ : ℕ)
    (hq : ∀ h i, 0 ≤ q h i ∧ q h i ≤ 1) (hs : ∀ i, (∑ h, q h i)=(Δ:ℚ)) :
    (∀ G, 0 < (law q).real.weight G → ∀ i, (G i).card=Δ) ∧
    (∀ h i, (law q).real.expect (fun G => GraphLaw.edge G h i)=(q h i:ℝ)) ∧
    (∀ h l i j, i≠j → (law q).real.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G l j)=
      (q h i:ℝ)*(q l j:ℝ)) ∧
    (∀ G, 0 < (law q).real.weight G → ∀ h i, q h i=1 → h∈G i) ∧
    (∀ G, 0 < (law q).real.weight G → ∀ h i, q h i=0 → h∉G i) := by
  have h := law_spec q Δ hq hs
  refine ⟨(law q).real_property _ h.2.1,?_,?_,?_,?_⟩
  · intro a i
    simp only [← cast_edge,SparseIntegerLaw.real_expect,h.2.2.1]
  · intro a b i j hij
    simp only [← cast_edge,← Rat.cast_mul,SparseIntegerLaw.real_expect,h.2.2.2 a b i j hij]
  · exact (law q).real_property _ (fun a h i => (law_fixed q Δ hq hs a h i).1)
  · exact (law q).real_property _ (fun a h i => (law_fixed q Δ hq hs a h i).2)

end MetricKMedian.SparseGraph
end
end

end OAI
