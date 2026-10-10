import OAI.GroupTheory.PolycyclicRecognition.Finiteness.InfiniteCyclicDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TrivialGroupDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PolycyclicDualityComparison

namespace OAI

/-! # The cyclic base cases of polycyclic finiteness and duality -/

noncomputable section
namespace PolycyclicRecognition

variable (G : Type) [Group G]

theorem typeFPInfinity_of_cyclic [IsCyclic G] : TypeFPInfinity G := by
  cases finite_or_infinite G with
  | inl h =>
      let := h
      exact typeFPInfinity_of_finite G
  | inr h =>
      let := h
      let := IsCyclic.commGroup (α := G)
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
      exact typeFPInfinity_of_infinite_cyclic G g hg

theorem subsingleton_of_finite_torsionFree [Finite G]
    (ht : HasNoNontrivialTorsion G) : Subsingleton G := by
  have hone (g : G) : g = 1 :=
    ht g (orderOf g) (ne_of_gt (orderOf_pos g)) (pow_orderOf_eq_one g)
  exact ⟨fun g h => (hone g).trans (hone h).symm⟩

theorem poincareDuality_of_cyclic [IsCyclic G] (ht : HasNoNontrivialTorsion G) :
    ∃ n, IsIntegralPoincareDualityGroup G n := by
  cases finite_or_infinite G with
  | inl h =>
      let := h
      let := subsingleton_of_finite_torsionFree G ht
      exact ⟨0, poincareDuality_zero_of_subsingleton G⟩
  | inr h =>
      let := h
      let := IsCyclic.commGroup (α := G)
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
      exact ⟨1, poincareDuality_one_of_infinite_cyclic G g hg⟩

end PolycyclicRecognition

end

end OAI
