import OAI.Combinatorics.ThinTrees.SparsifyGeometry

namespace OAI

section

noncomputable section
open Finset
namespace StrongThinTree.MultiGraph

theorem sparsification : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r → StepNumeric r ∧
    ∀(n m : ℕ) (G : MultiGraph n m), 2 ≤ n → G.TreePackable univ r →
      ∃A : Finset (Fin m), G.TreePackable A (stepCount r) ∧
        ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
          ((G.cut A S).card:ℝ) ≤ (1/2+3*splitTau r)*(G.cut univ S).card := by
  obtain ⟨RE,hRE,hE⟩ := extraction
  obtain ⟨RN,hN⟩ := eventual_step_numeric
  refine ⟨max RE RN,hRE.trans (le_max_left _ _),fun r hr => ?_⟩
  have hn := hN r ((le_max_right _ _).trans hr)
  refine ⟨hn,fun n m G hn' hp => ?_⟩
  obtain ⟨X,hX,hpack⟩ := hE r ((le_max_left _ _).trans hr) n m G hn' hp
  exact G.sparsify_from_extraction hn' hn hX hpack
end StrongThinTree.MultiGraph

end
end

end OAI
