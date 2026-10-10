import OAI.Analysis.MutuallyUnbiased.Bases.Basic

namespace OAI

/-! Restriction and cardinality lemmas. These reductions do not establish the
no-seven or completion theorem, which remain separate proof obligations. -/

noncomputable section
namespace MUB6

theorem IsMUBFamily.reindex {m n : ℕ} {B : Fin n → Basis} (hB : IsMUBFamily B)
    (f : Fin m → Fin n) (hf : Function.Injective f) : IsMUBFamily (B ∘ f) := by
  intro r s hrs i j
  exact hB (f r) (f s) (fun h => hrs (hf h)) i j

theorem attainable_mono {m n : ℕ} (hmn : m ≤ n) (hn : Attainable n) :
    Attainable m := by
  rcases hn with ⟨B, hB⟩
  exact ⟨B ∘ Fin.castLE hmn, hB.reindex _ (Fin.castLE_injective hmn)⟩

theorem attainable_zero : Attainable 0 := by
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  intro r
  exact Fin.elim0 r

/-- Precise completion statement, including preservation of the original bases. -/
def SixExtendToSeven : Prop :=
  ∀ B : Fin 6 → Basis, IsMUBFamily B →
    ∃ C : Fin 7 → Basis, IsMUBFamily C ∧ ∀ i : Fin 6, C i.castSucc = B i

theorem no_six_of_completion (hcompletion : SixExtendToSeven)
    (hseven : ¬ Attainable 7) : ¬ Attainable 6 := by
  rintro ⟨B, hB⟩
  rcases hcompletion B hB with ⟨C, hC, _⟩
  exact hseven ⟨C, hC⟩

theorem family_size_le_five_of_no_six (hsix : ¬ Attainable 6)
    (n : ℕ) (hn : Attainable n) : n ≤ 5 := by
  by_contra h
  have h6 : 6 ≤ n := by omega
  exact hsix (attainable_mono h6 hn)

theorem N6_le_five_of_no_six (hsix : ¬ Attainable 6) : N6 ≤ 5 := by
  apply csSup_le (show Set.Nonempty {n : ℕ | Attainable n} from ⟨0, attainable_zero⟩)
  intro n hn
  exact family_size_le_five_of_no_six hsix n hn

end MUB6

end

end OAI
