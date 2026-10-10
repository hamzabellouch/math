import OAI.RepresentationTheory.FoulkesHowe.Model

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

variable (a b : ℕ) (V : Type u) [AddCommGroup V] [Module ℂ V]

 theorem foulkesFormula_diagonal (u : Fin b → V) :
    foulkesFormula a b V (fun j _ => u j) =
      symMonomial a (SymPow b V) (fun _ => symMonomial b V u) := by
  classical
  simp [foulkesFormula, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    Nat.factorial_ne_zero]

 theorem IsFoulkesMap.map_diagonal
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V))
    (hμ : IsFoulkesMap a b V μ) (u : Fin b → V) :
    μ (symMonomial b (SymPow a V) (fun j => symMonomial a V (fun _ => u j))) =
      symMonomial a (SymPow b V) (fun _ => symMonomial b V u) := by
  rw [hμ, foulkesFormula_diagonal]

end Problem346

end

end OAI
