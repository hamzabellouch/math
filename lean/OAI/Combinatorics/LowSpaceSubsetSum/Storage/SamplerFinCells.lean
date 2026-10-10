import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerVectorCells

namespace OAI

/-! # The executable finite-range sampler with its stored candidates -/

noncomputable section
namespace LowSpaceSubsetSum.SamplerFinCells

variable {α : Type} [Fintype α]

def cast {S T : SamplerCoupling α} (h : S = T)
    (run : S.Seed → SamplerExecution.Trace α × ℕ) :
    T.Seed → SamplerExecution.Trace α × ℕ := h ▸ run

theorem cast_value {S T : SamplerCoupling α} (h : S = T)
    (run : S.Seed → SamplerExecution.Trace α × ℕ) (source : SamplerExecution.Execution S)
    (hv : ∀ s, (run s).1 = source.run s) (s : T.Seed) :
    (cast h run s).1 = (SamplerExecution.cast h source).run s := by
  subst T
  exact hv s

theorem cast_cells {S T : SamplerCoupling α} (h : S = T)
    (run : S.Seed → SamplerExecution.Trace α × ℕ) (K : ℕ)
    (hc : ∀ s, (run s).2 ≤ K) (s : T.Seed) : (cast h run s).2 ≤ K := by
  subst T
  exact hc s

def run (n D : ℕ) [NeZero D] : (finCoupling n D).Seed → SamplerExecution.Trace (Fin D) × ℕ :=
  if h : 1 < D then
    cast (by simp only [finCoupling, dite_eq_left h]) (SamplerVectorCells.rangeSeed h n)
  else
    cast (S := SamplerCoupling.pure (⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩ : Fin D))
      (by simp only [finCoupling, dite_eq_right h])
      (fun _ => (⟨some ⟨0, Nat.pos_of_ne_zero (NeZero.ne D)⟩, 0, 0⟩, 8))

theorem run_value (n D : ℕ) [NeZero D] (s : (finCoupling n D).Seed) :
    (run n D s).1 = (SamplerExecution.fin n D).run s := by
  by_cases h : 1 < D
  · simp only [run, SamplerExecution.fin, dite_eq_left h]
    exact cast_value _ _ (SamplerExecution.range h n) (SamplerVectorCells.rangeSeed_value h n) s
  · simp only [run, SamplerExecution.fin, dite_eq_right h]
    exact cast_value _ _ (SamplerExecution.pure _) (fun _ => rfl) s

theorem run_cells (n D : ℕ) [NeZero D] (s : (finCoupling n D).Seed) :
    (run n D s).2 ≤ 3*n^3+80 := by
  by_cases h : 1 < D
  · simp only [run, dite_eq_left h]
    apply cast_cells
    intro t
    exact (SamplerVectorCells.rangeSeed_cells h n t).trans (by omega)
  · simp only [run, dite_eq_right h]
    apply cast_cells
    intro t
    dsimp only
    omega

end LowSpaceSubsetSum.SamplerFinCells

end

end OAI
