import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearCells

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
variable {ρ κ : Type*} [Fintype ρ]

def rowCharacterKernel (q : κ → ℕ) (χ : ∀ j, MulChar (ZMod (q j)) ℂ)
    (Q N : ℕ) (a : ρ → ℕ) (W : ρ → ℕ → κ → ℂ) (x : ρ × Fin N) (j : κ) : ℂ :=
  primeCharacterKernel q χ Q (a x.1) (W x.1) x.2 j

def rowCrossVariation (cuts : Finset ℝ) (Q N : ℕ) (a : ρ → ℕ)
    (b : ρ → ℕ → ℝ) (W : ρ → ℕ → κ → ℂ) (j k : κ) : ℝ :=
  ∑ r, ∑ c : CutPieceIndex cuts,
    progressionVariation (pieceProgressionWeight cuts Q (a r)
      (crossProgressionWeight (b r) (W r) j k) c) N

theorem oneSidedGram_rows_eq (q : κ → ℕ) (χ : ∀ j, MulChar (ZMod (q j)) ℂ)
    (Q N : ℕ) (a : ρ → ℕ) (b : ρ → ℕ → ℝ) (W : ρ → ℕ → κ → ℂ) (j k : κ) :
    oneSidedGram (fun x : ρ × Fin N => b x.1 x.2) (rowCharacterKernel q χ Q N a W) j k =
      ∑ r, oneSidedGram (fun n : Fin N => b r n)
        (fun n : Fin N => primeCharacterKernel q χ Q (a r) (W r) n) j k := by
  simp only [oneSidedGram, Fintype.sum_prod_type, rowCharacterKernel]

theorem characterGram_rows_bound (q : κ → ℕ) (hq : ∀ j, (q j).Prime)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q N : ℕ) (a : ρ → ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (b : ρ → ℕ → ℝ) (W : ρ → ℕ → κ → ℂ) (j k : κ) (hjk : q j ≠ q k)
    (cuts : Finset ℝ) :
    ‖oneSidedGram (fun x : ρ × Fin N => b x.1 x.2) (rowCharacterKernel q χ Q N a W) j k‖ ≤
      (q j*q k : ℕ) * rowCrossVariation cuts Q N a b W j k := by
  rw [oneSidedGram_rows_eq]
  calc
    _ ≤ ∑ r, ‖oneSidedGram (fun n : Fin N => b r n)
        (fun n : Fin N => primeCharacterKernel q χ Q (a r) (W r) n) j k‖ := norm_sum_le _ _
    _ ≤ ∑ r, (q j*q k : ℕ) * ∑ c : CutPieceIndex cuts,
        progressionVariation (pieceProgressionWeight cuts Q (a r)
          (crossProgressionWeight (b r) (W r) j k) c) N := by
      apply Finset.sum_le_sum
      intro r hr
      exact characterGram_cells_bound q hq χ hχ Q (a r) N hQ (b r) (W r) j k hjk cuts
    _ = _ := by rw [← Finset.mul_sum]; rfl

end Ostmann.Characters

end

end OAI
