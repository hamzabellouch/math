import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearProgressions
import OAI.NumberTheory.Ostmann.Characters.PolynomialSupportPartitionTotal

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
attribute [local instance] Classical.propDecidable

def pieceProgressionWeight (cuts : Finset ℝ) (Q a : ℕ) (w : ℕ → ℂ)
    (c : CutPieceIndex cuts) (n : ℕ) : ℂ :=
  if ((Q*n+a : ℕ) : ℝ) ∈ cutPiece cuts c then w n else 0

theorem sum_pieceProgressionWeight (cuts : Finset ℝ) (Q a : ℕ) (w : ℕ → ℂ) (n : ℕ) :
    (∑ c : CutPieceIndex cuts, pieceProgressionWeight cuts Q a w c n) = w n := by
  have hmem : ((Q*n+a : ℕ) : ℝ) ∈ ⋃ c : CutPieceIndex cuts, cutPiece cuts c := by
    rw [iUnion_cutPiece]
    trivial
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hmem
  calc
    _ = pieceProgressionWeight cuts Q a w c n := by
      apply Finset.sum_eq_single c
      · intro c' hc' hne
        have hnot : ((Q*n+a : ℕ) : ℝ) ∉ cutPiece cuts c' := by
          intro hx
          exact Set.disjoint_left.mp (cutPiece_pairwiseDisjoint cuts hne) hx hc
        simp only [pieceProgressionWeight, ite_eq_right hnot]
      · simp
    _ = _ := by simp only [pieceProgressionWeight, ite_eq_left hc]

theorem progressionVariation_sum_le {ρ : Type*} [Fintype ρ]
    (w : ρ → ℕ → ℂ) (N : ℕ) :
    progressionVariation (fun n => ∑ r, w r n) N ≤ ∑ r, progressionVariation (w r) N := by
  unfold progressionVariation
  rw [Finset.sum_add_distrib]
  apply add_le_add (norm_sum_le _ _) _
  calc
    _ = ∑ n ∈ Finset.range (N-1), ‖∑ r, (w r (n+1)-w r n)‖ := by
      simp only [Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ Finset.range (N-1), ∑ r, ‖w r (n+1)-w r n‖ :=
      Finset.sum_le_sum (fun n _ => norm_sum_le _ _)
    _ = _ := Finset.sum_comm

theorem progressionVariation_le_pieces (cuts : Finset ℝ) (Q a : ℕ)
    (w : ℕ → ℂ) (N : ℕ) :
    progressionVariation w N ≤
      ∑ c : CutPieceIndex cuts, progressionVariation (pieceProgressionWeight cuts Q a w c) N := by
  have h := progressionVariation_sum_le (pieceProgressionWeight cuts Q a w) N
  simpa only [sum_pieceProgressionWeight] using h

theorem characterGram_cells_bound {κ : Type*} (q : κ → ℕ) (hq : ∀ j, (q j).Prime)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q a N : ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (b : ℕ → ℝ) (W : ℕ → κ → ℂ) (j k : κ) (hjk : q j ≠ q k) (cuts : Finset ℝ) :
    ‖oneSidedGram (fun n : Fin N => b n)
      (fun n : Fin N => primeCharacterKernel q χ Q a W n) j k‖ ≤
      (q j*q k : ℕ) * ∑ c : CutPieceIndex cuts,
        progressionVariation (pieceProgressionWeight cuts Q a (crossProgressionWeight b W j k) c) N := by
  exact (characterGram_bound q hq χ hχ Q a N hQ b W j k hjk).trans
    (mul_le_mul_of_nonneg_left (progressionVariation_le_pieces cuts Q a _ N) (Nat.cast_nonneg _))

end Ostmann.Characters

end

end OAI
