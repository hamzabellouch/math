import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperJointLaw
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceDrawBounds
import OAI.Combinatorics.ContingencyTables.Dense.DenseMaximalReindex
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordPadding

namespace OAI

/-! # A finite Boolean draw of the actual state-dependent completion fibre -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open ResidualMixture FirstSuccess GridBoundary FairBits

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ)
variable (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
variable (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
variable {q : ℕ}
variable (e : ({i : LargeRows r ((dimensionAllowance (I := I) (J := J))^20) // i≠i₀} ×
  {j : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20) // j≠j₀}) ≃ Fin q)

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "R" => referenceRows r c (d^20) (d^12) (stateCapacity r c) i₀
local notation "P" => referenceColumns r c (d^20) (d^12) (stateCapacity r c) j₀

abbrev paperReferenceEquiv (z : PaperStates r c) : PaperFibre r c z ≃ Table (R z) (P z) :=
  referenceFibreEquiv r c _ _ (stateCapacity r c) i₀ j₀ z
    (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)

abbrev completionDrawBits (h : ℕ) (z : PaperStates r c) :=
  reindexedDrawBits (R z) (P z) d e h

def completionBooleanDraw (h : ℕ) (a : Grid (I := Fin q) (4*d^8))
    (z : PaperStates r c) (fallback : PaperFibre r c z)
    (bits : Fin (completionDrawBits r c i₀ j₀ e h z) → Bool) : PaperFibre r c z :=
  (paperReferenceEquiv r c i₀ j₀ z).symm
    (reindexedBooleanDraw (R z) (P z) d (reference_dimension_fourteen r c _ i₀ j₀)
      (reference_row_padding r c _ _ _ i₀ j₀ z)
      (reference_column_padding r c _ _ _ i₀ j₀ z) e
      (reference_totals r c _ _ _ i₀ j₀ z
        (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z)) h a
      (paperReferenceEquiv r c i₀ j₀ z fallback) bits)

/-- The output is a genuine completion of the current retained profile
on every bit word; the distance bound is uniform in that state. -/
theorem completionBooleanDraw_variation
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) (4*d^8)))
    (h : ℕ) (a : Grid (I := Fin q) (4*d^8))
    (z : PaperStates r c) (fallback : PaperFibre r c z) :
    (variation (mapLaw (uniformLaw (α := Fin (completionDrawBits r c i₀ j₀ e h z) → Bool))
      (completionBooleanDraw r c i₀ j₀ e h a z fallback))
      (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ (2:ℝ)^(-(h:ℝ)) := by
  let E := paperReferenceEquiv r c i₀ j₀ z
  let : Nonempty (Table (R z) (P z)) := ⟨E fallback⟩
  have hh := reindexedBooleanDraw_variation (R z) (P z) d
    (reference_dimension_fourteen r c _ i₀ j₀)
    (reference_row_padding r c _ _ _ i₀ j₀ z)
    (reference_column_padding r c _ _ _ i₀ j₀ z)
    (reference_block_dimensions r c _ i₀ j₀).1
    (reference_block_dimensions r c _ i₀ j₀).2.1
    (reference_free_dimension r c _ i₀ j₀)
    (reference_totals r c _ _ _ i₀ j₀ z
      (physical_paper_capacity _ r c _ _ _ dimension_le_allowance z))
    e hPL hCheeger h a (E fallback)
  unfold completionBooleanDraw
  rw [mapLaw_equiv_output]
  change (variation (equivLaw E.symm _) (uniformLaw (α := PaperFibre r c z)):ℝ) ≤ _
  rw [←uniform_equiv E.symm,variation_equiv]
  exact hh

lemma completionDrawBits_le (b h : ℕ)
    (hb : Nat.clog 2 (stateBound r c+2) ≤ b) (z : PaperStates r c) :
    completionDrawBits r c i₀ j₀ e h z ≤ 25*(d+b+h+1)^62 := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    rw [←hc]
    exact reference_free_dimension r c _ i₀ j₀
  exact reindexedDrawBits_polynomial (R z) (P z) d (stateBound r c) b h e hq
    (reference_row_le_stateBound r c i₀ z) hb

/-- One common reserved word works at every state, despite the different
residual margins and quotient lengths. -/
def completionPaddedDraw (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (a : Grid (I := Fin q) (4*d^8)) (z : PaperStates r c) (fallback : PaperFibre r c z)
    (bits : Fin (25*(d+b+h+1)^62) → Bool) : PaperFibre r c z :=
  completionBooleanDraw r c i₀ j₀ e h a z fallback
    (prefixWord (completionDrawBits_le r c i₀ j₀ e b h hb z) bits)

theorem completionPaddedDraw_law (b h : ℕ) (hb : Nat.clog 2 (stateBound r c+2) ≤ b)
    (a : Grid (I := Fin q) (4*d^8)) (z : PaperStates r c) (fallback : PaperFibre r c z) :
    mapLaw (uniformLaw (α := Fin (25*(d+b+h+1)^62) → Bool))
      (completionPaddedDraw r c i₀ j₀ e b h hb a z fallback)=
    mapLaw (uniformLaw (α := Fin (completionDrawBits r c i₀ j₀ e h z) → Bool))
      (completionBooleanDraw r c i₀ j₀ e h a z fallback) := by
  unfold completionPaddedDraw
  exact padded_draw_law (completionDrawBits_le r c i₀ j₀ e b h hb z)
    (completionBooleanDraw r c i₀ j₀ e h a z fallback)

end
end ContingencyTables.SmallGraphProfiles

end OAI
