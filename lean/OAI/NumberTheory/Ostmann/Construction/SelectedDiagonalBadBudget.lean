import OAI.NumberTheory.Ostmann.Construction.DiagonalFixedOverhead

namespace OAI

open Erdos970

noncomputable section
open scoped Classical
open Filter
namespace Ostmann.Construction
open Conclusion Arithmetic.HistoryProductWindows

theorem selected_diagonal_bad_scalar_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,C.selectedDiagonalNormalizer l*
        (Nat.card {e // InitialSourceChoice.diagonalBadPermutation (2*(bulkSize k L/2)) k l e}:ℝ)*
        Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l)≤
      Real.exp (-stepGap BD Bz k L l+
        (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+37)*
          (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))) := by
  filter_upwards [selected_diagonal_bad_count_budget_eventually d Bs BD Bz hk,
    diagonal_fixed_overhead_absorbed_eventually hk] with L hcount hfixed
  intro E C hG hGu hcl hcu hb hd l hl
  have hc := hcount E C hG hGu hcl hcu hb hd l
  have hf := hfixed l hl
  calc
    _ ≤ (diagonalMatchingOverhead (bulkSize k L) k l*
        Real.exp (-stepGap BD Bz k L l+
          (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+36)*
            (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))))*
        Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = (diagonalMatchingOverhead (bulkSize k L) k l*
        Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l))*
        Real.exp (-stepGap BD Bz k L l+
          (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+36)*
            (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))) := by ring
    _ ≤ Real.exp ((2:ℝ)^l*(bulkSize k L:ℝ))*
        Real.exp (-stepGap BD Bz k L l+
          (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+36)*
            (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))) :=
      mul_le_mul_of_nonneg_right hf (Real.exp_pos _).le
    _ = _ := by
      rw [←Real.exp_add]
      congr 1
      push_cast
      ring

end Ostmann.Construction

end

end OAI
