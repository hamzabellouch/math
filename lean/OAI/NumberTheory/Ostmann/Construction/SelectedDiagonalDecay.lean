import OAI.NumberTheory.Ostmann.Conclusion.ScaleReserves
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalReduction

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
open Filter
namespace Ostmann.Construction
open Conclusion

theorem selected_diagonal_decay_of_actual_comparisons_eventually
    (d : Decomposition) (Bs BD Bz Cs : ℝ) {k : ℕ} (hk : 0 < k)
    (hBz : 9≤Bz) (hBD : Bs+Cs+105≤BD) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource),
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(s : ℕ)(X : ℝ),∀l<k,
      C.selectedDiagonalSingleEnergy spectator s X l≤
        Real.exp ((2:ℝ)^l*(initialGap Bs k L+Cs*(bulkSize k L:ℝ))) →
      C.selectedDiagonalNormalizer l*(C.selectedGoodCovarianceSum spectator s X l).re≤
        Real.exp (-67*(2:ℝ)^l*(bulkSize k L:ℝ)) →
      extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
        (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l≤
        Real.exp (-66*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_diagonal_le_single_energy_and_good_eventually d Bs BD Bz hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop (Real.log 2)] with L hD hm
  intro E C hG hGu hcl hcu hb hd spectator hspec s X l hl hsingle hgood
  have h := hD E C hG hGu hcl hcu hb hd spectator hspec s X l hl
  have hbad : Real.exp (-stepGap BD Bz k L l+
      (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+37)*
        (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ)))*C.selectedDiagonalSingleEnergy spectator s X l≤
      Real.exp (diagonalExponent Bs BD Bz (Cs+37) k L l) := by
    refine (mul_le_mul_of_nonneg_left hsingle (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    unfold diagonalExponent
    push_cast
    ring
  have hsum := h.trans (add_le_add hbad hgood)
  have hlog : Real.log 2≤(2:ℝ)^l*(bulkSize k L:ℝ) := by
    refine hm.trans ?_
    have hr : (1:ℝ)≤2^l := one_le_pow₀ (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (bulkSize k L))
  have h := diagonal_total_reserve (B:=31) (C:=Cs+37) (e:=0)
    (ω:=67*(2:ℝ)^l*(bulkSize k L:ℝ)) (by omega : 1≤k) hBz
    (by linarith : Bs+2*(31:ℝ)+(Cs+37)+6≤BD)
    (show (0:ℝ)≤(2:ℝ)^l*(bulkSize k L:ℝ) by positivity)
    (by norm_num : (2*(31:ℝ)+5)*(2:ℝ)^l*(bulkSize k L:ℝ)≤67*(2:ℝ)^l*(bulkSize k L:ℝ))
    hlog (by simpa only [add_zero,neg_mul] using hsum)
  norm_num only at h
  exact h

end Ostmann.Construction

end

end OAI
