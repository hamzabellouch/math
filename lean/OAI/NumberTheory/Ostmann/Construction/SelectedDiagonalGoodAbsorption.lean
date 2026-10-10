import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodEnergy
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodNormalizer

namespace OAI

open Erdos970

noncomputable section
open Filter
namespace Ostmann.Construction
open Conclusion

theorem selected_diagonal_good_absorption_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k)
    (hD : 0≤BD) (hz : 0≤Bz) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀(spectator : PrimeSource)(s : ℕ)(X : ℝ),∀l≤k,
      (∀e,InitialSourceChoice.diagonalGoodPermutation (2*(bulkSize k L/2)) k l e →
        ‖C.selectedDiagonalCovariance spectator s X l e‖≤
          Real.exp (-(selectedDiagonalGoodRate k+67*(2:ℝ)^k)*(bulkSize k L:ℝ))) →
      C.selectedDiagonalNormalizer l*(C.selectedGoodCovarianceSum spectator s X l).re≤
        Real.exp (-67*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_diagonal_good_normalizer_eventually d Bs BD Bz hk hD hz]
    with L hN
  intro E C hG hGu hcl hcu hb hd spectator s X l hl hgood
  have h := C.selectedGoodCovarianceSum_normalized_le spectator s X l
    (Real.exp (-(selectedDiagonalGoodRate k+67*(2:ℝ)^k)*(bulkSize k L:ℝ)))
    (Real.exp_pos _).le hgood
  refine h.trans ((mul_le_mul_of_nonneg_right
    (hN E C hG hGu hcl hcu hb hd l hl) (Real.exp_pos _).le).trans ?_)
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hp : (2:ℝ)^l≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hl
  have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (bulkSize k L))
  nlinarith

end Ostmann.Construction

end

end OAI
