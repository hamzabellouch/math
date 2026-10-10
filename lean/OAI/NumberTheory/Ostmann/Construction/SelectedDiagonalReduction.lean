import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalBadEnergy
import OAI.NumberTheory.Ostmann.Construction.SelectedDiagonalGoodEnergy

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
open Filter
namespace Ostmann.Construction
open Conclusion

theorem selected_diagonal_le_single_energy_and_good_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
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
      extendedDiagonal d C.favorable C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) C.giant spectator (2*s) X C.giantCenter
        (Arithmetic.sourceStateBins (bulkSize k L/2) s C.bulkBin C.spectatorBin) l≤
      Real.exp (-stepGap BD Bz k L l+
        (Real.log (bulkScale k)+(1/4:ℝ)*Real.log (((2^l:ℕ):ℝ))+37)*
          (((2^l:ℕ):ℝ)*(bulkSize k L:ℝ)))*C.selectedDiagonalSingleEnergy spectator s X l+
      C.selectedDiagonalNormalizer l*(C.selectedGoodCovarianceSum spectator s X l).re := by
  filter_upwards [selected_diagonal_environment_eventually d Bs BD Bz hk,
    selected_diagonal_bad_energy_eventually d Bs BD Bz hk] with L hD hbad
  intro E C hG hGu hcl hcu hb hd spectator hspec s X l hl
  have h := hD E C hG hcl hcu hb hd spectator hspec s X l hl
  rw [C.selectedDiagonalCovariance_sum_split spectator s X l,Complex.add_re,mul_add] at h
  exact h.trans (add_le_add (hbad E C hG hGu hcl hcu hb hd spectator hspec s X l hl) (le_refl _))

end Ostmann.Construction

end

end OAI
