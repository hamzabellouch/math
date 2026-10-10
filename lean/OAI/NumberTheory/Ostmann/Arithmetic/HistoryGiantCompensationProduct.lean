import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationProductBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCompensationProduct
open Construction HistorySignedResidues Filter

theorem selected_pair_compensationProduct_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ (m l : ℕ), l ≤ k → ∀ (V : ℕ → ℕ) (a b : State)
        (c e : HistoryChoices C.sources (Template.initial m k) V l),
      Template.Matches (Template.current (Template.initial m k) l) a.small →
      Template.Matches (Template.current (Template.initial m k) l) b.small →
      choicesMass C.sources (Template.initial m k) V l c ≠ 0 →
      choicesMass C.sources (Template.initial m k) V l e ≠ 0 →
      ((decodeHistory C.sources (Template.initial m k) V l a c).compensationProduct : ℝ) *
        ((decodeHistory C.sources (Template.initial m k) V l b e).compensationProduct : ℝ) ≤
          (actualFactorCap Bs BD Bz k L) ^ (4*l*2^l) := by
  filter_upwards [selected_sources_factorCap_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd m l hl V a b c e ha ha' hc he
  exact decoded_pair_compensationProduct_initial_le C.sources V m k l hl a b c e
    ha ha' hc he _ ((zero_le_one.trans (actualFactorCap_one_le Bs BD Bz k L)))
    (hL E C hG hcl hcu hb hd)

theorem decoded_pair_compensationProduct_norm_initial_le
    (sources : SourceFamily) (V : ℕ → ℕ) (m k l : ℕ) (hl : l ≤ k)
    (a b : State) (c e : HistoryChoices sources (Template.initial m k) V l)
    (ha : Template.Matches (Template.current (Template.initial m k) l) a.small)
    (hb : Template.Matches (Template.current (Template.initial m k) l) b.small)
    (hc : choicesMass sources (Template.initial m k) V l c ≠ 0)
    (he : choicesMass sources (Template.initial m k) V l e ≠ 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ origin, ∀ p : (sources origin).Sample,
      (sources origin).law.mass p ≠ 0 → (p.val : ℝ) ≤ B) :
    ‖((decodeHistory sources (Template.initial m k) V l a c).compensationProduct : ℂ) *
      ((decodeHistory sources (Template.initial m k) V l b e).compensationProduct : ℂ)‖ ≤
        B ^ (4*l*2^l) := by
  simpa only [norm_mul,Complex.norm_natCast] using
    decoded_pair_compensationProduct_initial_le sources V m k l hl a b c e ha hb hc he B hB hsource

end Ostmann.Arithmetic.HistoryGiantCompensationProduct

end

end OAI
