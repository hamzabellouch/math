import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationError
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCompensationProduct

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCompensationError
open Construction Conclusion Filter HistoryGiantCompensationProduct

theorem selected_compensation_error_eventually
    (d : Decomposition) (Bs BD Bz T : ℝ) (hT : 0 ≤ T) {k : ℕ} (hk : 0 < k) :
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
      ∀ F : ℝ, 0 ≤ F → F ≤ Real.exp (rawLogBudget T L) →
      (((decodeHistory C.sources (Template.initial m k) V l a c).compensationProduct : ℝ) *
        ((decodeHistory C.sources (Template.initial m k) V l b e).compensationProduct : ℝ))*F*
          (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L))) ≤
            Real.exp (-Real.exp ((21/2000:ℝ)*L)) := by
  filter_upwards [selected_cap_error_eventually Bs BD Bz T k hT,
    selected_pair_compensationProduct_eventually d Bs BD Bz hk] with L herror hprod
  intro E C hG hcl hcu hb hd m l hl V a b c e ha ha' hc he F hF hFC
  exact herror l hl _ F (by positivity)
    (hprod E C hG hcl hcu hb hd m l hl V a b c e ha ha' hc he) hF hFC

end Ostmann.Arithmetic.HistoryGiantCompensationError

end

end OAI
