import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairNumerators

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacement
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem family_nonzero_at_new_prime (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (p : ℕ) [Fact p.Prime]
    (x : PairKey h k → ZMod p) (i₀ : Fiber h k r)
    (hx : AncestorUnits h k x i₀.val) (hV : ∀j ≤ l,V j < p) :
    ¬∀i : Fiber h k r,leftRows h k hs ks r p x i=0 ∧ rightRows h k hs ks r p x i=0 := by
  intro hz
  have hn := flags_nonzero_field h k hs ks i₀.val x hx
    (HistoryPairNumerators.frequency_units h k hs ks p hV)
  exact hn.elim (fun hh=>hh (hz i₀).1) (fun hh=>hh (hz i₀).2)

end Ostmann.Arithmetic.HistoryPairKernelReplacement

end

end OAI
