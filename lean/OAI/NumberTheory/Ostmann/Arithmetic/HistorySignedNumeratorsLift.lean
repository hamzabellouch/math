import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsPair

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedNumerators
open Construction HistorySignedDecode HistoryPairPattern HistoryPairRows MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem pairActual_square_dvd_lift_iff (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (i : Occurrences h k) (p : ℕ) [Fact p.Prime]
    (X Y carry u v : ℤ)
    (hi : (rebuild h (X + (p : ℤ) * u) (Y + (p : ℤ) * v)).IntegralGuard)
    (ki : (rebuild k (X + (p : ℤ) * u) (Y + (p : ℤ) * v)).IntegralGuard)
    (hx : AncestorUnits h k (fun j => (pairSample h k j : ZMod p)) i)
    (hV : ∀ j ≤ l, V j < p)
    (hbase : eval (pairSample h k) (leftFlag h k hs ks i) * X +
      eval (pairSample h k) (rightFlag h k hs ks i) * Y = (p : ℤ) * carry) :
    (p : ℤ)^2 ∣ pairActual h k (X + (p : ℤ) * u) (Y + (p : ℤ) * v) i ↔
      (eval (pairSample h k) (leftFlag h k hs ks i) : ZMod p) * (u : ZMod p) +
      (eval (pairSample h k) (rightFlag h k hs ks i) : ZMod p) * (v : ZMod p) =
        -(carry : ZMod p) := by
  rw [pairActual_power_dvd_iff h k hs ks hroot _ _ hi ki i p 2 hx hV, pow_two]
  exact PrimeSquareLifts.square_divides_lift_iff_residue p _ _ X Y carry u v hbase

end Ostmann.Arithmetic.HistorySignedNumerators

end

end OAI
