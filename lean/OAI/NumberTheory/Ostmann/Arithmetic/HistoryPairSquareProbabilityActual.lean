import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPolynomialKernel
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityLines
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsLift

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open Construction Characters.RationalHistory HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives MvPolynomial
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

def actualLeft (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : Fiber h k r→ℤ :=
  fun i => eval (pairSample h k) (leftFlag h k hs ks i.val)
def actualRight (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : Fiber h k r→ℤ :=
  fun i => eval (pairSample h k) (rightFlag h k hs ks i.val)

lemma actualLeft_cast (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) :
    (fun i => (actualLeft h k hs ks r i:ZMod (prime h k r)))=
      HistoryPairPrimeIntegration.leftRows h k hs ks r (fun j => (pairSample h k j:ZMod (prime h k r))) := by
  funext i
  exact (Expr.eval₂_cast_int _ (pairSample h k)).symm

lemma actualRight_cast (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) :
    (fun i => (actualRight h k hs ks r i:ZMod (prime h k r)))=
      HistoryPairPrimeIntegration.rightRows h k hs ks r (fun j => (pairSample h k j:ZMod (prime h k r))) := by
  funext i
  exact (Expr.eval₂_cast_int _ (pairSample h k)).symm

theorem actual_rows_nonzero (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (r : Representative h k)
    (hx : HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r)))) :
    ∀i : Fiber h k r,(actualLeft h k hs ks r i:ZMod (prime h k r))≠0 ∨
      (actualRight h k hs ks r i:ZMod (prime h k r))≠0 := by
  intro i
  rcases HistoryPairPolynomialKernel.flags_polynomial_nonzero h k hs ks hroot i.val with hl | hr
  · left
    intro hz
    apply hl
    apply (hx.1 i).mp
    rw [Expr.eval₂_cast_int]
    exact hz
  · right
    intro hz
    apply hr
    apply (hx.2.1 i).mp
    rw [Expr.eval₂_cast_int]
    exact hz

lemma actual_unit_base_eq_kernel (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (r : Representative h k) [Fact (prime h k r).Prime]
    (hx : HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r)))) :
    unitBaseProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r)=
      HistoryPairPolynomialKernel.unitKernel h k hs ks r := by
  rw [unitBaseProbability_eq_lines,actualLeft_cast,actualRight_cast]
  exact HistoryPairPolynomialKernel.probability_eq_unitKernel h k hs ks hroot r _ hx

lemma actual_mixed_base_eq_kernel (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (r : Representative h k) [Fact (prime h k r).Prime]
    (hx : HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r)))) :
    mixedBaseProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r)=
      HistoryPairPolynomialKernel.mixedKernel h k hs ks r := by
  rw [mixedBaseProbability_eq_lines,actualLeft_cast,actualRight_cast]
  exact HistoryPairPolynomialKernel.probability_eq_mixedKernel h k hs ks hroot r _ hx

theorem actual_unit_square_loss (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (r : Representative h k) [Fact (prime h k r).Prime]
    (hx : HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r)))) :
    0 ≤ HistoryPairPolynomialKernel.unitKernel h k hs ks r-
      unitGoodProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r) ∧
    HistoryPairPolynomialKernel.unitKernel h k hs ks r-
      unitGoodProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r) ≤
      ((Fintype.card (Fiber h k r):ℝ)/prime h k r)*HistoryPairPolynomialKernel.unitKernel h k hs ks r := by
  have hh := unit_square_loss (prime h k r) Finset.univ (actualLeft h k hs ks r)
    (actualRight h k hs ks r) (fun i _ => actual_rows_nonzero h k hs ks hroot r hx i)
  simpa only [Finset.card_univ,actual_unit_base_eq_kernel h k hs ks hroot r hx] using hh

theorem actual_mixed_square_loss (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (r : Representative h k) [Fact (prime h k r).Prime]
    (hx : HistoryPairPolynomialKernel.NoAccidentalFlags h k hs ks r
      (fun j => (pairSample h k j:ZMod (prime h k r)))) :
    0 ≤ HistoryPairPolynomialKernel.mixedKernel h k hs ks r-
      mixedGoodProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r) ∧
    HistoryPairPolynomialKernel.mixedKernel h k hs ks r-
      mixedGoodProbability (prime h k r) Finset.univ (actualLeft h k hs ks r) (actualRight h k hs ks r) ≤
      ((Fintype.card (Fiber h k r):ℝ)/prime h k r)*HistoryPairPolynomialKernel.mixedKernel h k hs ks r := by
  have hh := mixed_square_loss (prime h k r) Finset.univ (actualLeft h k hs ks r)
    (actualRight h k hs ks r) (fun i _ => actual_rows_nonzero h k hs ks hroot r hx i)
  simpa only [Finset.card_univ,actual_mixed_base_eq_kernel h k hs ks hroot r hx] using hh

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
