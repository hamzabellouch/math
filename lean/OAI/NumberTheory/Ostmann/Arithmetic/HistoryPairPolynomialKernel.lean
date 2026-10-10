import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlagScope
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairPrimeIntegration

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairPolynomialKernel
open Construction Characters.RationalHistory HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairPrimeIntegration
open ClearedCoefficientFlags MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem flags_polynomial_nonzero (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (i : Occurrences h k) : leftFlag h k hs ks i≠0 ∨ rightFlag h k hs ks i≠0 := by
  obtain ⟨ha,hb,hn⟩ := row_regular_nonzero h k hs ks hroot i
  have hn' : (row h k hs ks i).1.fieldEval (pairRationalSample h k)≠0 ∨
      (row h k hs ks i).2.fieldEval (pairRationalSample h k)≠0 := by
    simpa only [Expr.fieldEval_rat] using hn
  have hh := (row_nonzero_iff (row h k hs ks i).1 (row h k hs ks i).2 (pairRationalSample h k)
    ((Expr.fieldRegularAt_rat _ _).mpr ha) ((Expr.fieldRegularAt_rat _ _).mpr hb)).mpr hn'
  rcases hh with hh | hh
  · exact Or.inl (fun hz => hh (by change eval₂ _ _ (leftFlag h k hs ks i)=0; rw [hz,eval₂_zero]))
  · exact Or.inr (fun hz => hh (by change eval₂ _ _ (rightFlag h k hs ks i)=0; rw [hz,eval₂_zero]))

def unitKernel (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : ℝ := by
  classical
  exact if (∀ i j : Fiber h k r, minorFlag h k hs ks i.val j.val=0) ∧
      (∃ i : Fiber h k r, leftFlag h k hs ks i.val≠0 ∧ rightFlag h k hs ks i.val≠0)
    then (((prime h k r-1:ℕ):ℝ))⁻¹ else 0

def mixedKernel (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : ℝ := by
  classical
  exact if (∀ i j : Fiber h k r, minorFlag h k hs ks i.val j.val=0) ∧
      (∃ i : Fiber h k r, leftFlag h k hs ks i.val≠0)
    then (prime h k r:ℝ)⁻¹ else 0

def NoAccidentalFlags (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (x : PairKey h k → ZMod (prime h k r)) : Prop :=
  (∀ i : Fiber h k r, eval₂ (Int.castRingHom _) x (leftFlag h k hs ks i.val)=0 ↔
    leftFlag h k hs ks i.val=0) ∧
  (∀ i : Fiber h k r, eval₂ (Int.castRingHom _) x (rightFlag h k hs ks i.val)=0 ↔
    rightFlag h k hs ks i.val=0) ∧
  (∀ i j : Fiber h k r, eval₂ (Int.castRingHom _) x (minorFlag h k hs ks i.val j.val)=0 ↔
    minorFlag h k hs ks i.val j.val=0)

theorem polynomial_family_nonzero (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) :
    ¬ (∀ i : Fiber h k r, leftFlag h k hs ks i.val=0 ∧ rightFlag h k hs ks i.val=0) := by
  intro hz
  let i := Classical.choice (fiber_nonempty h k r)
  exact (flags_polynomial_nonzero h k hs ks hroot i.val).elim
    (fun hi => hi (hz i).1) (fun hi => hi (hz i).2)

theorem probability_eq_unitKernel (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) (hx : NoAccidentalFlags h k hs ks r x) :
    PrimeLineFamilies.probability (prime h k r) (leftRows h k hs ks r x) (rightRows h k hs ks r x) =
      unitKernel h k hs ks r := by
  classical
  rw [HistoryPairPrimeIntegration.probability_eq_flags]
  simp only [ne_eq,hx.1,hx.2.1,hx.2.2,polynomial_family_nonzero h k hs ks hroot r,ite_false,unitKernel]

theorem probability_eq_mixedKernel (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hroot : RootGiantsAgree h k)
    (r : Representative h k) [Fact (prime h k r).Prime]
    (x : PairKey h k → ZMod (prime h k r)) (hx : NoAccidentalFlags h k hs ks r x) :
    PrimeMixedLineFamilies.probability (prime h k r) (leftRows h k hs ks r x) (rightRows h k hs ks r x) =
      mixedKernel h k hs ks r := by
  classical
  have hm : PrimeMixedLineFamilies.AllMinorsZero (leftRows h k hs ks r x) (rightRows h k hs ks r x) ↔
      ∀ i j : Fiber h k r, eval₂ (Int.castRingHom _) x (minorFlag h k hs ks i.val j.val)=0 := by
    change PrimeLineFamilies.AllMinorsZero _ _ ↔ _
    exact minors_zero_iff h k hs ks r x
  rw [PrimeMixedLineFamilies.probability_eq_flags,hm]
  simp only [PrimeMixedLineFamilies.AllZero,leftRows,rightRows,ne_eq,hx.1,hx.2.1,hx.2.2,
    polynomial_family_nonzero h k hs ks hroot r,ite_false,mixedKernel]

theorem unitKernel_bounds (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : 0 ≤ unitKernel h k hs ks r ∧
      unitKernel h k hs ks r≤(((prime h k r-1:ℕ):ℝ))⁻¹ := by
  unfold unitKernel
  split_ifs <;> constructor <;> first | exact le_rfl | positivity

theorem mixedKernel_bounds (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) : 0 ≤ mixedKernel h k hs ks r ∧ mixedKernel h k hs ks r≤(prime h k r:ℝ)⁻¹ := by
  unfold mixedKernel
  split_ifs <;> constructor <;> first | exact le_rfl | positivity

end Ostmann.Arithmetic.HistoryPairPolynomialKernel

end

end OAI
