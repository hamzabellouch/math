import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairFlagScope
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementPointwise

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacement
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem leftRows_congr_small (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (x y : PairKey h k → ZMod b)
    (hxy : ∀j, (∃a : ℕ × ℤ, j.val = Sum.inr a) → x j = y j) :
    leftRows h k hs ks r b x = leftRows h k hs ks r b y := by
  funext i
  exact HistoryPairFlagScope.eval_congr h k (level h k i.val) (leftFlag h k hs ks i.val)
    (HistoryPairFlagScope.flags_earlierSmall h k hs ks i.val).1 x y
    (fun j hj _ => hxy j hj)

theorem rightRows_congr_small (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (x y : PairKey h k → ZMod b)
    (hxy : ∀j, (∃a : ℕ × ℤ, j.val = Sum.inr a) → x j = y j) :
    rightRows h k hs ks r b x = rightRows h k hs ks r b y := by
  funext i
  exact HistoryPairFlagScope.eval_congr h k (level h k i.val) (rightFlag h k hs ks i.val)
    (HistoryPairFlagScope.flags_earlierSmall h k hs ks i.val).2 x y
    (fun j hj _ => hxy j hj)

theorem actualProbability_congr_small (mixed : Bool) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (b : ℕ) (x y : PairKey h k → ℤ)
    (hxy : ∀j, (∃a : ℕ × ℤ, j.val = Sum.inr a) → x j = y j) :
    actualProbability mixed h k hs ks r b x = actualProbability mixed h k hs ks r b y := by
  have hcast : ∀j, (∃a : ℕ × ℤ, j.val = Sum.inr a) → (x j : ZMod b) = (y j : ZMod b) :=
    fun j hj => congrArg (fun z : ℤ => (z : ZMod b)) (hxy j hj)
  have hl := leftRows_congr_small h k hs ks r b
    (fun j => (x j : ZMod b)) (fun j => (y j : ZMod b)) hcast
  have hr := rightRows_congr_small h k hs ks r b
    (fun j => (x j : ZMod b)) (fun j => (y j : ZMod b)) hcast
  unfold actualProbability
  split_ifs <;> simp only [hl,hr]

end Ostmann.Arithmetic.HistoryPairKernelReplacement

end

end OAI
