import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceTestsBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementPointwise
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbabilityBAverageBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBAverage
open Construction Characters.RationalHistory HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistoryPairSquareProbability HistoryCRTIntegration
open HistorySignedResidueFactorization ResidueHaar MvPolynomial
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

def actualLeftAt (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) : Fiber h k r→ℤ :=
  fun i => eval v (leftFlag h k hs ks i.val)

def actualRightAt (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) : Fiber h k r→ℤ :=
  fun i => eval v (rightFlag h k hs ks i.val)

lemma actualLeftAt_cast (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) :
    (fun i => (actualLeftAt h k hs ks v r i:ZMod (prime h k r)))=
      HistoryPairKernelReplacement.leftRows h k hs ks r (prime h k r) (fun j => (v j:ZMod (prime h k r))) := by
  funext i
  exact (Expr.eval₂_cast_int _ v).symm

lemma actualRightAt_cast (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) :
    (fun i => (actualRightAt h k hs ks v r i:ZMod (prime h k r)))=
      HistoryPairKernelReplacement.rightRows h k hs ks r (prime h k r) (fun j => (v j:ZMod (prime h k r))) := by
  funext i
  exact (Expr.eval₂_cast_int _ v).symm

def actualUnitSquareProbabilityAt (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) : ℝ :=
  letI : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
  unitGoodProbability (prime h k r) Finset.univ (actualLeftAt h k hs ks v r) (actualRightAt h k hs ks v r)

def actualMixedSquareProbabilityAt (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) : ℝ :=
  letI : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
  mixedGoodProbability (prime h k r) Finset.univ (actualLeftAt h k hs ks v r) (actualRightAt h k hs ks v r)

def actualSquareIndicatorAt (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k)
    (z : ZMod ((prime h k r)^2)×ZMod ((prime h k r)^2)) : ℂ :=
  guardIndicator (Good (prime h k r) Finset.univ (actualLeftAt h k hs ks v r)
    (actualRightAt h k hs ks v r) (z.1.val:ℤ) (z.2.val:ℤ))

def actualUnitSquareIndicatorAt (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) (z : UnitPair ((prime h k r)^2)) : ℂ :=
  actualSquareIndicatorAt h k hs ks v r (z.1,z.2)

def actualMixedSquareIndicatorAt (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k→ℤ) (r : Representative h k) (z : MixedPair ((prime h k r)^2)) : ℂ :=
  actualSquareIndicatorAt h k hs ks v r (z.1,z.2)

lemma actualUnitSquareIndicatorAt_average (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (r : Representative h k) [NeZero ((prime h k r)^2)] :
    average (actualUnitSquareIndicatorAt h k hs ks v r)=(actualUnitSquareProbabilityAt h k hs ks v r:ℂ) := by
  unfold actualUnitSquareIndicatorAt actualSquareIndicatorAt actualUnitSquareProbabilityAt unitGoodProbability
  exact average_guardIndicator _

lemma actualMixedSquareIndicatorAt_average (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (r : Representative h k) [NeZero ((prime h k r)^2)] :
    average (actualMixedSquareIndicatorAt h k hs ks v r)=(actualMixedSquareProbabilityAt h k hs ks v r:ℂ) := by
  unfold actualMixedSquareIndicatorAt actualSquareIndicatorAt actualMixedSquareProbabilityAt mixedGoodProbability
  exact average_guardIndicator _

lemma unit_baseAt_eq_actualProbability (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (r : Representative h k) [Fact (prime h k r).Prime] :
    unitBaseProbability (prime h k r) Finset.univ (actualLeftAt h k hs ks v r) (actualRightAt h k hs ks v r)=
      HistoryPairKernelReplacement.actualProbability false h k hs ks r (prime h k r) v := by
  rw [unitBaseProbability_eq_lines,actualLeftAt_cast,actualRightAt_cast]
  simp only [HistoryPairKernelReplacement.actualProbability,representative_prime h k hs ks r,
    dite_eq_left,Bool.false_eq_true,ite_false]

lemma mixed_baseAt_eq_actualProbability (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (r : Representative h k) [Fact (prime h k r).Prime] :
    mixedBaseProbability (prime h k r) Finset.univ (actualLeftAt h k hs ks v r) (actualRightAt h k hs ks v r)=
      HistoryPairKernelReplacement.actualProbability true h k hs ks r (prime h k r) v := by
  rw [mixedBaseProbability_eq_lines,actualLeftAt_cast,actualRightAt_cast]
  simp only [HistoryPairKernelReplacement.actualProbability,representative_prime h k hs ks r,
    dite_eq_left,ite_true]

end Ostmann.Arithmetic.HistoryPairVariableBAverage

end

end OAI
