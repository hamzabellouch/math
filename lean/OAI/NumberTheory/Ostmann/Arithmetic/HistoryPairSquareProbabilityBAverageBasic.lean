import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationRepresentatives
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSquareProbability
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlocks

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairSquareProbability
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryCRTIntegration HistorySignedResidueFactorization ResidueHaar
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

lemma guardIndicator_forall {ι : Type*} [Fintype ι] (P : ι→Prop) :
    guardIndicator (∀i,P i)=∏i,guardIndicator (P i) := by
  by_cases hh : ∀i,P i
  · simp [guardIndicator,hh]
  · obtain ⟨i,hi⟩ := not_forall.mp hh
    rw [guardIndicator,ite_eq_right hh]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [guardIndicator,hi])).symm

lemma average_guardIndicator {α : Type*} [Fintype α] (P : α→Prop) :
    average (fun x => guardIndicator (P x))=(probability P:ℂ) := by
  simp [average,guardIndicator,probability,div_eq_mul_inv,mul_comm]

def actualSquareIndicator (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (z : ZMod ((prime h k r)^2)×ZMod ((prime h k r)^2)) : ℂ :=
  guardIndicator (Good (prime h k r) Finset.univ (actualLeft h k hs ks r)
    (actualRight h k hs ks r) (z.1.val:ℤ) (z.2.val:ℤ))

def actualUnitSquareIndicator (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (z : UnitPair ((prime h k r)^2)) : ℂ :=
  actualSquareIndicator h k hs ks r (z.1,z.2)

def actualMixedSquareIndicator (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (r : Representative h k) (z : MixedPair ((prime h k r)^2)) : ℂ :=
  actualSquareIndicator h k hs ks r (z.1,z.2)

theorem primeResidueIndicatorB_eq_projected_product (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (z : ZMod (representativeModulus h k)×ZMod (representativeModulus h k)) :
    primeResidueIndicatorB h k hs ks z=∏r : Representative h k,
      actualSquareIndicator h k hs ks r
        (representativeSquareProjectionB h k r z.1,representativeSquareProjectionB h k r z.2) := by
  unfold primeResidueIndicatorB actualSquareIndicator
  rw [propext (finiteB_iff_projected_fiber_good h k hs ks z),guardIndicator_forall]

lemma actualUnitSquareIndicator_average (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k)
    [NeZero ((prime h k r)^2)] :
    average (actualUnitSquareIndicator h k hs ks r)=(actualUnitSquareProbability h k hs ks r:ℂ) := by
  unfold actualUnitSquareIndicator actualSquareIndicator actualUnitSquareProbability unitGoodProbability
  exact average_guardIndicator _

lemma actualMixedSquareIndicator_average (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (r : Representative h k)
    [NeZero ((prime h k r)^2)] :
    average (actualMixedSquareIndicator h k hs ks r)=(actualMixedSquareProbability h k hs ks r:ℂ) := by
  unfold actualMixedSquareIndicator actualSquareIndicator actualMixedSquareProbability mixedGoodProbability
  exact average_guardIndicator _

end Ostmann.Arithmetic.HistoryPairSquareProbability

end

end OAI
