import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.PreparedWindows
import OAI.Combinatorics.RamseyFive.Marking.OrderedHighConflict

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype κ] {w n : ℕ} [Nonempty (Fin n)]
local instance hcrBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance hcrTDE : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
local instance hcrIDE : DecidableEq (Slots w n) := Classical.decEq _
omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma orderedHigh_collision_subset (p : Law (Slots w n→FlagPair K V)) (s : ℝ)
    (U : Finset (Slots w n)) :
    (∑i∈U,∑j∈U,orderedHighCollision p (slotEquiv w n) s i j)≤
      ∑i,∑j,orderedHighCollision p (slotEquiv w n) s i j := by
  apply (Finset.sum_le_sum (fun i _=>Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ U) (fun j _ _=>orderedHighCollision_nonneg p _ s i j))).trans
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
    (fun i _ _=>Finset.sum_nonneg (fun j _=>orderedHighCollision_nonneg p _ s i j))

theorem exists_high_three_round (hd : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (elig : κ→Fin w×Bool→Finset (Fin n)) (rounds rem : ℕ)
    (hrounds : 0<rounds) (hrem : 0<rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(elig a b).card)
    (J d ε budget s M : ℝ) (hdpos : 0<d) (hε : 0<ε)
    (D : κ→Slots w n→Finset (FlagPair K V)) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (elig a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (elig a)) J)≤budget)
    (hs : 2 ≤ s) (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
    (hinc : ∀a,0<μ a→∀x,0<p a x→∀i,Incident (x i).1 (x i).2)
    (hocc : ∀a,0<μ a→∀x,0<p a x→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∃i : Fin rounds,mean (preRoundLaw μ p elig i.val) (fun z=>
      ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
        preRoundBad μ p elig i.val J d ε
          (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w n) s) z j)≤
      budget/d+(2*budget/rounds+(4*(w*(4*n):ℝ)*M)/rem)/ε := by
  apply exists_small_deletion_round μ p elig rounds rem hrounds hrem hS J d ε budget
    (4*(w*(4*n):ℝ)*M) hdpos hε D hJ hp hfix hbudget
    (fun i a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w n) s)
  · intro i a h x y
    exact orderedHighCollision_nonneg _ _ _ _ _
  · intro i a ha h hh
    apply (orderedHigh_collision_subset _ s _).trans
    have hn : ((w*(4*n):ℕ):ℝ)=w*(4*n) := by push_cast;rfl
    rw [←hn]
    apply orderedHigh_collision_budget hd _ _ s M hs hsmall
    · intro x hx j
      exact hinc a ha x (history_support (p a) i.val h x hx) j
    · intro x hx W
      exact hocc a ha x (history_support (p a) i.val h x hx) W
end
end SharpRamseyFive.Marking

end OAI
