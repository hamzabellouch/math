import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.WindowLevels
import OAI.Combinatorics.RamseyFive.Entropy.OrderedWindowVariation

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {w r : ℕ} [Nonempty (Fin r)]
local instance goodVarBDE : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance goodVarIDE : DecidableEq (Slots w r) := Classical.decEq _

omit [Nonempty (Fin r)] in
theorem reciprocal_large_window_count (hdim : finrank K V=5)
    (p : Law (Slots w r→FlagPair K V)) (u : Slots w r→ℝ)
    (sel : (Fin w×Bool)→Fin r) (s d ε k lo hi : ℝ) (G : Finset (Fin w))
    (W : ReciprocalWindows p u sel (fun i : G=>i.val) s)
    (hcons : ∀x,0<p x→∀i j,slotEmbedding i<slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hgood : ∀i∈G,indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (earlySlot sel i)=0 ∧
      indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w r) u s) sel (lateSlot sel i)=0)
    (hu : ∀i,lo≤u i ∧ u i≤hi) (hlohi : lo≤hi) (hc : 0≤2*s+Real.log 64) (hk : 0<k)
    (hsmall : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    ((G.filter fun i=>k<u (earlySlot sel i)-u (lateSlot sel i)).card:ℝ)≤
      (hi-lo+2*(G.card:ℝ)*(2*s+Real.log 64))/k := by
  apply good_large_window_count G (fun i=>u (earlySlot sel i)) (fun i=>u (lateSlot sel i))
    lo hi (2*s+Real.log 64) k hc hk hlohi (fun i _=>(hu _).2) (fun i _=>(hu _).1)
  · intro i hi
    rw [←add_assoc]
    apply ordered_good_u_monotone hdim p (slotEquiv w r) u s ε hcons
      (earlySlot sel i) (lateSlot sel i) (early_late_le sel i i le_rfl)
      (W.early ⟨i,hi⟩) (W.late ⟨i,hi⟩) _ hsmall
    exact (good_index_scores _ d ε p _ (fun _ _=>orderedCollision_nonneg ..)
      sel _ (hgood i hi).1).2 (i,true) (by simp [OtherBlock,earlySlot])
  · intro i hi j hj hij
    rw [←add_assoc]
    apply ordered_good_u_monotone hdim p (slotEquiv w r) u s ε hcons
      (lateSlot sel i) (earlySlot sel j) (ordered_windows _ _ hij)
      (W.late ⟨i,hi⟩) (W.early ⟨j,hj⟩) _ hsmall
    exact (good_index_scores _ d ε p _ (fun _ _=>orderedCollision_nonneg ..)
      sel _ (hgood i hi).2).2 (j,false) (by simp [OtherBlock,lateSlot])
end
end SharpRamseyFive.Marking

end OAI
