import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.WindowDeletionCount
import OAI.Combinatorics.RamseyFive.Marking.GoodWindowVariation
import OAI.Combinatorics.RamseyFive.Entropy.GoodIndexThreshold

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows PivotTree
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {w n : ℕ} [Nonempty (Fin n)]
local instance wfcIDE : DecidableEq (Slots w n) := Classical.decEq _
local instance wfcBDE : DecidableEq (Fin w×Bool) := Classical.decEq _

structure ReciprocalCaps (p : Law (I→FlagPair K V)) (u : I→ℝ) (C : ℝ) : Prop where
  incident : ∀x,0<p x→∀i,Incident (x i).1 (x i).2
  first : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i)
  second : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i)
  flag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C*(Nat.card K:ℝ)^4

omit [Finite K] [FiniteDimensional K V] [Nonempty (Fin n)] in
lemma goodWindow_scores {p : Law (Slots w n→FlagPair K V)} {u : Slots w n→ℝ}
    {sel : Fin w×Bool→Fin n} {J d ε s : ℝ} (hJ : 4*Real.log (Nat.card K)≤J)
    {v : Fin w} (hv : v∈goodWindowSet
      (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel) :
    indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w n) u s) sel
      (earlySlot sel v)=0 ∧
    indexBad (4*Real.log (Nat.card K)) d ε p (orderedCollision p (slotEquiv w n) u s) sel
      (lateSlot sel v)=0 := by
  have hg := (mem_goodWindowSet _ _ _).mp hv
  exact ⟨indexBad_of_larger_cap hJ _ _ _ _ (hg false),indexBad_of_larger_cap hJ _ _ _ _ (hg true)⟩

variable (hdim : finrank K V=5) (p : Law (Slots w n→FlagPair K V))
  (u : Slots w n→ℝ) (sel : Fin w×Bool→Fin n) (J d ε s C : ℝ)
  (hcap : ReciprocalCaps p u C) (hs : 0<s) (hJ : 4*Real.log (Nat.card K)≤J)
  (hmass : reciprocalBadMass s d C≤1/2)
  (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
    2*Real.exp 1*reciprocalBadMass s d C≤1/2)

include hdim hcap hs hJ hmass hsmall

omit [Nonempty (Fin n)] in
theorem goodWindows_exist {A : Type} [Fintype A] (e : A→Fin w)
    (he : ∀i,e i∈goodWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel) :
    Nonempty (ReciprocalWindows p u sel e s) :=
  reciprocal_windows_exist hdim p u sel e s d ε C hs hcap.incident hcap.first hcap.second hcap.flag
    (fun i=>goodWindow_scores hJ (he i)) hmass hsmall

omit [Nonempty (Fin n)] in
theorem survivingWindows_exist (k : ℝ)
    (hE : (survivingWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel)
      sel (fun v=>u (earlySlot sel v)-u (lateSlot sel v)) k).Nonempty) :
    Nonempty (ReciprocalWindows p u sel
      (survivingOriginal (survivingWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel)
        sel (fun v=>u (earlySlot sel v)-u (lateSlot sel v)) k) hE) s) := by
  apply goodWindows_exist hdim p u sel J d ε s C hcap hs hJ hmass hsmall
  intro i
  have hi:=survivingOriginal_mem _ hE i
  exact (Finset.mem_filter.mp hi).1

omit [Nonempty (Fin n)] in
theorem goodWindows_drop_bound (k lo hi : ℝ)
    (hcons : ∀x,0<p x→∀i j,slotEmbedding i<slotEmbedding j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hu : ∀i,lo≤u i ∧ u i≤hi) (hlohi : lo≤hi) (hc : 0≤2*s+Real.log 64) (hk : 0<k)
    (hε : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    (((goodWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel).filter
      fun v=>k<u (earlySlot sel v)-u (lateSlot sel v)).card:ℝ)≤
      (hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k := by
  let G:=goodWindowSet (indexBad J d ε p (orderedCollision p (slotEquiv w n) u s) sel) sel
  let W:=Classical.choice (goodWindows_exist hdim p u sel J d ε s C hcap hs hJ hmass hsmall
    (fun i : G=>i.val) (fun i=>i.property))
  have h:=reciprocal_large_window_count hdim p u sel s d ε k lo hi G W hcons
    (fun _ h=>goodWindow_scores hJ h) hu hlohi hc hk hε
  apply h.trans
  gcongr
  exact_mod_cast (show G.card≤w from (Finset.card_le_univ G).trans_eq (Fintype.card_fin w))
end
end SharpRamseyFive.Marking

end OAI
