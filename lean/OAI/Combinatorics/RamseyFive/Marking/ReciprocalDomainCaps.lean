import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.AllHistoryWindowLoss
import OAI.Combinatorics.RamseyFive.Marking.MarkingClassDomains
import OAI.Combinatorics.RamseyFive.Marking.WindowCaps
import OAI.Combinatorics.RamseyFive.Entropy.History

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module ProjectiveIncidence FiniteEntropy Windows
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I]

omit [Finite K] [FiniteDimensional K V] in
lemma endpoint_support_domains (p : Law (I→FlagPair K V)) (D : I→Finset (FlagPair K V))
    (hp : InDomains p D) (i : I) :
    support (FiniteEntropy.first (map p (fun x=>x i)))⊆(D i).image Prod.fst ∧
    support (FiniteEntropy.second (map p (fun x=>x i)))⊆(D i).image Prod.snd := by
  constructor
  · intro a ha
    obtain ⟨z,hz,rfl⟩:=map_positive (map p (fun x=>x i)) Prod.fst a (by simpa only [map_fst] using (mem_support _ _).mp ha)
    exact Finset.mem_image.mpr ⟨z,marginal_support_subset p D hp i ((mem_support _ _).mpr hz),rfl⟩
  · intro a ha
    obtain ⟨z,hz,rfl⟩:=map_positive (map p (fun x=>x i)) Prod.snd a (by simpa only [map_snd] using (mem_support _ _).mp ha)
    exact Finset.mem_image.mpr ⟨z,marginal_support_subset p D hp i ((mem_support _ _).mpr hz),rfl⟩

omit [Finite K] [FiniteDimensional K V] in
lemma ReciprocalCaps.of_domains (p : Law (I→FlagPair K V)) (D : I→Finset (FlagPair K V))
    (u : I→ℝ) (C : ℝ) (hp : InDomains p D)
    (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
    (hcap : ∀i,ForwardCaps (D i) (u i))
    (hflag : ∀i,((D i).card:ℝ)≤C*(Nat.card K:ℝ)^4) : ReciprocalCaps p u C := by
  refine ⟨hinc,?_,?_,?_⟩
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (endpoint_support_domains p D hp i).1)).trans (hcap i).1
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (endpoint_support_domains p D hp i).2)).trans (hcap i).2
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (marginal_support_subset p D hp i))).trans (hflag i)

lemma support_map_mono {α β : Type} [Fintype α] [Fintype β]
    (p r : Law α) (f : α→β) (h : ∀x,0<r x→0<p x) :
    support (map r f)⊆support (map p f) := by
  intro b hb
  obtain ⟨x,hx,rfl⟩:=map_positive r f b ((mem_support _ _).mp hb)
  apply (mem_support _ _).mpr
  apply (h x hx).trans_le
  change p x≤∑y,if f y=f x then p y else 0
  have ht:=Finset.single_le_sum (s:=Finset.univ) (a:=x)
    (f:=fun y=>if f y=f x then p y else 0)
    (fun y _=>by split_ifs;exact p.nonneg _;rfl) (Finset.mem_univ x)
  simpa only [ite_true] using ht

variable {B A T : Type} [Fintype B] [Fintype A] [Fintype T] [Nonempty A]
local instance reciprocalHistoryDE : DecidableEq ((B×A)⊕T) := Classical.decEq _

omit [Finite K] [FiniteDimensional K V] [Nonempty A] in
lemma ReciprocalCaps.history
    (p : Law (((B×A)⊕T)→FlagPair K V)) (u : ((B×A)⊕T)→ℝ) (C : ℝ)
    (h : ReciprocalCaps (K:=K) (V:=V) p u C) (steps : ℕ) (z : BlockHistory B A T (FlagPair K V) steps) :
    ReciprocalCaps (K:=K) (V:=V) (historyPosterior p z) u C := by
  have hp : ∀x,0<historyPosterior p z x→0<p x := history_support p steps z
  have hfm (i) : support (FiniteEntropy.first (map (historyPosterior p z) (fun x=>x i)))⊆
      support (FiniteEntropy.first (map p (fun x=>x i))) := by
    rw [←map_fst,←map_fst,map_comp,map_comp]
    exact support_map_mono p (historyPosterior p z) _ hp
  have hsm (i) : support (FiniteEntropy.second (map (historyPosterior p z) (fun x=>x i)))⊆
      support (FiniteEntropy.second (map p (fun x=>x i))) := by
    rw [←map_snd,←map_snd,map_comp,map_comp]
    exact support_map_mono p (historyPosterior p z) _ hp
  refine ⟨fun x hx=>h.incident x (hp x hx),?_,?_,?_⟩
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (hfm i))).trans (h.first i)
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card (hsm i))).trans (h.second i)
  · intro i
    exact (Nat.cast_le.mpr (Finset.card_le_card
      (support_map_mono p (historyPosterior p z) (fun x=>x i) hp))).trans (h.flag i)
end
end

open Module ProjectiveIncidence FiniteEntropy Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
local instance histWinBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance histWinIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype κ]
  {w n steps : ℕ} [Nonempty (Fin n)]

def historyCollision (p : κ→Law (Slots w n→FlagPair K V)) (u : κ→Slots w n→ℝ) (s : ℝ)
    (a : κ) (h : BlockHistory (Fin w×Bool) (Fin n) (Fin w×Fin (2*n)) (FlagPair K V) steps) :=
  orderedCollision (historyPosterior (p a) h) (slotEquiv w n) (u a) s

def actualWindowSet (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (u : κ→Slots w n→ℝ) (J d ε s k : ℝ) (z : WindowHistory κ K V w n steps) : Finset (Fin w) :=
  if 0<μ z.1.1 then survivingWindowSet
    (indexBad J d ε (windowPosterior p z) (historyCollision p u s z.1.1 z.1.2) z.2)
    z.2 (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k else ∅

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma actualWindowSet_eq (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (S : κ→(Fin w×Bool)→Finset (Fin n)) (u : κ→Slots w n→ℝ) (J d ε s k : ℝ)
    (z : WindowHistory κ K V w n steps) (hz : 0<preRoundLaw μ p S steps z) :
    actualWindowSet μ p u J d ε s k z=survivingWindowSet
      (preRoundBad μ p S steps J d ε (historyCollision p u s) z) z.2
      (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k := by
  rw [actualWindowSet,ite_eq_left (preRound_positive μ p S steps z hz).1]
  rfl

def actualWindows (hdim : finrank K V=5) (μ : Law κ)
    (p : κ→Law (Slots w n→FlagPair K V)) (u : κ→Slots w n→ℝ) (J d ε s k C : ℝ)
    (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C)
    (hs : 0<s) (hJ : 4*Real.log (Nat.card K)≤J)
    (hmass : reciprocalBadMass s d C≤1/2)
    (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C≤1/2)
    (z : WindowHistory κ K V w n steps) (hE : (actualWindowSet μ p u J d ε s k z).Nonempty) :
    ReciprocalWindows (windowPosterior p z) (u z.1.1) z.2
      (survivingOriginal (actualWindowSet μ p u J d ε s k z) hE) s := by
  have ha : 0<μ z.1.1 := by
    by_contra h
    simp only [actualWindowSet,ite_eq_right h,Finset.not_nonempty_empty] at hE
  generalize hset : actualWindowSet μ p u J d ε s k z=E at hE ⊢
  have hsame : E=survivingWindowSet
      (indexBad J d ε (windowPosterior p z) (historyCollision p u s z.1.1 z.1.2) z.2)
      z.2 (fun v=>u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)) k := by
    rw [←hset,actualWindowSet,ite_eq_left ha]
  cases hsame
  exact Classical.choice (survivingWindows_exist hdim (windowPosterior p z) (u z.1.1) z.2
    J d ε s C ((hcap z.1.1 ha).history _ _ _ steps z.1.2) hs hJ hmass hsmall k hE)

omit [Fintype (ℙ K (Dual K (Dual K V)))] in
theorem actualWindows_drop_mean (hdim : finrank K V=5) (μ : Law κ)
    (p : κ→Law (Slots w n→FlagPair K V)) (S : κ→(Fin w×Bool)→Finset (Fin n))
    (u : κ→Slots w n→ℝ) (J d ε s k C lo hi : ℝ)
    (hcap : ∀a,0<μ a→ReciprocalCaps (p a) (u a) C)
    (hs : 0<s) (hJ : 4*Real.log (Nat.card K)≤J)
    (hmass : reciprocalBadMass s d C≤1/2)
    (hsmall : 2*(d+Real.log 32+Real.log 33+2*(Real.log (5*Real.log (Nat.card K)+1)+1))/s+
      2*Real.exp 1*reciprocalBadMass s d C≤1/2)
    (hcons : ∀a,0<μ a→∀x,0<p a x→∀i j,slotEmbedding i<slotEmbedding j→
      Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (hu : ∀a,0<μ a→∀i,lo≤u a i ∧ u a i≤hi) (hlohi : lo≤hi)
    (hc : 0≤2*s+Real.log 64) (hk : 0<k)
    (hε : ((4*Real.exp 1)^2*80004)*ε≤1/(4*(Nat.card K:ℝ))) :
    mean (preRoundLaw μ p S steps) (fun z=>
      (((goodWindowSet (preRoundBad μ p S steps J d ε (historyCollision p u s) z) z.2).filter
        fun v=>k<u z.1.1 (earlySlot z.2 v)-u z.1.1 (lateSlot z.2 v)).card:ℝ))≤
      (hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k := by
  rw [←mean_const (preRoundLaw μ p S steps) ((hi-lo+2*(w:ℝ)*(2*s+Real.log 64))/k)]
  apply mean_mono_pos
  intro z hz
  have ha:=(preRound_positive μ p S steps z hz).1
  exact goodWindows_drop_bound hdim (windowPosterior p z) (u z.1.1) z.2 J d ε s C
    ((hcap z.1.1 ha).history _ _ _ steps z.1.2) hs hJ hmass hsmall k lo hi
    (fun x hx=>hcons z.1.1 ha x (history_support (p z.1.1) steps z.1.2 x hx))
    (hu z.1.1 ha) hlohi hc hk hε
end

end SharpRamseyFive.Marking

end OAI
