import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.MarkingClassDomains

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
local instance dtPDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance dtDDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance dtDDDE : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _

def swapDomain (D : Finset (FlagPair K V)) := D.map swapFlag.toEmbedding

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
@[simp] lemma mem_swapDomain_iff (D : Finset (FlagPair K V)) (z : FlagPair K V) :
    swapFlag z∈swapDomain D ↔ z∈D := by
  simp only [swapDomain,Finset.mem_map,Equiv.toEmbedding_apply,EmbeddingLike.apply_eq_iff_eq]
  simp

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma swapDomain_first_card (D : Finset (FlagPair K V)) :
    ((swapDomain D).image Prod.fst).card=(D.image Prod.snd).card := by
  congr 1
  ext b
  simp only [swapDomain,Finset.mem_image,Finset.mem_map]
  aesop

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma swapDomain_second_card (D : Finset (FlagPair K V)) :
    ((swapDomain D).image Prod.snd).card=(D.image Prod.fst).card := by
  have he : (swapDomain D).image Prod.snd=(D.image Prod.fst).map bidualPoint.toEmbedding := by
    ext b
    simp only [swapDomain,Finset.mem_image,Finset.mem_map]
    aesop
  rw [he,Finset.card_map]

omit [Fintype (ℙ K (Dual K V))] in
lemma swapDomain_first_partners (D : Finset (FlagPair K V)) (b : ℙ K (Dual K V)) :
    (Finset.univ.filter fun c=>(b,c)∈swapDomain D).card=
      (Finset.univ.filter fun a=>(a,b)∈D).card := by
  apply Eq.symm
  apply Finset.card_equiv bidualPoint
  intro a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact (mem_swapDomain_iff D (a,b)).symm

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma swapDomain_second_partners (D : Finset (FlagPair K V)) (c : ℙ K (Dual K (Dual K V))) :
    (Finset.univ.filter fun b=>(b,c)∈swapDomain D).card=
      (Finset.univ.filter fun b=>(bidualPoint.symm c,b)∈D).card := by
  congr 1
  ext b
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hh:=mem_swapDomain_iff D (bidualPoint.symm c,b)
  simpa only [swapFlag_apply,Equiv.apply_symm_apply] using hh

omit [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] in
lemma ReverseCaps.swap {D : Finset (FlagPair K V)} {u : ℝ} (h : ReverseCaps D u) :
    ForwardCaps (swapDomain D) u := by
  simpa only [ForwardCaps,ReverseCaps,swapDomain_first_card,swapDomain_second_card] using h

structure HighCaps (D : Finset (FlagPair K V)) (r r' : ℕ) : Prop where
  flag : (D.card:ℝ)≤153*(Nat.card K:ℝ)^4
  first : ((D.image Prod.fst).card:ℝ)≤32*(Nat.card K:ℝ)^r'
  second : ((D.image Prod.snd).card:ℝ)≤32*(Nat.card K:ℝ)^r
  firstPartners : ∀a,((Finset.univ.filter fun b=>(a,b)∈D).card:ℝ)≤2*(Nat.card K:ℝ)^(4-r')
  secondPartners : ∀b,((Finset.univ.filter fun a=>(a,b)∈D).card:ℝ)≤2*(Nat.card K:ℝ)^(4-r)

lemma HighCaps.swap {D : Finset (FlagPair K V)} {r r' : ℕ} (h : HighCaps D r r') :
    HighCaps (swapDomain D) r' r := by
  constructor
  · simpa only [swapDomain,Finset.card_map] using h.flag
  · simpa only [swapDomain_first_card] using h.second
  · simpa only [swapDomain_second_card] using h.first
  · intro b
    simpa only [swapDomain_first_partners] using h.secondPartners b
  · intro c
    simpa only [swapDomain_second_partners] using h.firstPartners (bidualPoint.symm c)

variable [Finite K] {N : ℕ}
lemma marking_highCaps (hd : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty)
    (hp : (m.1 i).1.2.1=true) (hp' : (m.1 i).1.2.2=true) :
    HighCaps (markingDomain m i) (m.1 i).1.1.1.val (m.1 i).1.1.2.val := by
  have hh:=marking_popular_caps hd m i hne hp hp'
  exact ⟨markingDomain_card hd m i,hh.2.2.1,hh.2.2.2,
    marking_popular_partners_first hd m i hp',marking_popular_partners_second hd m i hp⟩
end
end SharpRamseyFive.Marking

end OAI
