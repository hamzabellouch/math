import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalBands

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] {N : ℕ}
local instance classDomainPointDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance classDomainDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance classDomainDualDualDE : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _

def reversedMarkingDomain (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :=
  (markingDomain m i).map swapFlag.toEmbedding

omit [Finite K] in
lemma markingDomain_forward (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    markingDomain m i  ⊆  forwardDomain m i := Finset.inter_subset_left

omit [Finite K] in
lemma markingDomain_backward (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    reversedMarkingDomain m i  ⊆  backwardDomain m i := by
  intro z hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hz
  obtain ⟨y,hy,he⟩:=Finset.mem_map.mp (Finset.mem_inter.mp hx).2
  have hh : y=swapFlag x := by
    simpa only [Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using congrArg swapFlag he
  exact hh ▸ hy

lemma endpoint_card_mono {A B : Type*} [DecidableEq A] [DecidableEq B]
    {S T : Finset (A×B)} (h : S ⊆ T) :
    ((S.image Prod.fst).card:ℝ) ≤ (T.image Prod.fst).card ∧
    ((S.image Prod.snd).card:ℝ) ≤ (T.image Prod.snd).card := by
  constructor  <;> exact_mod_cast Finset.card_le_card (Finset.image_subset_image h)

omit [Finite K] in
lemma reversedDomain_first_card (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    ((reversedMarkingDomain m i).image Prod.fst).card=((markingDomain m i).image Prod.snd).card := by
  congr 1
  ext b
  simp only [reversedMarkingDomain,Finset.mem_image,Finset.mem_map]
  aesop

omit [Finite K] in
lemma reversedDomain_second_card (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N) :
    ((reversedMarkingDomain m i).image Prod.snd).card=((markingDomain m i).image Prod.fst).card := by
  have he : (reversedMarkingDomain m i).image Prod.snd=
      ((markingDomain m i).image Prod.fst).map bidualPoint.toEmbedding := by
    ext b
    simp only [reversedMarkingDomain,Finset.mem_image,Finset.mem_map]
    aesop
  rw [he,Finset.card_map]

def ForwardCaps (D : Finset (FlagPair K V)) (u : ℝ) : Prop :=
  ((D.image Prod.fst).card:ℝ) ≤ 32*Real.exp (5*Real.log (Nat.card K)-u) ∧
  ((D.image Prod.snd).card:ℝ) ≤ 32*Real.exp u

def ReverseCaps (D : Finset (FlagPair K V)) (u : ℝ) : Prop :=
  ((D.image Prod.snd).card:ℝ) ≤ 32*Real.exp (5*Real.log (Nat.card K)-u) ∧
  ((D.image Prod.fst).card:ℝ) ≤ 32*Real.exp u

lemma marking_poor_forward (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) (hp : (m.1 i).1.2.1=false) :
    ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ForwardCaps (markingDomain m i) u := by
  let W:=decodeState (finiteDecodeRecord (forwardRecord m)) i.val
  let r:=(m.1 i).1.1.1
  have hs : markingDomain m i ⊆ typedDomain W r false := by
    simpa only [forwardDomain,finiteTypedDomain,hp] using markingDomain_forward m i
  have ht:=(typed_poor_reciprocal hdim W r (hne.mono hs))
  let u:=clampParameter (Nat.card K) (levelSet W (chooseLevel W r.val)).card
  have hb:=clampParameter_bounds (M:=(levelSet W (chooseLevel W r.val)).card)
    (show (1:ℝ) ≤ Nat.card K by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
  exact ⟨u,hb.1,hb.2,(endpoint_card_mono hs).1.trans ht.1,
    (endpoint_card_mono hs).2.trans ht.2⟩

lemma marking_poor_backward (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) (hp : (m.1 i).1.2.2=false) :
    ∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ReverseCaps (markingDomain m i) u := by
  let W:=decodeState (finiteDecodeRecord (backwardRecord m)) i.rev.val
  let r:=(m.1 i).1.1.2
  have hs : reversedMarkingDomain m i ⊆ typedDomain W r false := by
    simpa only [backwardDomain,finiteTypedDomain,Fin.rev_rev,hp] using markingDomain_backward m i
  have ht:=(typed_poor_reciprocal (K:=K) (V:=Dual K V) (by simpa using hdim)
    W r (hne.map.mono hs))
  let u:=clampParameter (Nat.card K) (levelSet W (chooseLevel W r.val)).card
  have hb:=clampParameter_bounds (M:=(levelSet W (chooseLevel W r.val)).card)
    (show (1:ℝ) ≤ Nat.card K by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
  have hc:=endpoint_card_mono hs
  rw [reversedDomain_first_card,reversedDomain_second_card] at hc
  exact ⟨u,hb.1,hb.2,hc.1.trans ht.1,hc.2.trans ht.2⟩

lemma marking_popular_caps (_hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty)
    (hp : (m.1 i).1.2.1=true) (hp' : (m.1 i).1.2.2=true) :
    let r:=(m.1 i).1.1.1
    let s:=(m.1 i).1.1.2
    1 ≤ r.val ∧ 1 ≤ s.val ∧
      (((markingDomain m i).image Prod.fst).card:ℝ) ≤ 32*(Nat.card K:ℝ)^s.val ∧
      (((markingDomain m i).image Prod.snd).card:ℝ) ≤ 32*(Nat.card K:ℝ)^r.val := by
  let W:=decodeState (finiteDecodeRecord (forwardRecord m)) i.val
  let W':=decodeState (finiteDecodeRecord (backwardRecord m)) i.rev.val
  let r:=(m.1 i).1.1.1
  let s:=(m.1 i).1.1.2
  have hs : markingDomain m i ⊆ typedDomain W r true := by
    simpa only [forwardDomain,finiteTypedDomain,hp] using markingDomain_forward m i
  have hs' : reversedMarkingDomain m i ⊆ typedDomain W' s true := by
    simpa only [backwardDomain,finiteTypedDomain,Fin.rev_rev,hp'] using markingDomain_backward m i
  have hc':=(endpoint_card_mono hs').2.trans (typed_popular_second W' s)
  rw [reversedDomain_second_card] at hc'
  exact ⟨typed_popular_rank_pos W r (hne.mono hs),
    typed_popular_rank_pos W' s (hne.map.mono hs'),hc',
    (endpoint_card_mono hs).2.trans (typed_popular_second W r)⟩

lemma marking_popular_partners_first (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hp' : (m.1 i).1.2.2=true) :
    ∀ a,((Finset.univ.filter fun b=>(a,b)∈markingDomain m i).card:ℝ) ≤
      2*(Nat.card K:ℝ)^((4-(m.1 i).1.1.2.val):ℕ) := by
  intro a
  let W:=decodeState (finiteDecodeRecord (backwardRecord m)) i.rev.val
  let r:=(m.1 i).1.1.2
  have hs : reversedMarkingDomain m i ⊆ typedDomain W r true := by
    simpa only [backwardDomain,finiteTypedDomain,Fin.rev_rev,hp'] using markingDomain_backward m i
  have hc : (Finset.univ.filter fun b=>(a,b)∈markingDomain m i) ⊆
      (Finset.univ.filter fun b=>(b,bidualPoint a)∈typedDomain W r true) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs (Finset.mem_map.mpr
      ⟨(a,b),(Finset.mem_filter.mp hb).2,rfl⟩)⟩
  have hcard : ((Finset.univ.filter fun b=>(a,b)∈markingDomain m i).card:ℝ) ≤
      (Finset.univ.filter fun b=>(b,bidualPoint a)∈typedDomain W r true).card :=
    Nat.cast_le.mpr (Finset.card_le_card hc)
  have hpart := typed_popular_partner (K:=K) (V:=Dual K V)
    (by simpa only [Subspace.dual_finrank_eq] using hdim) W r (bidualPoint a)
  apply hcard.trans
  simpa only [r] using hpart

lemma marking_popular_partners_second (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hp : (m.1 i).1.2.1=true) :
    ∀ b,((Finset.univ.filter fun a=>(a,b)∈markingDomain m i).card:ℝ) ≤
      2*(Nat.card K:ℝ)^((4-(m.1 i).1.1.1.val):ℕ) := by
  intro b
  let W:=decodeState (finiteDecodeRecord (forwardRecord m)) i.val
  let r:=(m.1 i).1.1.1
  have hs : markingDomain m i ⊆ typedDomain W r true := by
    simpa only [forwardDomain,finiteTypedDomain,hp] using markingDomain_forward m i
  have hc : (Finset.univ.filter fun a=>(a,b)∈markingDomain m i) ⊆
      (Finset.univ.filter fun a=>(a,b)∈typedDomain W r true) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs (Finset.mem_filter.mp ha).2⟩
  have hcard : ((Finset.univ.filter fun a=>(a,b)∈markingDomain m i).card:ℝ) ≤
      (Finset.univ.filter fun a=>(a,b)∈typedDomain W r true).card :=
    Nat.cast_le.mpr (Finset.card_le_card hc)
  have hpart := typed_popular_partner (K:=K) (V:=V) hdim W r b
  apply hcard.trans
  simpa only [r] using hpart

theorem marking_domain_dichotomy (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) :
    (∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ForwardCaps (markingDomain m i) u) ∨
    (∃ u,Real.log (Nat.card K) ≤ u ∧ u ≤ 4*Real.log (Nat.card K) ∧
      ReverseCaps (markingDomain m i) u) ∨
    ((m.1 i).1.2.1=true ∧ (m.1 i).1.2.2=true ∧
      5 < (m.1 i).1.1.1.val+(m.1 i).1.1.2.val) := by
  cases hp:(m.1 i).1.2.1 with
  | false=>exact Or.inl (marking_poor_forward hdim m i hne hp)
  | true=>
    cases hp':(m.1 i).1.2.2 with
    | false=>exact Or.inr (Or.inl (marking_poor_backward hdim m i hne hp'))
    | true=>
      by_cases hh:5 < (m.1 i).1.1.1.val+(m.1 i).1.1.2.val
      · exact Or.inr (Or.inr ⟨rfl,rfl,hh⟩)
      · have hc:=marking_popular_caps hdim m i hne hp hp'
        have hr:=(m.1 i).1.1.1.isLt
        have he:=popular_reciprocal_caps
          (show (1:ℝ) ≤ Nat.card K by exact_mod_cast (Finite.one_lt_card (α:=K)).le)
          hc.1 (by omega) (by omega) hc.2.2.1 hc.2.2.2
        exact Or.inl ⟨_,he.1,he.2.1,he.2.2⟩
end
end SharpRamseyFive.Marking

end OAI
