import Mathlib.Data.Finset.Option
import OAI.NumberTheory.Jacobsthal.Estimates.FrozenSuffixData

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CanonicalStopKey
open ActualSourceTags ActualTagFreezing FiniteFirstTag
open SourceStopPredicate ErdosInversePrimeBin ErdosInverseAlignment


structure Key (n : ℕ) where
  tag : Tag n
  pre : List ℕ
  tail : List ℕ
  deriving DecidableEq

noncomputable def stopKey {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) : Option (Key n) :=
  (sourceTag Y w Cs eta lower width label a ps).map
    (fun t => ⟨t,ps.take t.index,ps.drop (t.index+1)⟩)

theorem stopKey_of_tagged_word {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (pre tail : List ℕ) (p : ℕ) {t : Tag n}
    (ht : sourceTag Y w Cs eta lower width label a (pre++p::tail)=some t)
    (hi : t.index=pre.length) :
    stopKey Y w Cs eta lower width label a (pre++p::tail)=some ⟨t,pre,tail⟩ := by
  simp [stopKey,ht,hi,List.take_append,List.drop_append]

theorem stopKey_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {k : Key n}
    (hk : stopKey Y w Cs eta lower width label a ps=some k) :
    ∃ p : ℕ,ps=k.pre++p::k.tail ∧ k.tag.index=k.pre.length ∧
      sourceTag Y w Cs eta lower width label a ps=some k.tag ∧
      tagCandidate Y w Cs eta lower width label a p=some (k.tag.bin,k.tag.rational) := by
  cases ht : sourceTag Y w Cs eta lower width label a ps with
  | none => simp [stopKey,ht] at hk
  | some t =>
    obtain ⟨pre,p,tail,heq,hi,hp,_hbefore⟩ := firstTagFrom_witness
      (tagCandidate Y w Cs eta lower width label a) 0 ps ht
    have hi' : t.index=pre.length := by simpa only [zero_add] using hi
    have hkey : stopKey Y w Cs eta lower width label a ps=some ⟨t,pre,tail⟩ := by
      rw [heq]
      exact stopKey_of_tagged_word Y w Cs eta lower width label a pre tail p (by simpa only [heq] using ht) hi'
    have he : k=⟨t,pre,tail⟩ := Option.some.inj (hk.symm.trans hkey)
    subst k
    exact ⟨p,heq,hi',rfl,hp⟩

theorem stopKey_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {k : Key n}
    (hk : stopKey Y w Cs eta lower width label a ps=some k) (p' : ℕ)
    (hl : label p'=k.tag.bin)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p')))
    (ha' : aligns a k.tag.rational p') :
    stopKey Y w Cs eta lower width label a (k.pre++p'::k.tail)=some k := by
  obtain ⟨p,heq,hi,ht,hp⟩ := stopKey_witness Y w Cs eta lower width label a ps hk
  have hwit := candidate_witness Y w Cs eta lower width label a p hp
  have he := sourceTag_replacement Y w Cs eta lower width label a k.pre k.tail p p'
    hp (hl.trans hwit.1) hp' ha'
  have ht' : sourceTag Y w Cs eta lower width label a (k.pre++p'::k.tail)=some k.tag :=
    he.symm.trans (by simpa only [heq] using ht)
  have hh := stopKey_of_tagged_word Y w Cs eta lower width label a k.pre k.tail p' ht' hi
  exact hh
end NumberTheoryLean.CanonicalStopKey



namespace NumberTheoryLean.ActualStopGroupFiber
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags FiniteFirstTag CanonicalStopKey
open StoppedCountAdapters StoppedTraceSets ActualSourceStopBinding ActualFrozenStopFamily
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open FrozenPrimeGroup ErdosInversePrimeBin

attribute [local instance] Classical.propDecidable

noncomputable def family (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) : Finset (List ℕ) :=
  stopped w (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) a z) (sourcePrimeSet w top).card
    (rootVertex z ∅ (sourcePrimeSet w top) mu)

noncomputable def key (Y : ℕ) (w top Cs eta xi : ℝ) (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (a : ℕ → ℕ) (ps : List ℕ) : Option (Key (binCount w top xi)) :=
  stopKey (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps

noncomputable def keyGroup (w top xi : ℝ) (a : ℕ → ℕ) (k : Key (binCount w top xi)) :
    Finset (List ℕ) := frozenGroup (lower w top xi k.tag.bin) (width w top xi k.tag.bin)
      (sourceClass a) k.tag.rational k.pre k.tail

theorem key_some_of_mem (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hps : ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z) :
    ∃ k,key Y w top Cs eta xi hw htop hxi a ps=some k := by
  have hh := actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁ mu (lower w top xi)
    (width w top xi) (label (zero_lt_one.trans hw) htop hxi) a z (sourcePrimeSet w top) hps
  obtain ⟨t,ht,_hc,_ha⟩ := hh.2.1.2.2.2.2.2
  refine ⟨⟨t,ps.take t.index,ps.drop (t.index+1)⟩,?_⟩
  simp only [key,stopKey,ht,Option.map_some]

theorem key_mem_group (Y : ℕ) (w top Cs eta xi : ℝ) (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (a : ℕ → ℕ) (ps : List ℕ) {k : Key (binCount w top xi)}
    (hk : key Y w top Cs eta xi hw htop hxi a ps=some k) : ps ∈ keyGroup w top xi a k := by
  obtain ⟨p,heq,_hi,_ht,hp⟩ := stopKey_witness (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps hk
  have hc := candidate_witness (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) p hp
  apply (mem_frozenGroup _ _ _ _ _ _ ps).mpr
  refine ⟨p,?_,hc.2.2.2.2,heq⟩
  rw [hc.1]
  exact hc.2.1

theorem group_eq_fiber (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (a : ℕ → ℕ) (z : Node) (k : Key (binCount w top xi))
    (hpresent : ∃ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,
      key Y w top Cs eta xi hw htop hxi a ps=some k) :
    keyGroup w top xi a k=(family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z).filter
      (fun ps => key Y w top Cs eta xi hw htop hxi a ps=some k) := by
  obtain ⟨ps,hps,hk⟩ := hpresent
  obtain ⟨p,heq,hi,ht,hp⟩ := stopKey_witness (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps hk
  apply Finset.ext
  intro qs
  constructor
  · intro hqs
    obtain ⟨p',hp',ha',rfl⟩ := (mem_frozenGroup _ _ _ _ _ _ qs).mp hqs
    have hnew := (bin_mem_iff_label (zero_lt_one.trans hw) htop hxi k.tag.bin p').mp hp'
    have hown : p' ∈ primeBin (lower w top xi (label (zero_lt_one.trans hw) htop hxi p'))
        (width w top xi (label (zero_lt_one.trans hw) htop hxi p')) := by
      rw [hnew.2.2.2]
      exact hp'
    have hnewkey := stopKey_replacement (Y:ℝ) w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) ps hk p' hnew.2.2.2 hown ha'
    refine Finset.mem_filter.mpr ⟨?_,hnewkey⟩
    subst ps
    exact actual_stopped_replacement Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z
      k.pre k.tail p p' hps ht hp hp' ha'
  · intro hqs
    exact key_mem_group Y w top Cs eta xi hw htop hxi a qs (Finset.mem_filter.mp hqs).2
end NumberTheoryLean.ActualStopGroupFiber



namespace NumberTheoryLean.CanonicalStopPartition
open PrimeHistories CanonicalStopKey ActualStopGroupFiber

attribute [local instance] Classical.propDecidable

noncomputable def keys (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node) :
    Finset (Key (LogarithmicBinScale.binCount w top xi)) :=
  (family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z).biUnion
    (fun ps => (key Y w top Cs eta xi hw htop hxi a ps).toFinset)

theorem mem_keys (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (a : ℕ → ℕ) (z : Node)
    (k : Key (LogarithmicBinScale.binCount w top xi)) :
    k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z ↔
      ∃ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,
        key Y w top Cs eta xi hw htop hxi a ps=some k := by
  simp [keys]

theorem groups_disjoint (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen) (a : ℕ → ℕ) (z : Node)
    {k l : Key (LogarithmicBinScale.binCount w top xi)}
    (hk : k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z)
    (hl : l ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z) (hne : k ≠ l) :
    Disjoint (keyGroup w top xi a k) (keyGroup w top xi a l) := by
  rw [group_eq_fiber Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z k
    ((mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k).mp hk),
    group_eq_fiber Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z l
    ((mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ l).mp hl)]
  apply Finset.disjoint_left.mpr
  intro ps hps hps'
  exact hne (Option.some.inj ((Finset.mem_filter.mp hps).2.symm.trans (Finset.mem_filter.mp hps').2))

theorem groups_union (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen) (a : ℕ → ℕ) (z : Node) :
    (keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z).biUnion (keyGroup w top xi a)=
      family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z := by
  ext ps
  constructor
  · intro hps
    obtain ⟨k,hk,hmem⟩ := Finset.mem_biUnion.mp hps
    rw [group_eq_fiber Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z k
      ((mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k).mp hk)] at hmem
    exact (Finset.mem_filter.mp hmem).1
  · intro hps
    obtain ⟨k,hk⟩ := key_some_of_mem Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z ps hps
    exact Finset.mem_biUnion.mpr ⟨k,(mem_keys _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k).mpr ⟨ps,hps,hk⟩,
      key_mem_group Y w top Cs eta xi hw htop hxi a ps hk⟩

theorem sum_over_groups (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen) (a : ℕ → ℕ) (z : Node)
    (F : List ℕ → ℝ) :
    (∑ ps ∈ family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,F ps)=
      ∑ k ∈ keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z,∑ ps ∈ keyGroup w top xi a k,F ps := by
  rw [← groups_union Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z]
  apply Finset.sum_biUnion
  intro k hk l hl hne
  exact groups_disjoint Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi hC a z hk hl hne
end NumberTheoryLean.CanonicalStopPartition



namespace NumberTheoryLean.CanonicalKeyWitness
open PrimeHistories CanonicalStopKey CanonicalStopPartition ActualStopGroupFiber
open SourceStopPredicate ActualSourceTags ActualBinOwners ActualSourceStopBinding TagBelowStopWindow
open StoppedCountAdapters StoppedTraceSets StoppedTraceAdmission
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ErdosInversePrimeBin ErdosInverseAlignment ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

structure Witness {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ mu : ℝ) (a : ℕ → ℕ) (z : Node)
    (k : Key (binCount w top xi)) where
  p₀ : ℕ
  mem_family : k.pre++p₀::k.tail∈family Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z
  candidate : stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) a z (k.pre++p₀::k.tail)
  tag : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) (k.pre++p₀::k.tail)=some k.tag
  prime_tag : tagCandidate Y w Cs eta (lower w top xi) (width w top xi)
    (label (zero_lt_one.trans hw) htop hxi) (sourceClass a) p₀=some (k.tag.bin,k.tag.rational)
  index : k.tag.index=k.pre.length
  ordered : (k.pre++p₀::k.tail).Pairwise (· > ·)
  source : ∀ p∈k.pre++p₀::k.tail,p∈sourcePrimeSet w top
  singleton : ((k.pre++p₀::k.tail).map (label (zero_lt_one.trans hw) htop hxi)).count k.tag.bin=1
  eligible : ActualBinOwners.eligible Y w Cs k.tag.rational
  near_full : (1-eta)*((primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)).card:ℝ) ≤
    (((primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)).filter (aligns (sourceClass a) k.tag.rational)).card:ℝ)
  aligned : ∀ p∈k.pre++p₀::k.tail,aligns (sourceClass a) k.tag.rational p
  prime_bin : p₀∈primeBin (lower w top xi k.tag.bin) (width w top xi k.tag.bin)
  bin_eq : k.tag.bin=label (zero_lt_one.trans hw) htop hxi p₀
  search : searchBin w (lower w top xi k.tag.bin)
  owner : ActualBinOwners.owner Y w Cs eta (lower w top xi k.tag.bin) (width w top xi k.tag.bin) (sourceClass a)=some k.tag.rational
  tail_nonempty : k.tail≠[]

theorem key_witness_exists {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (Y : ℕ) (Cs eta Clen B b₀ b₁ mu : ℝ) (a : ℕ → ℕ) (z : Node)
    (hwindow : b₁ < w^((1/4:ℝ))) (k : Key (binCount w top xi))
    (hk : k∈keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z) :
    Nonempty (Witness hw htop hxi Y Cs eta Clen B b₀ b₁ mu a z k) := by
  obtain ⟨ps,hps,hkey⟩ := (mem_keys Y w top Cs eta Clen B xi b₀ b₁ mu hw htop hxi a z k).mp hk
  let lo := lower w top xi
  let wi := width w top xi
  let lab := label (zero_lt_one.trans hw) htop hxi
  let P := sourcePrimeSet w top
  let stop := stopCandidate Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z
  obtain ⟨p₀,heq,hindex,htag,hptag⟩ := stopKey_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) ps hkey
  have hstop := actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁ mu lo wi lab a z P hps
  have href := trace_reference_member w stop P.card (rootVertex z ∅ P mu) (Or.inr hps)
  have hd := mem_decreasingPrefixes.mp (Finset.mem_filter.mp href).1
  obtain ⟨t,ht,hsingle,helig,hnear,halign⟩ := candidate_owner_witness Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z ps hw hstop.2.1
  have he : t=k.tag := Option.some.inj (ht.symm.trans htag)
  subst t
  subst ps
  have hp := candidate_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) p₀ hptag
  have htail := source_tag_nonterminal (t:=k.tag) Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z k.pre k.tail p₀
    hw (fun b => endpoint_pos (zero_lt_one.trans hw) b.1)
    (fun _ => (effectiveWidth_pos (zero_lt_one.trans hw) htop hxi).le) hwindow hptag hstop.2.1
  refine ⟨{
    p₀ := p₀
    mem_family := hps
    candidate := hstop.2.1
    tag := htag
    prime_tag := hptag
    index := hindex
    ordered := hd.1
    source := hd.2
    singleton := hsingle
    eligible := helig
    near_full := hnear
    aligned := halign
    prime_bin := ?_
    bin_eq := hp.1
    search := ?_
    owner := ?_
    tail_nonempty := htail }⟩
  · simpa only [← hp.1] using hp.2.1
  · simpa only [← hp.1] using hp.2.2.1
  · simpa only [← hp.1] using hp.2.2.2.1
end NumberTheoryLean.CanonicalKeyWitness


end Erdos970

end OAI
