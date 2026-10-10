import OAI.NumberTheory.Jacobsthal.Primes.FrozenPrimeGroup

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualNearFullStopGroup
open FinitePathGeometry PrimeHistories SourceStopPredicate ActualSourceTags ActualBinOwners FiniteFirstTag
open StoppedCountVertex StoppedCountAdapters StoppedTraceSets ActualSourceStopBinding
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open ActualFrozenStopFamily FrozenPrimeGroup TagBelowStopWindow
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem actual_near_full_stop_group (Y : ℕ) (w top Cs eta Clen B xi b₀ b₁ mu : ℝ)
    (hw : 1 < w) (hwtop : w < top) (hxi : 0 < xi) (hC : 0 ≤ Clen)
    (hwindow : b₁ < w^((1/4:ℝ))) (a : ℕ → ℕ) (z : Node) (ps : List ℕ)
    (hs : ps ∈ stopped w
      (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
        (label (zero_lt_one.trans hw) hwtop hxi) a z)
      (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu)) :
    ∃ pre tail : List ℕ,∃ t : Tag (binCount w top xi),
      tail ≠ [] ∧ t.index=pre.length ∧ eligible (Y:ℝ) w Cs t.rational ∧
      ps ∈ frozenGroup (lower w top xi t.bin) (width w top xi t.bin) (sourceClass a) t.rational pre tail ∧
      frozenGroup (lower w top xi t.bin) (width w top xi t.bin) (sourceClass a) t.rational pre tail ⊆
        stopped w
          (stopCandidate Y w Cs eta Clen B xi b₀ b₁ (lower w top xi) (width w top xi)
            (label (zero_lt_one.trans hw) hwtop hxi) a z)
          (sourcePrimeSet w top).card (rootVertex z ∅ (sourcePrimeSet w top) mu) ∧
      (1-eta)*((primeBin (lower w top xi t.bin) (width w top xi t.bin)).card:ℝ) ≤
        (frozenGroup (lower w top xi t.bin) (width w top xi t.bin) (sourceClass a) t.rational pre tail).card := by
  let lo := lower w top xi
  let wi := width w top xi
  let lab := label (zero_lt_one.trans hw) hwtop hxi
  let P := sourcePrimeSet w top
  have hf := actual_source_stops_first Y w Cs eta Clen B xi b₀ b₁ mu lo wi lab a z P hs
  have hcand := hf.2.1
  obtain ⟨t,ht,_hcount,_halign⟩ := hcand.2.2.2.2.2
  obtain ⟨pre,p,tail,heq,hindex,hp,_hbefore⟩ := firstTagFrom_witness
    (tagCandidate (Y:ℝ) w Cs eta lo wi lab (sourceClass a)) 0 ps ht
  have hwit := candidate_witness (Y:ℝ) w Cs eta lo wi lab (sourceClass a) p hp
  have ho : owner (Y:ℝ) w Cs eta (lo t.bin) (wi t.bin) (sourceClass a)=some t.rational := by
    rw [hwit.1]
    exact hwit.2.2.2.1
  have howner := actual_owner_witness (Nat.cast_nonneg Y) hw (sourceClass a) ho
  have hmem : p ∈ primeBin (lo t.bin) (wi t.bin) := by rw [hwit.1]; exact hwit.2.1
  have htail : tail ≠ [] := source_tag_nonterminal Y w Cs eta Clen B xi b₀ b₁ lo wi lab a z pre tail p
    hw (fun i => endpoint_pos (zero_lt_one.trans hw) _) (fun i => (effectiveWidth_pos (zero_lt_one.trans hw) hwtop hxi).le)
    hwindow hp (by simpa only [heq] using hcand)
  refine ⟨pre,tail,t,htail,by simpa only [zero_add] using hindex,howner.1,?_,?_,?_⟩
  · exact (mem_frozenGroup _ _ _ _ _ _ ps).mpr ⟨p,hmem,hwit.2.2.2.2,heq⟩
  · intro qs hqs
    obtain ⟨p',hp',ha',rfl⟩ := (mem_frozenGroup _ _ _ _ _ _ qs).mp hqs
    subst ps
    exact actual_stopped_replacement Y w top Cs eta Clen B xi b₀ b₁ mu hw hwtop hxi hC a z pre tail p p'
      hs ht hp hp' ha'
  · exact frozenGroup_owner_card (Y:ℝ) w Cs eta (lo t.bin) (wi t.bin) (sourceClass a) t.rational pre tail
      (Nat.cast_nonneg Y) hw ho
end NumberTheoryLean.ActualNearFullStopGroup

end

end Erdos970

end OAI
