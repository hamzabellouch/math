import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementNonzero
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceCoordinatesBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationAncestors
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelReplacement
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryPairPattern HistoryPairRows HistoryPairRepresentatives HistoryPairRepresentativeVariables
open HistoryRepresentativeSourceSeparation
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def smallSlotAt (h : History l) : Fin h.root.small.length ⊕ InternalKey h → SmallSlot :=
  Sum.elim h.root.small.get (internalSlot h)

def resampledSlot (q : SmallSlot) (n : ℕ) : SmallSlot := {q with value:=n}

def SmallSourceSamples (sources : SourceFamily) (h k : History l)
    (x : PairKey h k → ℤ) : Prop :=
  (∀i : Fin h.root.small.length ⊕ InternalKey h,∃n : ℕ,
    x (leftMap h k (.inr i))=(n:ℤ) ∧ sourceMass sources (resampledSlot (smallSlotAt h i) n)≠0) ∧
  (∀i : Fin k.root.small.length ⊕ InternalKey k,∃n : ℕ,
    x (rightMap h k (.inr i))=(n:ℤ) ∧ sourceMass sources (resampledSlot (smallSlotAt k i) n)≠0)

theorem resampledSlot_prime {sources : SourceFamily} {q : SmallSlot} {n : ℕ}
    (h : sourceMass sources (resampledSlot q n)≠0) : n.Prime := by
  unfold sourceMass at h
  split_ifs at h with hn
  · exact (sources q.origin).prime n hn
  · exact (h rfl).elim

variable {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}

theorem ancestor_sources_disjoint (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (hs : h.Supported V outside) (i : InternalKey h)
    (a : Fin h.root.small.length ⊕ InternalKey h)
    (ha : internalLevel h i < keyLevel h (.inr a)) :
    (C.sources (internalSlot h i).origin).DisjointMass (C.sources (smallSlotAt h a).origin) := by
  refine source_disjoint_of_comp C hsep (r:=sourceOfSlot (smallSlotAt h a))
    (internalSlot_source_mem _ h hh i) ?_
    (internalSlot_role h hs i) ?_
  · rcases a with a | a
    · exact rootSlot_source_mem _ h hh a
    · exact internalSlot_source_mem _ h hh a
  · change (smallSlotAt h a).role≠(internalSlot h i).role
    rw [internalSlot_role h hs i]
    rcases a with a | a
    · intro he
      have ht := History.supported_template hs _ (List.get_mem _ a) _ he
      have hi := internalLevel_pos_le h i
      omega
    · change (internalSlot h a).role≠_
      rw [internalSlot_role h hs a]
      intro he
      have he' := SlotRole.compensation.inj he
      change internalLevel h i < internalLevel h a at ha
      omega

theorem new_sample_ancestor_units (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples C.sources h k x)
    (i : Occurrences h k) (p : ℕ) (hp : p.Prime)
    (hi : x (representativeMap h k (label h k i))=(p:ℤ)) :
    AncestorUnits h k (fun a=>(x a:ZMod p)) i := by
  rcases i with i | i
  · obtain ⟨n,hn,hm⟩ := hx.1 (.inr i)
    have hnp : n=p := by exact_mod_cast hn.symm.trans hi
    subst n
    intro a ha
    obtain ⟨q,hq,hqm⟩ := hx.1 a
    change (x (leftMap h k (.inr a)):ZMod p)≠0
    rw [hq,Int.cast_natCast]
    apply natCast_nonzero_of_prime_ne hp (resampledSlot_prime hqm)
    exact sourceMass_ne_of_disjoint
      (q:=resampledSlot (internalSlot h i) p) (r:=resampledSlot (smallSlotAt h a) q)
      (ancestor_sources_disjoint C hsep h hh hs i a ha) hm hqm
  · obtain ⟨n,hn,hm⟩ := hx.2 (.inr i)
    have hnp : n=p := by exact_mod_cast hn.symm.trans hi
    subst n
    intro a ha
    obtain ⟨q,hq,hqm⟩ := hx.2 a
    change (x (rightMap h k (.inr a)):ZMod p)≠0
    rw [hq,Int.cast_natCast]
    apply natCast_nonzero_of_prime_ne hp (resampledSlot_prime hqm)
    exact sourceMass_ne_of_disjoint
      (q:=resampledSlot (internalSlot k i) p) (r:=resampledSlot (smallSlotAt k a) q)
      (ancestor_sources_disjoint C hsep k kh ks i a ha) hm hqm

theorem new_sample_frequency_bound (sources : SourceFamily) (h k : History l)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples sources h k x)
    (r : Representative h k) (p : ℕ) (hp : x (representativeMap h k r)=(p:ℤ))
    (hV : ∀j ≤ l,∀origin,(sources origin).AboveFrequency (V j)) :
    ∀j ≤ l,V j < p := by
  obtain ⟨i,rfl⟩ := label_surjective h k r
  rcases i with i | i
  · obtain ⟨n,hn,hm⟩ := hx.1 (.inr i)
    have hnp : n=p := by exact_mod_cast hn.symm.trans hp
    subst n
    exact fun j hj=>sourceMass_value_gt (hV j hj) hm
  · obtain ⟨n,hn,hm⟩ := hx.2 (.inr i)
    have hnp : n=p := by exact_mod_cast hn.symm.trans hp
    subst n
    exact fun j hj=>sourceMass_value_gt (hV j hj) hm

theorem new_sample_family_nonzero (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (x : PairKey h k → ℤ) (hx : SmallSourceSamples C.sources h k x)
    (r : Representative h k) (p : ℕ) (hp : p.Prime)
    (hr : x (representativeMap h k r)=(p:ℤ))
    (hV : ∀j ≤ l,∀origin,(C.sources origin).AboveFrequency (V j)) :
    ¬∀i : Fiber h k r,leftRows h k hs ks r p (fun a=>(x a:ZMod p)) i=0 ∧
      rightRows h k hs ks r p (fun a=>(x a:ZMod p)) i=0 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨i⟩ := fiber_nonempty h k r
  apply family_nonzero_at_new_prime h k hs ks r p _ i
    (new_sample_ancestor_units C hsep h k hh kh hs ks x hx i.val p hp ?_)
    (new_sample_frequency_bound C.sources h k x hx r p hr hV)
  simpa only [i.property] using hr

end Ostmann.Arithmetic.HistoryPairKernelReplacement

end

end OAI
