import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionSeparation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConversePlanIntegerSample
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationAncestors
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalParent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction Conclusion CanonicalOccurrenceTransport HistoryRepresentativeSourceSeparation
open HistoryBulkSupportConversePlan

theorem canonical_internalSource_role (seed : List SourceSlot) {l : ℕ} (i : Internal seed l) :
    (internalSource seed i).role = .compensation (CanonicalOccurrenceTransport.internalLevel seed i) := by
  induction l with
  | zero => exact Empty.elim i
  | succ l ih =>
    rcases i with i | i | i
    · exact of_decide_eq_true (List.mem_filter.mp
        (List.get_mem (Template.extracted (l+1) (Template.current seed l)) i)).2
    · exact ih i
    · exact ih i

theorem canonical_internalLevel_le (seed : List SourceSlot) {l : ℕ} (i : Internal seed l) :
    CanonicalOccurrenceTransport.internalLevel seed i ≤ l := by
  induction l with
  | zero => exact Empty.elim i
  | succ l ih =>
    rcases i with i | i | i
    · exact le_rfl
    · exact (ih i).trans (Nat.le_succ l)
    · exact (ih i).trans (Nat.le_succ l)

theorem canonical_historyDraws_mass_ne_zero (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (c : HistoryChoices sources seed V l)
    (hc : choicesMass sources seed V l c ≠ 0) (i : Internal seed l) :
    (sources (internalSource seed i).origin).law.mass (historyDraws sources seed V l c i) ≠ 0 := by
  induction l with
  | zero => exact Empty.elim i
  | succ l ih =>
    change (_ * _ * _) ≠ 0 at hc
    rcases i with i | i | i
    · exact assignmentPrior_component_mass_ne_zero sources _ c.2.2.1
        (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc).1).1 i
    · exact ih c.2.2.2.1 (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc).1).2 i
    · exact ih c.2.2.2.2 (mul_ne_zero_iff.mp hc).2 i

private theorem finCongr_value {a b : ℕ} (h : a=b) (i : Fin a) :
    (finCongr h i).val=i.val := by
  cases h
  rfl

private theorem assigned_get_value (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (h : T.length=(assignedSlots sources T x).length)
    (q : Fin T.length) :
    ((assignedSlots sources T x).get (finCongr h q)).value = (x q).val := by
  simp only [assignedSlots, Template.sample, List.get_eq_getElem, List.getElem_ofFn]
  exact congrArg (fun j => (x j).val) (Fin.ext (finCongr_value h q))

theorem newIntegerSample_ancestor_units
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) {spectator : PrimeSource}
    (hsep : C.CrossRoleSeparation spectator) (V : ℕ → ℕ) (l : ℕ)
    (x : SourceAssignment C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l))
    (hx : (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x ≠ 0)
    (c : HistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k) V l)
    (hc : choicesMass C.sources (Template.initial (2*(bulkSize k L/2)) k) V l c ≠ 0)
    (s : ℤ) (Gp Gm : ℕ) (Xp Xm : ℤ)
    (i : Internal (Template.initial (2*(bulkSize k L/2)) k) l)
    (q : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length ⊕
      Internal (Template.initial (2*(bulkSize k L/2)) k) l)
    (hlevel : CanonicalOccurrenceTransport.internalLevel _ i < coordinateLevel _ l (.inr q)) :
    (newIntegerSample C.sources _ V l
      ⟨s,Gp,Gm,assignedSlots C.sources _ x⟩ c (Template.assignedSlots_matches C.sources _ x)
      Xp Xm (.inr q) : ZMod (historyDraws C.sources _ V l c i).val) ≠ 0 := by
  let seed := Template.initial (2*(bulkSize k L/2)) k
  let p := historyDraws C.sources seed V l c i
  have hp : p.val.Prime := (C.sources (internalSource seed i).origin).prime _ p.property
  have hpm := canonical_historyDraws_mass_ne_zero C.sources seed V l c hc i
  have hi := canonical_internalSource_role seed i
  rcases q with q | q
  · have hdis : (C.sources (internalSource seed i).origin).DisjointMass
        (C.sources (Template.current seed l)[q].origin) := by
      apply source_disjoint_of_comp C hsep (internalSource_mem_seed seed i)
        (Template.mem_current_mem_seed (List.getElem_mem q.isLt)) hi
      intro he
      have hgt := Template.current_types_gt seed (initial_seed_types_pos _ _) l _
        (List.getElem_mem q.isLt) _ (he.trans hi)
      have hle := canonical_internalLevel_le seed i
      omega
    have hq := assignmentPrior_component_mass_ne_zero C.sources _ x hx q
    have hne := hdis p (x q) hpm hq
    have hu := natCast_nonzero_of_prime_ne hp ((C.sources _).prime _ (x q).property) hne
    simpa only [newIntegerSample, assigned_get_value, Int.cast_natCast] using hu
  · have hdis : (C.sources (internalSource seed i).origin).DisjointMass
        (C.sources (internalSource seed q).origin) := by
      apply source_disjoint_of_comp C hsep (internalSource_mem_seed seed i)
        (internalSource_mem_seed seed q) hi
      rw [hi, canonical_internalSource_role seed q]
      intro he
      have he' := SlotRole.compensation.inj he
      change CanonicalOccurrenceTransport.internalLevel seed i <
        CanonicalOccurrenceTransport.internalLevel seed q at hlevel
      omega
    have hq := canonical_historyDraws_mass_ne_zero C.sources seed V l c hc q
    have hne := hdis p (historyDraws C.sources seed V l c q) hpm hq
    have hu := natCast_nonzero_of_prime_ne hp
      ((C.sources _).prime _ (historyDraws C.sources seed V l c q).property) hne
    simpa only [newIntegerSample, Int.cast_natCast] using hu

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
