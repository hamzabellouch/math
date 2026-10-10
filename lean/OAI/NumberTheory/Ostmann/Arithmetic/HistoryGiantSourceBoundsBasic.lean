import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceXi
import OAI.NumberTheory.Ostmann.Construction.CanonicalSourceLabels
import OAI.NumberTheory.Ostmann.Construction.SelectedSourceSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantSourceBounds
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistoryRepresentativeSourceSeparation

theorem slot_prime_of_mass (sources : SourceFamily) (q : SmallSlot)
    (hq : sourceMass sources q ≠ 0) : Nat.Prime q.value := by
  unfold sourceMass at hq
  split_ifs at hq with hm
  · exact (sources q.origin).prime _ hm
  · exact (hq rfl).elim

theorem selected_slot_log_support {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (q : SmallSlot)
    (hq : sourceOfSlot q ∈ Template.initial (2*(Conclusion.bulkSize k L/2)) k)
    (hm : sourceMass C.sources q ≠ 0) (hr : q.role ≠ .bulk) :
    |Real.log (q.value : ℝ)-C.cells.center (Conclusion.bulkSize k L/2) q.origin| ≤ 1 := by
  have hb := Template.initial_nonbulk_origin_bounds hq hr
  unfold sourceMass at hm
  split_ifs at hm with hp
  · exact (C.source_log_support q.origin hb.1 hb.2 ⟨q.value,hp⟩ hm).le
  · exact (hm rfl).elim

theorem sourceDomain_of_slot_masses {d : Decomposition} {Bs BD Bz : ℝ}
    {k : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) {l : ℕ} (h : History l)
    (hlabels : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize k L/2)) k) h)
    (hroot : ∀ i : Fin h.root.small.length,
      sourceMass C.sources (h.root.small.get i) ≠ 0)
    (hinternal : ∀ i : InternalKey h, sourceMass C.sources (internalSlot h i) ≠ 0)
    (hpositive : ∀ b : Bool, 0 < (integerSample h (.inl b) : ℝ))
    (hgiant : ∀ b : Bool,
      |Real.log (integerSample h (.inl b) : ℝ)-(C.giantCenter : ℝ)| ≤ 1) :
    SourceDomain (Conclusion.bulkSize k L/2) k (C.giantCenter : ℝ)
      (C.cells.center (Conclusion.bulkSize k L/2)) h (fun i => (integerSample h i : ℝ)) := by
  constructor
  · intro i
    rcases i with b | i | i
    · exact hpositive b
    · have hp := (slot_prime_of_mass C.sources _ (hroot i)).pos
      simpa only [integerSample, Int.cast_natCast] using (Nat.cast_pos.mpr hp :
        0 < ((h.root.small.get i).value : ℝ))
    · have hp := (slot_prime_of_mass C.sources _ (hinternal i)).pos
      simpa only [integerSample, Int.cast_natCast] using (Nat.cast_pos.mpr hp :
        0 < ((internalSlot h i).value : ℝ))
  · intro i q hi hq
    rcases i with b | i | i
    · cases hi
    · have he : h.root.small.get i = q := Option.some.inj hi
      subst q
      simpa only [integerSample, Int.cast_natCast] using selected_slot_log_support C _
        (rootSlot_source_mem _ h hlabels i) (hroot i) hq
    · have he : internalSlot h i = q := Option.some.inj hi
      subst q
      simpa only [integerSample, Int.cast_natCast] using selected_slot_log_support C _
        (internalSlot_source_mem _ h hlabels i) (hinternal i) hq
  · exact hgiant
  · exact hlabels.leaves

end Ostmann.Arithmetic.HistoryGiantSourceBounds

end

end OAI
