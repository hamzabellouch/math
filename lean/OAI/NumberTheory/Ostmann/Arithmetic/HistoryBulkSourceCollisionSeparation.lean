import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionBasic
import OAI.NumberTheory.Ostmann.Conclusion.BulkPermutation
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupportCells
import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSourceCollision
open Construction Conclusion HistoryBulkDiagramParameters
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem disjointMass_coprime {S T : PrimeSource} (h : S.DisjointMass T)
    (p : S.Sample) (q : T.Sample) (hp : S.law.mass p ≠ 0) (hq : T.law.mass q ≠ 0) :
    p.val.Coprime q.val :=
  (Nat.coprime_primes (S.prime _ p.property) (T.prime _ q.property)).mpr (h p q hp hq)

theorem bulk_nonbulk_source_coprime
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hsep : C.CrossRoleSeparation spectator) (origin : ℕ)
    (hlo : 2*(bulkSize k L/2) ≤ origin)
    (hhi : origin < 2*(bulkSize k L/2)+6+4*k)
    (p : C.bulk.Sample) (hp : C.bulk.law.mass p ≠ 0)
    (q : (C.sources origin).Sample) (hq : (C.sources origin).law.mass q ≠ 0) :
    p.val.Coprime q.val := by
  have h := initialSourceValue_rel_nonbulk (bulkSize k L/2) k C.bulk ()
    (C.cells.topSource E C.deleted_card) (fun _ => ())
    (C.cells.compSource E C.deleted_card) (fun _ _ => ())
    (fun (S : PrimeSource) (_ : Unit) => ∀ q : S.Sample, S.law.mass q ≠ 0 → p.val.Coprime q.val)
    (fun i q hq => disjointMass_coprime (hsep.bulk_aux (.inl i)) p q hp hq)
    (fun j i q hq => disjointMass_coprime (hsep.bulk_aux (.inr (j,i))) p q hp hq)
    origin hlo hhi
  exact h q hq

theorem bulk_assigned_nonbulk_coprime
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hsep : C.CrossRoleSeparation spectator) (T : List SourceSlot)
    (hT : ∀ a ∈ T, a ∈ Template.initial (2*(bulkSize k L/2)) k)
    (x : SourceAssignment C.sources T) (hx : (assignmentPrior C.sources T).mass x ≠ 0)
    (p : C.bulk.Sample) (hp : C.bulk.law.mass p ≠ 0)
    (a : SmallSlot) (ha : a ∈ assignedSlots C.sources T x) (hr : a.role ≠ .bulk) :
    p.val.Coprime a.value := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  have hb := Template.initial_nonbulk_origin_bounds (hT T[i] (List.getElem_mem i.isLt)) hr
  exact bulk_nonbulk_source_coprime C spectator hsep T[i].origin hb.1 hb.2 p hp (x i)
    (assignmentPrior_component_mass_ne_zero C.sources T x hx i)

theorem assigned_bulk_representative
    (C : InitialSourceChoice d Bs BD Bz k L E) (T : List SourceSlot)
    (hT : ∀ a ∈ T, a ∈ Template.initial (2*(bulkSize k L/2)) k)
    (x : SourceAssignment C.sources T) (hx : (assignmentPrior C.sources T).mass x ≠ 0)
    (a : SmallSlot) (ha : a ∈ assignedSlots C.sources T x) (hr : a.role = .bulk) :
    ∃ p : C.bulk.Sample, p.val = a.value ∧ C.bulk.law.mass p ≠ 0 := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  have hb := initial_bulk_origin_lt (hT T[i] (List.getElem_mem i.isLt)) hr
  have he : C.sources T[i].origin = C.bulk := initialSourceValue_bulk _ _ _ _ _ hb
  have hrep : ∀ p : (C.sources T[i].origin).Sample,
      (C.sources T[i].origin).law.mass p ≠ 0 →
      ∃ q : C.bulk.Sample, q.val = p.val ∧ C.bulk.law.mass q ≠ 0 := by
    rw [he]
    exact fun p hp => ⟨p,rfl,hp⟩
  exact hrep (x i) (assignmentPrior_component_mass_ne_zero C.sources T x hx i)

theorem assigned_small_outside_pairwise
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (hsep : C.CrossRoleSeparation spectator) (T : List SourceSlot)
    (hT : ∀ a ∈ T, a ∈ Template.initial (2*(bulkSize k L/2)) k)
    (x y : SourceAssignment C.sources T) (hx : (assignmentPrior C.sources T).mass x ≠ 0)
    (hnonbulk : ∀ i : Fin T.length, T[i].role ≠ .bulk → (x i:ℕ) = (y i:ℕ))
    (outside : List ℕ)
    (houtside : ∀ q ∈ outside, ∃ p : spectator.Sample,
      p.val = q ∧ spectator.law.mass p ≠ 0)
    (href : ((assignedSlots C.sources T y).map SmallSlot.value ++ outside).Pairwise Nat.Coprime)
    (hbulk : (((assignedSlots C.sources T x).filter
      (fun a => a.role = .bulk)).map SmallSlot.value).Nodup) :
    ((assignedSlots C.sources T x).map SmallSlot.value ++ outside).Pairwise Nat.Coprime := by
  apply small_outside_pairwise_of_reference _ _ outside
    (assignedSlots_erase_eq C.sources T x y hnonbulk) href
    (assignedSlots_prime C.sources T x) hbulk
  · intro a ha hr b hb hbr
    obtain ⟨p,hp,hpm⟩ := assigned_bulk_representative C T hT x hx a ha hr
    rw [← hp]
    exact bulk_assigned_nonbulk_coprime C spectator hsep T hT x hx p hpm b hb hbr
  · intro a ha hr q hq
    obtain ⟨p,hp,hpm⟩ := assigned_bulk_representative C T hT x hx a ha hr
    obtain ⟨r,hrv,hrm⟩ := houtside q hq
    rw [← hp, ← hrv]
    exact disjointMass_coprime hsep.spectator_bulk.symm p r hpm hrm

end Ostmann.Arithmetic.HistoryBulkSourceCollision

end

end OAI
