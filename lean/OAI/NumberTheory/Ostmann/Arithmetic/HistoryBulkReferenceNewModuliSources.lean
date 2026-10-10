import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceNewModuliBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSourceCollisionSeparation

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkReferenceNewModuli
open Construction Conclusion Construction.CanonicalOccurrenceTransport
open HistoryCRTIntegration HistoryPairBulkTransport HistoryBulkSourceCollision
open HistoryOccurrenceVariables HistoryRepresentativeSourceSeparation HistoryPairRepresentatives HistorySymbolicEncoding

theorem assigned_product_coprime_of_fixed_nonbulk (sources : SourceFamily) (T : List SourceSlot)
    (x₀ x : SourceAssignment sources T) (M : ℕ)
    (hfixed : ∀i:Fin T.length,(T.get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hold : Nat.Coprime ((assignedSlots sources T x₀).map SmallSlot.value).prod M)
    (hbulk : ∀q∈assignedSlots sources T x,q.role=.bulk → Nat.Coprime q.value M) :
    Nat.Coprime ((assignedSlots sources T x).map SmallSlot.value).prod M := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro n hn
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hn
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  by_cases hi : (T.get i).role=.bulk
  · apply hbulk _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact hi
  · change Nat.Coprime (x i).val M
    rw [hfixed i hi]
    apply Nat.coprime_list_prod_left_iff.mp hold
    exact List.mem_map.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩

variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth : ℕ} {E : Finset ℕ}
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem bulk_coprime_internalSlot (C : InitialSourceChoice d Bs BD Bz depth L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator)
    (h : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) h)
    (hs : h.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (p : C.bulk.Sample) (hp : C.bulk.law.mass p≠0) (i : InternalKey h) :
    Nat.Coprime p.val (internalSlot h i).value := by
  have hr : (sourceOfSlot (internalSlot h i)).role≠.bulk := by
    change (internalSlot h i).role≠.bulk
    rw [internalSlot_role h hs i]
    simp
  have hb := Template.initial_nonbulk_origin_bounds (internalSlot_source_mem _ h hh i) hr
  have hi := hm i
  unfold sourceMass at hi
  split_ifs at hi with him
  · exact bulk_nonbulk_source_coprime C spectator hsep (internalSlot h i).origin hb.1 hb.2
      p hp ⟨(internalSlot h i).value,him⟩ hi
  · exact (hi rfl).elim

theorem bulk_coprime_representativeModulus (C : InitialSourceChoice d Bs BD Bz depth L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (km : ∀i,sourceMass C.sources (internalSlot k i)≠0)
    (p : C.bulk.Sample) (hp : C.bulk.law.mass p≠0) :
    Nat.Coprime p.val (representativeModulus h k) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro r hr
  apply Nat.Coprime.pow_right 2
  obtain ⟨i,rfl⟩ := label_surjective h k r
  rcases i with i | i
  · exact bulk_coprime_internalSlot C spectator hsep h hh hs hm p hp i
  · exact bulk_coprime_internalSlot C spectator hsep k kh ks km p hp i

theorem assigned_product_coprime_outside (C : InitialSourceChoice d Bs BD Bz depth L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator) (T : List SourceSlot)
    (hT : ∀q∈T,q∈Template.initial (2*(bulkSize depth L/2)) depth)
    (x₀ x : SourceAssignment C.sources T)
    (hx : (assignmentPrior C.sources T).mass x≠0)
    (hfixed : ∀i:Fin T.length,(T.get i).role≠.bulk → (x i).val=(x₀ i).val)
    (hout : ∀q∈outside,∃p:spectator.Sample,p.val=q ∧ spectator.law.mass p≠0)
    (hold : Nat.Coprime ((assignedSlots C.sources T x₀).map SmallSlot.value).prod outside.prod) :
    Nat.Coprime ((assignedSlots C.sources T x).map SmallSlot.value).prod outside.prod := by
  apply assigned_product_coprime_of_fixed_nonbulk C.sources T x₀ x outside.prod hfixed hold
  intro q hq hr
  obtain ⟨p,hpv,hpm⟩ := assigned_bulk_representative C T hT x hx q hq hr
  rw [←hpv]
  apply Nat.coprime_list_prod_right_iff.mpr
  intro a ha
  obtain ⟨r,hrv,hrm⟩ := hout a ha
  rw [←hrv]
  exact disjointMass_coprime hsep.spectator_bulk.symm p r hpm hrm

theorem assigned_product_coprime_representatives (C : InitialSourceChoice d Bs BD Bz depth L E)
    (spectator : PrimeSource) (hsep : C.CrossRoleSeparation spectator) (T : List SourceSlot)
    (hT : ∀q∈T,q∈Template.initial (2*(bulkSize depth L/2)) depth)
    (x₀ x : SourceAssignment C.sources T)
    (hx : (assignmentPrior C.sources T).mass x≠0)
    (hfixed : ∀i:Fin T.length,(T.get i).role≠.bulk → (x i).val=(x₀ i).val)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hm : ∀i,sourceMass C.sources (internalSlot h i)≠0)
    (km : ∀i,sourceMass C.sources (internalSlot k i)≠0)
    (hold : Nat.Coprime ((assignedSlots C.sources T x₀).map SmallSlot.value).prod
      (representativeModulus h k)) :
    Nat.Coprime ((assignedSlots C.sources T x).map SmallSlot.value).prod
      (representativeModulus h k) := by
  apply assigned_product_coprime_of_fixed_nonbulk C.sources T x₀ x _ hfixed hold
  intro q hq hr
  obtain ⟨p,hpv,hpm⟩ := assigned_bulk_representative C T hT x hx q hq hr
  rw [←hpv]
  exact bulk_coprime_representativeModulus C spectator hsep h k hh kh hs ks hm km p hpm

end Ostmann.Arithmetic.HistoryBulkReferenceNewModuli

end

end OAI
