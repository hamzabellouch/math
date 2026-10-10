import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates

namespace OAI

/-!
# Every positive root occurs exactly once

The chart compatibility conditions prohibit repeating an eliminated
root: a repeat would force an eliminated diagonal entry. A complete
chain therefore lists exactly the positive roots, without repetitions.
-/

noncomputable section
open Matrix Set

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def roots : {P : Finset (Fin n × Fin n)} → {D : Finset (Fin n)} →
    EliminationChain P D → List (Fin n × Fin n)
  | _, _, .done => []
  | _, _, .step a b _ _ _ tail => (a, b) :: tail.roots

lemma finalEntries_eq_union_roots (c : EliminationChain P D) :
    c.finalEntries = P ∪ c.roots.toFinset := by
  induction c with
  | done => simp [finalEntries, roots]
  | step a b hab hP hb tail ih =>
      simpa [finalEntries, roots, Finset.union_comm, Finset.union_left_comm,
        Finset.union_assoc] using ih

lemma roots_notMem_initial (c : EliminationChain P D)
    (hpos : ∀ p ∈ c.finalEntries, p.1 < p.2) :
    ∀ p ∈ c.roots, p ∉ P := by
  induction c with
  | done => simp [roots]
  | @step P D a b hab hP hb tail ih =>
      intro p hp
      change p ∈ (a, b) :: tail.roots at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · intro hpP
        have haa := hP a hpP
        exact lt_irrefl a (hpos (a, a)
          (tail.entries_subset_final (Finset.mem_insert_of_mem haa)))
      · exact fun hpP => ih hpos p hp (Finset.mem_insert_of_mem hpP)

lemma roots_nodup (c : EliminationChain P D)
    (hpos : ∀ p ∈ c.finalEntries, p.1 < p.2) : c.roots.Nodup := by
  induction c with
  | done => exact List.nodup_nil
  | step a b hab hP hb tail ih =>
      apply List.nodup_cons.mpr
      exact ⟨fun hp => tail.roots_notMem_initial hpos (a, b) hp
        (Finset.mem_insert_self _ _), ih hpos⟩

end EliminationChain

lemma completeRootChain_roots_toFinset (n : ℕ) :
    (completeRootChain n).roots.toFinset = allPositiveRoots n := by
  have h := (completeRootChain n).finalEntries_eq_union_roots
  simpa only [completeRootChain_final, Finset.empty_union] using h.symm

lemma completeRootChain_roots_nodup (n : ℕ) : (completeRootChain n).roots.Nodup := by
  apply (completeRootChain n).roots_nodup
  intro p hp
  rw [completeRootChain_final] at hp
  exact (Finset.mem_filter.mp hp).2

lemma completeRootChain_roots_length (n : ℕ) :
    (completeRootChain n).roots.length = (allPositiveRoots n).card := by
  rw [←completeRootChain_roots_toFinset]
  exact (List.toFinset_card_of_nodup (completeRootChain_roots_nodup n)).symm

end DukePrimeDegree

end

end OAI
