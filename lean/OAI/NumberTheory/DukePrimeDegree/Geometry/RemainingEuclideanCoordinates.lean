import OAI.NumberTheory.DukePrimeDegree.Geometry.EliminationMatrixCoordinates
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingRootCoordinates

namespace OAI

/-! # Matrix-entry coordinates on every remaining Gaussian subgroup -/

noncomputable section
open Matrix Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma roots_toFinset_remaining (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    c.roots.toFinset = allPositiveRoots n \ P := by
  have hpos : ∀ p ∈ c.finalEntries, p.1 < p.2 := by
    intro p hp
    rw [hfinal] at hp
    exact (Finset.mem_filter.mp hp).2
  ext p
  constructor
  · intro hp
    refine Finset.mem_sdiff.mpr ⟨?_,c.roots_notMem_initial hpos p (List.mem_toFinset.mp hp)⟩
    rw [←hfinal,c.finalEntries_eq_union_roots]
    exact Finset.mem_union_right P hp
  · intro hp
    have hf : p ∈ c.finalEntries := by rw [hfinal]; exact (Finset.mem_sdiff.mp hp).1
    rw [c.finalEntries_eq_union_roots] at hf
    exact (Finset.mem_union.mp hf).resolve_left (Finset.mem_sdiff.mp hp).2

def remainingIndexEquiv (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    Fin c.roots.length ≃ ↥(allPositiveRoots n \ P) :=
  (List.Nodup.getEquiv _ (c.roots_nodup (by
    intro p hp
    rw [hfinal] at hp
    exact (Finset.mem_filter.mp hp).2))).trans
    (Set.equivOfEq (by
      ext p
      change p ∈ c.roots ↔ p ∈ allPositiveRoots n \ P
      rw [←List.mem_toFinset,c.roots_toFinset_remaining hfinal]))

def remainingEuclideanCoordinates (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    c.Time ≃ₜ (↥(allPositiveRoots n \ P) → ℝ) :=
  c.timeVectorHomeomorph.trans (realCoordinatesReindex (c.remainingIndexEquiv hfinal))

lemma remainingEuclideanCoordinates_entry (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time)
    (p : ↥(allPositiveRoots n \ P)) :
    (c.word t).val p.val.1 p.val.2 = c.remainingEuclideanCoordinates hfinal t p := by
  have he : c.roots.get ((c.remainingIndexEquiv hfinal).symm p) = p.val :=
    congrArg Subtype.val ((c.remainingIndexEquiv hfinal).apply_symm_apply p)
  have H := c.word_entry_eq_time (by
    intro q hq
    rw [hfinal] at hq
    exact (Finset.mem_filter.mp hq).2) t ((c.remainingIndexEquiv hfinal).symm p)
  change (c.word t).val p.val.1 p.val.2 =
    c.timeVectorHomeomorph t ((c.remainingIndexEquiv hfinal).symm p)
  simpa only [he] using H

def remainingGroupCoordinates (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    positiveRootGeneratedGroup (allPositiveRoots n \ P) ≃ₜ (↥(allPositiveRoots n \ P) → ℝ) :=
  (c.remainingWordHomeomorph hP hfinal).symm.trans (c.remainingEuclideanCoordinates hfinal)

lemma remainingGroupCoordinates_apply (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n)
    (g : positiveRootGeneratedGroup (allPositiveRoots n \ P))
    (p : ↥(allPositiveRoots n \ P)) :
    c.remainingGroupCoordinates hP hfinal g p = g.val.val p.val.1 p.val.2 := by
  have he : c.word ((c.remainingWordHomeomorph hP hfinal).symm g) = g.val :=
    congrArg Subtype.val ((c.remainingWordHomeomorph hP hfinal).apply_symm_apply g)
  change c.remainingEuclideanCoordinates hfinal
    ((c.remainingWordHomeomorph hP hfinal).symm g) p = _
  rw [←he]
  exact (c.remainingEuclideanCoordinates_entry hfinal _ p).symm

end EliminationChain
end DukePrimeDegree

end

end OAI
