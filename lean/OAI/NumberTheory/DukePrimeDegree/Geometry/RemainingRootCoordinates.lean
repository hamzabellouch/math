import OAI.NumberTheory.DukePrimeDegree.Geometry.LexicographicRootWeights
import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootGlobalCoordinates

namespace OAI

/-! # Global coordinates on each remaining Gaussian root subgroup -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def identityFinal (c : EliminationChain P D) (hfinal : c.finalEntries = allPositiveRoots n) :
    c.FinalSlice :=
  ⟨1, by
    constructor
    · intro p hp
      rw [hfinal] at hp
      have hne := ne_of_lt (Finset.mem_filter.mp hp).2
      change (1 : Matrix (Fin n) (Fin n) ℝ) p.1 p.2 = 0
      simp [hne]
    · intro r _
      change (1 : Matrix (Fin n) (Fin n) ℝ) r r ≠ 0
      simp⟩

lemma word_mem_remaining (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    c.word t ∈ positiveRootGeneratedGroup (allPositiveRoots n \ P) := by
  apply c.word_mem_generated_of_roots
  intro p hp
  have hpos : ∀ q ∈ c.finalEntries, q.1 < q.2 := by
    intro q hq
    rw [hfinal] at hq
    exact (Finset.mem_filter.mp hq).2
  refine Finset.mem_sdiff.mpr ⟨?_, c.roots_notMem_initial hpos p hp⟩
  rw [←hfinal, c.finalEntries_eq_union_roots]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr hp)

theorem word_surjective_remaining (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (g : positiveRootGeneratedGroup (allPositiveRoots n \ P)) :
    ∃ t : c.Time, c.word t = g.val := by
  have hgU : g.val ∈ positiveRootGeneratedGroup (allPositiveRoots n) :=
    positiveRootGeneratedGroup_mono Finset.sdiff_subset g.prop
  have hpat := positiveRootGeneratedGroup_pattern (allPositiveRoots n \ P)
    (initialRemaining_roots_closed P hP) g.prop
  let q : EliminationSlice P D := ⟨g.val, by
    constructor
    · intro p hp
      have hn : p ∉ allPositiveRoots n \ P := by
        intro h
        exact (Finset.mem_sdiff.mp h).2 hp
      have hz := hpat p.1 p.2 hn
      have hne := ne_of_lt (Finset.mem_filter.mp (hP p hp).1).2
      simpa only [Matrix.one_apply, hne, ite_false] using hz
    · intro a _
      rw [upperRoot_diagonal hgU a]
      exact one_ne_zero⟩
  obtain ⟨s, t, he, hs⟩ := c.exists_param_of_upperRoot (by rw [hfinal]) q hgU
  have hs1 : s.val = 1 := upperRoot_zeroPattern_eq_one hs (by
    simpa only [hfinal] using s.prop.1)
  have hv := congrArg (fun z : EliminationSlice P D => z.val) he
  change (c.param (s,t)).val = g.val at hv
  rw [c.param_val, hs1, one_mul] at hv
  exact ⟨t,hv⟩

theorem word_isEmbedding_remaining (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    Topology.IsEmbedding c.word := by
  have he := Topology.IsEmbedding.subtypeVal.comp
    (c.param_isOpenEmbedding.isEmbedding.comp (isEmbedding_prodMkRight (c.identityFinal hfinal)))
  convert he using 1
  funext t
  rw [Function.comp_apply, Function.comp_apply, c.param_val]
  exact (one_mul _).symm

def remainingWordMap (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    positiveRootGeneratedGroup (allPositiveRoots n \ P) :=
  ⟨c.word t, c.word_mem_remaining hfinal t⟩

theorem remainingWordMap_isEmbedding (c : EliminationChain P D)
    (hfinal : c.finalEntries = allPositiveRoots n) :
    Topology.IsEmbedding (c.remainingWordMap hfinal) :=
  Topology.IsEmbedding.subtypeVal.of_comp_iff.mp (c.word_isEmbedding_remaining hfinal)

theorem remainingWordMap_surjective (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) :
    Function.Surjective (c.remainingWordMap hfinal) := by
  intro g
  obtain ⟨t,ht⟩ := c.word_surjective_remaining hP hfinal g
  exact ⟨t,Subtype.ext ht⟩

def remainingWordHomeomorph (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) :
    c.Time ≃ₜ positiveRootGeneratedGroup (allPositiveRoots n \ P) :=
  (c.remainingWordMap_isEmbedding hfinal).toHomeomorphOfSurjective
    (c.remainingWordMap_surjective hP hfinal)

@[simp] lemma remainingWordHomeomorph_apply (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n) (t : c.Time) :
    (c.remainingWordHomeomorph hP hfinal t).val = c.word t := rfl

end EliminationChain
end DukePrimeDegree

end

end OAI
