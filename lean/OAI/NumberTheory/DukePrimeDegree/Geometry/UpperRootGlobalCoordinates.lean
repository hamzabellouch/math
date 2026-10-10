import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootLongBoxes

namespace OAI

/-!
# Global coordinates on the upper unipotent group

Gaussian elimination never encounters a zero pivot on a unipotent
upper triangular matrix. Consequently the ordered root word covers
that entire group, and is a homeomorphism onto it.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma upperRoot_diagonal {n : ℕ} {g : G n}
    (hg : g ∈ positiveRootGeneratedGroup (allPositiveRoots n)) (a : Fin n) :
    g.val a a = 1 := by
  have h := positiveRootGeneratedGroup_pattern (allPositiveRoots n)
    (allPositiveRoots_closed n) hg a a (by simp [allPositiveRoots])
  simpa only [Matrix.one_apply, ite_true] using h

lemma upperRoot_zeroPattern_eq_one {n : ℕ} {g : G n}
    (hg : g ∈ positiveRootGeneratedGroup (allPositiveRoots n))
    (hz : ZeroPattern (allPositiveRoots n) g) : g = 1 := by
  apply Subtype.ext
  ext a b
  by_cases hab : a < b
  · rw [hz (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)]
    simp [ne_of_lt hab]
  · exact positiveRootGeneratedGroup_pattern (allPositiveRoots n)
      (allPositiveRoots_closed n) hg a b (by simpa [allPositiveRoots] using hab)

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

theorem exists_param_of_upperRoot (c : EliminationChain P D)
    (hS : c.finalEntries ⊆ allPositiveRoots n) (q : EliminationSlice P D)
    (hq : q.val ∈ positiveRootGeneratedGroup (allPositiveRoots n)) :
    ∃ (s : c.FinalSlice) (t : c.Time), c.param (s, t) = q ∧
      s.val ∈ positiveRootGeneratedGroup (allPositiveRoots n) := by
  induction c with
  | done => exact ⟨q, PUnit.unit, rfl, hq⟩
  | @step P D a b hab hP hb tail ih =>
      have ha : q.val.val a a ≠ 0 := by rw [upperRoot_diagonal hq a]; exact one_ne_zero
      let E := eliminationRootHomeomorph P D hab hP hb
      let z := E ⟨q, ha⟩
      have habS : (a, b) ∈ allPositiveRoots n :=
        hS (tail.entries_subset_final (Finset.mem_insert_self _ _))
      have hz : z.1.val ∈ positiveRootGeneratedGroup (allPositiveRoots n) := by
        change q.val * Matrix.SpecialLinearGroup.transvection hab
          (-rootParameter a b a q.val) ∈ positiveRootGeneratedGroup (allPositiveRoots n)
        exact (positiveRootGeneratedGroup _).mul_mem hq
          (transvection_mem_positiveRootGeneratedGroup _ hab habS _)
      obtain ⟨s, t, hst, hs⟩ := ih hS z.1 hz
      refine ⟨s, (t, z.2), ?_, hs⟩
      change (E.symm (tail.param (s, t), z.2)).val = q
      rw [hst]
      exact congrArg Subtype.val (E.symm_apply_apply ⟨q, ha⟩)

end EliminationChain

theorem upperRootWord_surjective (n : ℕ)
    (g : positiveRootGeneratedGroup (allPositiveRoots n)) :
    ∃ t : UpperRootTime n, (completeRootChain n).word t = g.val := by
  let q : EliminationSlice (∅ : Finset (Fin n × Fin n)) ∅ :=
    ⟨g.val, by constructor <;> simp [ZeroPattern, NonzeroPivots]⟩
  obtain ⟨s, t, he, hs⟩ := (completeRootChain n).exists_param_of_upperRoot
    (by rw [completeRootChain_final]) q g.prop
  have hs1 : s.val = 1 := upperRoot_zeroPattern_eq_one hs (by
    simpa only [←completeRootChain_final n] using s.prop.1)
  have hv := congrArg (fun a : EliminationSlice (∅ : Finset (Fin n × Fin n)) ∅ => a.val) he
  change ((completeRootChain n).param (s, t)).val = g.val at hv
  rw [EliminationChain.param_val, hs1, one_mul] at hv
  exact ⟨t, hv⟩

def upperRootWordMap (n : ℕ) (t : UpperRootTime n) :
    positiveRootGeneratedGroup (allPositiveRoots n) :=
  ⟨(completeRootChain n).word t, upperRootWord_mem n t⟩

theorem upperRootWordMap_bijective (n : ℕ) : Function.Bijective (upperRootWordMap n) := by
  constructor
  · intro t u h
    exact upperRootWord_injective n (congrArg Subtype.val h)
  · intro g
    obtain ⟨t, ht⟩ := upperRootWord_surjective n g
    exact ⟨t, Subtype.ext ht⟩

theorem upperRootWord_isEmbedding (n : ℕ) :
    Topology.IsEmbedding (fun t : UpperRootTime n => (completeRootChain n).word t) := by
  have he := (upperRootParam_isOpenEmbedding n).isEmbedding.comp
    (isEmbedding_prodMkRight (upperRootIdentity n))
  convert he using 1
  funext t
  rw [Function.comp_apply, upperRootParam_eq_mul]
  exact (one_mul _).symm

theorem upperRootWordMap_isEmbedding (n : ℕ) : Topology.IsEmbedding (upperRootWordMap n) :=
  Topology.IsEmbedding.subtypeVal.of_comp_iff.mp (upperRootWord_isEmbedding n)

def upperRootWordHomeomorph (n : ℕ) :
    UpperRootTime n ≃ₜ positiveRootGeneratedGroup (allPositiveRoots n) :=
  (upperRootWordMap_isEmbedding n).toHomeomorphOfSurjective (upperRootWordMap_bijective n).2

@[simp] lemma upperRootWordHomeomorph_apply (n : ℕ) (t : UpperRootTime n) :
    (upperRootWordHomeomorph n t).val = (completeRootChain n).word t := rfl

end DukePrimeDegree

end

end OAI
