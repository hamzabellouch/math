import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootEuclideanCoordinates

namespace OAI

/-!
# The first root factor as an actual one-root chart

The remaining Gaussian chart embeds openly into the standard root
transversal. Its fibers are the same right root orbits used to define
the intrinsic one-dimensional leaf measures.
-/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma word_mem_generated_of_roots (c : EliminationChain P D)
    (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ c.roots, p ∈ S) (t : c.Time) :
    c.word t ∈ positiveRootGeneratedGroup S := by
  induction c with
  | done => exact (positiveRootGeneratedGroup S).one_mem
  | step a b hab hP hb tail ih =>
      apply (positiveRootGeneratedGroup S).mul_mem
      · exact ih (fun p hp => hS p (List.mem_cons_of_mem _ hp)) t.1
      · exact transvection_mem_positiveRootGeneratedGroup S hab
          (hS (a, b) (List.mem_cons_self)) t.2

end EliminationChain

def singletonEliminationHomeomorph {n : ℕ} {a b : Fin n} (_hab : a ≠ b) :
    EliminationSlice ({(a, b)} : Finset (Fin n × Fin n)) {a} ≃ₜ RootSlice a b a where
  toFun q := ⟨q.val, q.prop.2 a (Finset.mem_singleton_self _),
    q.prop.1 (a, b) (Finset.mem_singleton_self _)⟩
  invFun s := ⟨s.val, by
    constructor
    · intro p hp
      have hp' : p = (a, b) := Finset.mem_singleton.mp hp
      simpa only [hp'] using s.prop.2
    · intro r hr
      have hr' : r = a := Finset.mem_singleton.mp hr
      simpa only [hr'] using s.prop.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def firstRootSliceParam {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (c : EliminationChain ({(a, b)} : Finset (Fin n × Fin n)) {a})
    (z : c.FinalSlice × c.Time) : RootSlice a b a :=
  singletonEliminationHomeomorph hab (c.param z)

lemma firstRootSliceParam_isOpenEmbedding {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (c : EliminationChain ({(a, b)} : Finset (Fin n × Fin n)) {a}) :
    Topology.IsOpenEmbedding (firstRootSliceParam hab c) :=
  (singletonEliminationHomeomorph hab).isOpenEmbedding.comp c.param_isOpenEmbedding

lemma firstRootSliceParam_orbit {n : ℕ} {a b : Fin n} (hab : a ≠ b)
    (c : EliminationChain ({(a, b)} : Finset (Fin n × Fin n)) {a})
    (s : c.FinalSlice) (w : c.Time) (t : ℝ) :
    rootQuotientParametrization hab (firstRootSliceParam hab c (s, w), t) =
      rightAction (Quotient.mk _ s.val)
        (c.word w * Matrix.SpecialLinearGroup.transvection hab t) := by
  change Quotient.mk _ ((c.param (s, w)).val * Matrix.SpecialLinearGroup.transvection hab t) =
    Quotient.mk _ (s.val * (c.word w * Matrix.SpecialLinearGroup.transvection hab t))
  rw [c.param_val, mul_assoc]

lemma firstRootWord_mem_remaining {n : ℕ} {a b : Fin n}
    (c : EliminationChain ({(a, b)} : Finset (Fin n × Fin n)) {a})
    (hfinal : c.finalEntries = allPositiveRoots n) (w : c.Time) :
    c.word w ∈ positiveRootGeneratedGroup ((allPositiveRoots n).erase (a, b)) := by
  apply c.word_mem_generated_of_roots
  intro p hp
  have hpos : ∀ q ∈ c.finalEntries, q.1 < q.2 := by
    intro q hq
    rw [hfinal] at hq
    exact (Finset.mem_filter.mp hq).2
  have hn := c.roots_notMem_initial hpos p hp
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro he
    exact hn (Finset.mem_singleton.mpr he)
  · rw [←hfinal, c.finalEntries_eq_union_roots]
    exact Finset.mem_union_right _ (List.mem_toFinset.mpr hp)

theorem exists_firstRootBox (n : ℕ) {a b : Fin n} (hab : a ≠ b)
    (c : EliminationChain ({(a, b)} : Finset (Fin n × Fin n)) {a})
    (z : c.FinalSlice × c.Time) (t : ℝ) :
    ∃ (A : RootBox hab a) (R : ℝ),
      (firstRootSliceParam hab c z, t) ∈ A.domain ∧
      A.transverse ⊆ Set.range (firstRootSliceParam hab c) ∧
      A.time ⊆ rootLeafWindow R 0 := by
  obtain ⟨A, hA⟩ := exists_rootBox_at_coordinates hab (firstRootSliceParam hab c z, t)
  let U := A.transverse ∩ Set.range (firstRootSliceParam hab c)
  have hU : IsOpen U := A.transverse_open.inter (firstRootSliceParam_isOpenEmbedding hab c).isOpen_range
  let R := |t| + 1
  let J := A.time ∩ Ioo (-R) R
  have hJ : IsOpen J := A.time_open.inter isOpen_Ioo
  let D := A.shrink U J hU hJ inter_subset_left inter_subset_left
  refine ⟨D, R, ⟨⟨hA.1, ⟨z, rfl⟩⟩, hA.2, ?_⟩, inter_subset_right, ?_⟩
  · apply abs_lt.mp
    exact lt_add_one _
  · intro u hu
    change u ∈ A.time ∩ Ioo (-R) R at hu
    simpa only [rootLeafWindow, Nat.cast_zero, add_zero] using hu.2

end DukePrimeDegree

end

end OAI
