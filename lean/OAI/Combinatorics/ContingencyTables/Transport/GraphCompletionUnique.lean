import OAI.Combinatorics.ContingencyTables.Transport.GraphIntegralCompletion

namespace OAI

/-!
# Uniqueness of the actual forest completion

A homogeneous real table supported on an acyclic row/column graph,
with zero sums at every nonroot vertex, vanishes. The proof constructs
an actual root-away deletion cut for each tree cell and isolates that
cell in the signed margin sum. Thus the integral root-path construction
is the unique integral completion, without a leaf-order encoding input.
-/

namespace ContingencyTables.GraphCompletionUnique

open scoped BigOperators Classical
open SimpleGraph
open MaximumForest ForestCut ForestCapacity GraphIntegralCompletion

variable {I J : Type*} [Fintype I] [Fintype J]

/-- This is the nonsingular forest-incidence assertion needed by the
companion's tree-coordinate sum, over the reals as well as the integers. -/
theorem zero_of_nonroot_sums (T : SimpleGraph (I⊕J))
    (hT : T.IsAcyclic) (z : I → J → ℝ)
    (hsupport : ∀ i j, ¬T.Adj (.inl i) (.inr j) → z i j=0)
    (hr : ∀ i, Sum.inl i≠componentRoot T (.inl i) → (∑ j, z i j)=0)
    (hc : ∀ j, Sum.inr j≠componentRoot T (.inr j) → (∑ i, z i j)=0) :
    ∀ i j, z i j=0 := by
  intro i₀ j₀
  by_cases ht : T.Adj (.inl i₀) (.inr j₀)
  · let t : Sym2 (I⊕J) := s(Sum.inl i₀,Sum.inr j₀)
    let D := T.deleteEdges {t}
    let root := componentRoot T (.inl i₀)
    have hrootReach : T.Reachable root (.inl i₀) :=
      (componentRoot_reachable T (.inl i₀)).symm
    obtain ⟨r,hrr,hrootSide,hcross⟩ := exists_root_avoiding_side T hT ht root hrootReach
    let rowU : I → Bool := fun i => side D r (.inl i)
    let colU : J → Bool := fun j => side D r (.inr j)
    have hcross' : rowU i₀≠colU j₀ := hcross
    have hrootRoot : componentRoot T root=root := componentRoot_idempotent T (.inl i₀)
    have hnonroot : ∀ v : I⊕J, side D r v=true → v≠componentRoot T v := by
      intro v hv he
      have hrv : D.Reachable r v := by simpa only [side,decide_eq_true_eq] using hv
      have hcomp := hrr.trans (hrv.mono (T.deleteEdges_le {t}))
      have hsame : componentRoot T v=root := by
        rw [← componentRoot_constant T hcomp,hrootRoot]
      have hvroot : v=root := he.trans hsame
      have hbad : side D r root=true := by simpa only [hvroot] using hv
      exact Bool.false_ne_true (hrootSide.symm.trans hbad)
    let f : I×J → ℝ := fun a => cutTerm (fun _ _ => false) rowU colU 0 0 z 0 a.1 a.2
    have hsum : (∑ a, f a)=0 := by
      rw [Fintype.sum_prod_type]
      apply cut_sum_zero
      · intro i hi
        simpa only [rowDifference,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero]
          using hr i (hnonroot (.inl i) hi)
      · intro j hj
        simpa only [columnDifference,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero]
          using hc j (hnonroot (.inr j) hj)
    have hother : ∀ a : I×J, a≠(i₀,j₀) → f a=0 := by
      rintro ⟨i,j⟩ hne
      by_cases hij : T.Adj (.inl i) (.inr j)
      · have he : rowU i=colU j := side_eq_of_tree_edge T t r hij
          (fun h => hne (cell_edge_injective h))
        simp [f,cutTerm,he]
      · simp [f,cutTerm,hsupport i j hij]
    have hisolate : (∑ a, f a)=f (i₀,j₀) := by
      apply Finset.sum_eq_single (i₀,j₀)
      · intro a _ hne
        exact hother a hne
      · simp
    rw [hisolate] at hsum
    have habs : |f (i₀,j₀)|=|z i₀ j₀| := by
      simp only [f,cutTerm,Bool.false_eq_true,ite_false,Pi.zero_apply,sub_zero,
        abs_mul,abs_indicator_sub hcross',one_mul]
    rw [hsum,abs_zero] at habs
    exact abs_eq_zero.mp habs.symm
  · exact hsupport i₀ j₀ ht

/-- The explicit integral root-path solution has no hidden multiplicity:
every integral table supported on the tree and satisfying its nonroot
margin equations equals that solution. -/
theorem tableCompletion_unique (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (hT : T.IsAcyclic)
    (r : I → ℤ) (c : J → ℤ) (z : I → J → ℤ)
    (hsupport : ∀ i j, ¬T.Adj (.inl i) (.inr j) → z i j=0)
    (hr : ∀ i, Sum.inl i≠componentRoot T (.inl i) → (∑ j, z i j)=r i)
    (hc : ∀ j, Sum.inr j≠componentRoot T (.inr j) → (∑ i, z i j)=c j) :
    z=tableCompletion T r c := by
  let δ : I → J → ℝ := fun i j => (z i j:ℝ)-tableCompletion T r c i j
  have hz := zero_of_nonroot_sums T hT δ (by
    intro i j hij
    simp only [δ,hsupport i j hij,Int.cast_zero,tableCompletion_supported T r c i j hij,sub_self])
    (by
      intro i hi
      have h := tableCompletion_row small T hTG r c i hi
      dsimp [δ]
      rw [Finset.sum_sub_distrib,← Int.cast_sum,← Int.cast_sum,hr i hi,h,sub_self])
    (by
      intro j hj
      have h := tableCompletion_column small T hTG r c j hj
      dsimp [δ]
      rw [Finset.sum_sub_distrib,← Int.cast_sum,← Int.cast_sum,hc j hj,h,sub_self])
  funext i j
  have he : (z i j:ℝ)=(tableCompletion T r c i j:ℝ) := sub_eq_zero.mp (hz i j)
  exact_mod_cast he

theorem exists_unique_integral_completion (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (hT : T.IsAcyclic) (r : I → ℤ) (c : J → ℤ) :
    ∃! z : I → J → ℤ,
      (∀ i j, ¬T.Adj (.inl i) (.inr j) → z i j=0) ∧
      (∀ i, Sum.inl i≠componentRoot T (.inl i) → (∑ j, z i j)=r i) ∧
      (∀ j, Sum.inr j≠componentRoot T (.inr j) → (∑ i, z i j)=c j) := by
  refine ⟨tableCompletion T r c,
    ⟨tableCompletion_supported T r c,tableCompletion_row small T hTG r c,
      tableCompletion_column small T hTG r c⟩,?_⟩
  intro z hz
  exact tableCompletion_unique small T hTG hT r c z hz.1 hz.2.1 hz.2.2

end ContingencyTables.GraphCompletionUnique

end OAI
