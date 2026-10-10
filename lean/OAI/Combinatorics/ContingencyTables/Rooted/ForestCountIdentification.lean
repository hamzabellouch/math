import OAI.Combinatorics.ContingencyTables.Rooted.ForestAssignmentSplit
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalLargeProfiles
import OAI.Combinatorics.ContingencyTables.Rooted.ForestLargeMarginal

namespace OAI

/-!
# The companion signature marginal is the literal weighted completion count

The physical all-large product is split bijectively into tree and free
assignments. Exact nonroot equations then retain one tree completion per
free assignment, with exactly its root/tree exponential penalty.
-/

namespace ContingencyTables.ForestCountIdentification

open scoped BigOperators Classical
open SimpleGraph LargePairEnumeration PhysicalLargeProfiles
open ForestCapacity GraphCompletionCounts ForestAssignmentSplit ForestLiteralCount

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def smallX (small : I → J → Bool)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then z (⟨(i,j),hs⟩,false) else 0

noncomputable def smallY (small : I → J → Bool)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) (i : I) (j : J) : ℕ :=
  if hs : small i j=true then z (⟨(i,j),hs⟩,true) else 0

omit [Fintype I] [Fintype J] in
lemma split_profile (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b : I → J → ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (a : TreeIndex T d b×FreeIndex small T b) :
    physicalProfile (fun a : I×J => small a.1 a.2) (fun p => width T d b p.1 p.2) z
      ((assignmentSplit small T hTG d b).symm a)=
      profile small T d b (smallX small z) (smallY small z) (freeTable small T b a.2) a.1 := by
  funext u
  rcases u with ⟨⟨i,j⟩,v⟩
  by_cases hs : small i j=true
  · cases v <;> simp [physicalProfile,hs,profile,smallX,smallY]
  · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
    have he := split_cellCount small T hTG d b a ⟨(i,j),hs'⟩
    cases v <;> simp [physicalProfile,hs,profile,he]

private theorem physical_sum_split (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (d : ℕ) (b : I → J → ℕ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (F : (((I×J)×Bool) → ℕ) → ℝ) :
    (∑ a : PhysicalAssignments (fun a : I×J => small a.1 a.2)
      (fun a => width T d b a.1 a.2),
      F (physicalProfile (fun a : I×J => small a.1 a.2) (fun a => width T d b a.1 a.2) z a))=
      ∑ f : FreeIndex small T b, ∑ t : TreeIndex T d b,
        F (profile small T d b (smallX small z) (smallY small z) (freeTable small T b f) t) := by
  have heq := Fintype.sum_equiv (assignmentSplit small T hTG d b)
    (fun a => F (physicalProfile (fun a : I×J => small a.1 a.2)
      (fun a => width T d b a.1 a.2) z a))
    (fun a => F (profile small T d b (smallX small z) (smallY small z) (freeTable small T b a.2) a.1))
    (by
      intro a
      apply congrArg F
      have he := split_profile small T hTG d b z ((assignmentSplit small T hTG d b) a)
      simpa only [Equiv.symm_apply_apply] using he)
  rw [heq,Fintype.sum_prod_type,Finset.sum_comm]

noncomputable def sourceMarginal (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (_d : ℕ) (b : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) : ℝ :=
  ∑ f : FreeIndex small T b, (2:ℝ)^(-alpha*actualPenalty small T b
    (smallX small z) (smallY small z) (freeTable small T b f) r c
    (ForestPhysicalCompletion.solved small T r c
      (fun i j => (smallX small z i j:ℤ))
      (fun i j => ((b i j-smallY small z i j:ℕ):ℤ))
      (fun i j => (freeTable small T b f i j:ℤ))))

theorem sourceMarginal_positive (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b : I → J → ℕ) (r : I → ℤ) (c : J → ℤ) (alpha : ℝ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) :
    0<sourceMarginal small T d b r c alpha z := by
  let f : FreeIndex small T b := fun _ => 0
  unfold sourceMarginal
  apply lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)
  exact Finset.single_le_sum (fun a _ =>
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).le) (Finset.mem_univ f)

/-- At annealing parameter zero the original count is exactly the
product of the free interval lengths. -/
theorem sourceMarginal_zero (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (d : ℕ) (b : I → J → ℕ) (r : I → ℤ) (c : J → ℤ)
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ) :
    sourceMarginal small T d b r c 0 z=
      ∏ a : FreeCell small T, ((b a.val.1 a.val.2+1:ℕ):ℝ) := by
  simp [sourceMarginal,Fintype.card_pi,Nat.cast_prod]

/-- The source's actual free-assignment count is precisely the all-large
physical marginal with its raw removal signature. -/
theorem sourceMarginal_eq_largeMarginal (small : I → J → Bool) (b : I → J → ℕ)
    (T : SimpleGraph (I⊕J)) (hTG : T≤cellGraph small) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph (I⊕J), F≤cellGraph small → F.IsAcyclic →
      MaximumForest.weight F (capacity b)≤MaximumForest.weight T (capacity b))
    (r : I → ℤ) (c : J → ℤ) (X : I → J → ℤ)
    (d W : ℕ) (alpha : ℝ) (hd : 1≤d) (hcard : Fintype.card I*Fintype.card J≤d)
    (hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j)
    (hsmall : ∀ i j, small i j=true → b i j<W)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hXr : ∀ i, (∑ j, X i j)=r i) (hXc : ∀ j, (∑ i, X i j)=c j)
    {n : ℕ} (e : Fin n ≃ LargeCell (fun a : I×J => small a.1 a.2))
    (z : SmallView (fun a : I×J => small a.1 a.2) → ℕ)
    (hz : ∀ u, z u≤b u.1.val.1 u.1.val.2) :
    sourceMarginal small T d b r c alpha z=
      ForestLargeMarginal.largeMarginal (fun a : I×J => small a.1 a.2) T b
        (lower T d b) (width T d b) r c alpha e z := by
  unfold ForestLargeMarginal.largeMarginal
  rw [sum_joined_eq_physical (fun a : I×J => small a.1 a.2)
    (fun a : I×J => width T d b a.1 a.2) e z
    (ForestPenaltyApplication.physicalWeight T b (lower T d b) (width T d b) r c alpha)]
  trans (∑ f : FreeIndex small T b, ∑ t : TreeIndex T d b,
    ForestPenaltyApplication.physicalWeight T b (lower T d b) (width T d b) r c alpha
      (profile small T d b (smallX small z) (smallY small z) (freeTable small T b f) t))
  · unfold sourceMarginal
    have hsmall' : ∀ i j, small i j=true →
        b i j<W ∧ smallX small z i j≤b i j ∧ smallY small z i j≤b i j := by
      intro i j hs
      refine ⟨hsmall i j hs,?_,?_⟩
      · simpa only [smallX,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,false)
      · simpa only [smallY,hs,dite_eq_left] using hz (⟨(i,j),hs⟩,true)
    apply Finset.sum_congr rfl
    intro f _
    exact (literal_tree_sum small b T hTG hT hmax r c (smallX small z) (smallY small z)
      (freeTable small T b f) X d W alpha hd hcard hlarge hsmall'
      (freeTable_bound small T b f) hX hXr hXc).symm

  · convert (physical_sum_split small T hTG d b z
      (ForestPenaltyApplication.physicalWeight T b (lower T d b) (width T d b) r c alpha)).symm using 1
    all_goals
      congr 1
      ext
      simp

end ContingencyTables.ForestCountIdentification

end OAI
