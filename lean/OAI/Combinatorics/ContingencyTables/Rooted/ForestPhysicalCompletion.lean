import OAI.Combinatorics.ContingencyTables.Transport.GraphCompletionCounts

namespace OAI

/-!
# The companion's actual small/free profiles and tree intervals

Residual margins subtract the two separate small views and the fixed
free values. The integral graph completion satisfies every nonroot line.
The maximum-forest cut bound then supplies, rather than assumes, the
physical tree interval used by the signature/count marginal.
-/

namespace ContingencyTables.ForestPhysicalCompletion

open scoped BigOperators Classical
open SimpleGraph
open ForestCapacity GraphIntegralCompletion GraphCompletionCounts

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def fixedRow (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (x free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if small i j then x i j else if T.Adj (.inl i) (.inr j) then 0 else free i j

noncomputable def fixedColumn (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (q free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if small i j then q i j else if T.Adj (.inl i) (.inr j) then 0 else free i j

noncomputable def rowResidual (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (x free : I → J → ℤ) (i : I) : ℤ :=
  r i-∑ j, fixedRow small T x free i j

noncomputable def columnResidual (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (c : J → ℤ) (q free : I → J → ℤ) (j : J) : ℤ :=
  c j-∑ i, fixedColumn small T q free i j

noncomputable def solved (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) : I → J → ℤ :=
  tableCompletion T (rowResidual small T r x free) (columnResidual small T c q free)

noncomputable def completed (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ) (i : I) (j : J) : ℤ :=
  if T.Adj (.inl i) (.inr j) then solved small T r c x q free i j else free i j

lemma row_pointwise (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ)
    (i : I) (j : J) :
    (if small i j then x i j else completed small T r c x q free i j)=
      solved small T r c x q free i j+fixedRow small T x free i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,completed,ht,ite_true,fixedRow,add_zero]
  · have hz : solved small T r c x q free i j=0 := tableCompletion_supported T _ _ i j ht
    simp only [completed,ht,ite_false,hz,zero_add,fixedRow]

lemma column_pointwise (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ)
    (i : I) (j : J) :
    (if small i j then q i j else completed small T r c x q free i j)=
      solved small T r c x q free i j+fixedColumn small T q free i j := by
  by_cases ht : T.Adj (.inl i) (.inr j)
  · have hs : small i j=false := hTG ht
    simp only [hs,Bool.false_eq_true,ite_false,completed,ht,ite_true,fixedColumn,add_zero]
  · have hz : solved small T r c x q free i j=0 := tableCompletion_supported T _ _ i j ht
    simp only [completed,ht,ite_false,hz,zero_add,fixedColumn]

lemma row_completed_sum (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ)
    (i : I) (hi : Sum.inl i≠componentRoot T (.inl i)) :
    (∑ j, if small i j then x i j else completed small T r c x q free i j)=r i := by
  simp_rw [row_pointwise small T hTG r c x q free]
  rw [Finset.sum_add_distrib,show (∑ j, solved small T r c x q free i j)=
    rowResidual small T r x free i from tableCompletion_row small T hTG _ _ i hi]
  exact sub_add_cancel _ _

lemma column_completed_sum (small : I → J → Bool) (T : SimpleGraph (I⊕J))
    (hTG : T≤cellGraph small) (r : I → ℤ) (c : J → ℤ) (x q free : I → J → ℤ)
    (j : J) (hj : Sum.inr j≠componentRoot T (.inr j)) :
    (∑ i, if small i j then q i j else completed small T r c x q free i j)=c j := by
  simp_rw [column_pointwise small T hTG r c x q free]
  rw [Finset.sum_add_distrib,show (∑ i, solved small T r c x q free i j)=
    columnResidual small T c q free j from tableCompletion_column small T hTG _ _ j hj]
  exact sub_add_cancel _ _

omit [Fintype I] [Fintype J] in
lemma nonroot_of_root_component (T : SimpleGraph (I⊕J)) (u v : I⊕J)
    (h : T.Reachable (componentRoot T u) v) (hv : v≠componentRoot T u) :
    v≠componentRoot T v := by
  have he : componentRoot T v=componentRoot T u := by
    rw [← componentRoot_constant T h,componentRoot_idempotent]
  simpa only [he] using hv

/-- The completion interval holds for the literal residual
margin equations, including every box-valid unbalanced small profile. -/
theorem solved_in_intervals (small : I → J → Bool) (b : I → J → ℕ)
    (T : SimpleGraph (I⊕J)) (hTG : T≤cellGraph small) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph (I⊕J), F≤cellGraph small → F.IsAcyclic →
      MaximumForest.weight F (capacity b)≤MaximumForest.weight T (capacity b))
    (r : I → ℤ) (c : J → ℤ) (x q free X : I → J → ℤ) (d W : ℕ)
    (hd : 1≤d) (hcard : Fintype.card I*Fintype.card J≤d)
    (hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j)
    (hsmall : ∀ i j, small i j=true → b i j<W ∧
      (0≤x i j ∧ x i j≤b i j) ∧ (0≤q i j ∧ q i j≤b i j))
    (hfree : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) →
      0≤free i j ∧ free i j≤b i j)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hXr : ∀ i, (∑ j, X i j)=r i) (hXc : ∀ j, (∑ i, X i j)=c j) :
    ∀ i j, T.Adj (.inl i) (.inr j) →
      -((10*d*b i j:ℕ):ℤ) ≤ solved small T r c x q free i j ∧
        solved small T r c x q free i j≤(10*d*b i j:ℕ) := by
  intro i₀ j₀ ht
  let root := componentRoot T (.inl i₀)
  have hb := completion_interval small b T hTG hT hmax i₀ j₀ ht root
    (componentRoot_reachable T (.inl i₀)).symm
    (fun i j => (x i j:ℝ)) (fun i j => (q i j:ℝ))
    (fun i j => (completed small T r c x q free i j:ℝ)) (fun i j => (X i j:ℝ))
    (d:ℝ) W (by exact_mod_cast hd) (by exact_mod_cast hcard) hlarge
    (by
      intro i j hs
      exact ⟨(hsmall i j hs).1,by exact_mod_cast (hsmall i j hs).2.1,
        by exact_mod_cast (hsmall i j hs).2.2⟩)
    (by intro i j; exact_mod_cast hX i j)
    (by
      intro i j hs htree
      have hn : ¬T.Adj (.inl i) (.inr j) := by
        simpa only [treeCell,decide_eq_false_iff_not] using htree
      simp only [completed,hn,ite_false]
      have hf := hfree i j hs hn
      constructor
      · exact_mod_cast hf.1
      · have hcast : (free i j:ℝ)≤(b i j:ℝ) := by exact_mod_cast hf.2
        linarith)
    (by
      intro i hcomp hi
      have hrow := row_completed_sum small T hTG r c x q free i
        (nonroot_of_root_component T (.inl i₀) (.inl i) hcomp hi)
      have hrowR : (∑ j, if small i j then (x i j:ℝ) else
          (completed small T r c x q free i j:ℝ))=(r i:ℝ) := by exact_mod_cast hrow
      have hXR : (∑ j, (X i j:ℝ))=(r i:ℝ) := by exact_mod_cast hXr i
      unfold ForestCut.rowDifference
      calc
        _=(∑ j, if small i j then (x i j:ℝ) else
          (completed small T r c x q free i j:ℝ))-(∑ j, (X i j:ℝ)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> rfl
        _=0 := by rw [hrowR,hXR,sub_self])
    (by
      intro j hcomp hj
      have hcol := column_completed_sum small T hTG r c x q free j
        (nonroot_of_root_component T (.inl i₀) (.inr j) hcomp hj)
      have hcolR : (∑ i, if small i j then (q i j:ℝ) else
          (completed small T r c x q free i j:ℝ))=(c j:ℝ) := by exact_mod_cast hcol
      have hXC : (∑ i, (X i j:ℝ))=(c j:ℝ) := by exact_mod_cast hXc j
      unfold ForestCut.columnDifference
      calc
        _=(∑ i, if small i j then (q i j:ℝ) else
          (completed small T r c x q free i j:ℝ))-(∑ i, (X i j:ℝ)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> rfl
        _=0 := by rw [hcolR,hXC,sub_self])
  simp only [completed,ht,ite_true] at hb
  constructor
  · have hlow : (-10:ℤ)*(d:ℤ)*(b i₀ j₀:ℤ) ≤ solved small T r c x q free i₀ j₀ := by
      exact_mod_cast hb.1
    convert hlow using 1
    push_cast
    ring
  · exact_mod_cast hb.2

/-- For the literal small/free residual margins, the equality-limit
sum over the prescribed tree intervals retains exactly one term, with
precisely the weight of the source's solved tree values. -/
theorem tree_indicator_sum (small : I → J → Bool) (b : I → J → ℕ)
    (T : SimpleGraph (I⊕J)) (hTG : T≤cellGraph small) (hT : T.IsAcyclic)
    (hmax : ∀ F : SimpleGraph (I⊕J), F≤cellGraph small → F.IsAcyclic →
      MaximumForest.weight F (capacity b)≤MaximumForest.weight T (capacity b))
    (r : I → ℤ) (c : J → ℤ) (x q free X : I → J → ℤ) (d W : ℕ)
    (hd : 1≤d) (hcard : Fintype.card I*Fintype.card J≤d)
    (hlarge : ∀ i j, small i j=false → W≤b i j ∧ 1≤b i j)
    (hsmall : ∀ i j, small i j=true → b i j<W ∧
      (0≤x i j ∧ x i j≤b i j) ∧ (0≤q i j ∧ q i j≤b i j))
    (hfree : ∀ i j, small i j=false → ¬T.Adj (.inl i) (.inr j) →
      0≤free i j ∧ free i j≤b i j)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hXr : ∀ i, (∑ j, X i j)=r i) (hXc : ∀ j, (∑ i, X i j)=c j)
    (weight : (I → J → ℤ) → ℝ) :
    (∑ a : TreeIndex T d b,
      if NonrootMargins T (rowResidual small T r x free) (columnResidual small T c q free)
        (physical T d b a) then weight (physical T d b a) else 0)=
      weight (solved small T r c x q free) := by
  exact weighted_completion_sum small T hTG hT (rowResidual small T r x free)
    (columnResidual small T c q free) d b
    (solved_in_intervals small b T hTG hT hmax r c x q free X d W hd hcard hlarge
      hsmall hfree hX hXr hXc) weight

end ContingencyTables.ForestPhysicalCompletion

end OAI
