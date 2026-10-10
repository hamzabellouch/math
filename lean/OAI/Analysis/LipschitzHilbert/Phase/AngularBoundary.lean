import OAI.Analysis.LipschitzHilbert.Phase.AngularGeometry
import OAI.Analysis.LipschitzHilbert.Phase.AngularConservation

namespace OAI

/-! Boundary masses formed from actual top sets in a common angular ancestor. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_eq_of_add (g : AngularGrid) (base steps : ℕ) {s t : ℝ}
    (h : g.index (base + steps) s = g.index (base + steps) t) :
    g.index base s = g.index base t := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    rw [← g.index_parent (base + steps) s, ← g.index_parent (base + steps) t]
    simpa only [Nat.add_succ] using congrArg (fun a : ℤ => a / g.branching) h

theorem index_eq_of_le (g : AngularGrid) {base level : ℕ} (hle : base ≤ level)
    {s t : ℝ} (h : g.index level s = g.index level t) :
    g.index base s = g.index base t := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.index_eq_of_add base steps h

theorem eligible_of_add (g : AngularGrid) {cutoff precision : ℝ}
    (hp : 0 ≤ precision) (base steps : ℕ)
    (h : g.eligible cutoff precision (base + steps)) :
    g.eligible cutoff precision base := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    exact g.eligible_parent hp (base + steps) (by simpa only [Nat.add_succ] using h)

theorem eligible_of_le (g : AngularGrid) {cutoff precision : ℝ} (hp : 0 ≤ precision)
    {base level : ℕ} (hle : base ≤ level) (h : g.eligible cutoff precision level) :
    g.eligible cutoff precision base := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.eligible_of_add hp base steps h

/-- Tops in a descendant cell remain eligible and lie in its actual ancestor. -/
theorem cellTops_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  intro i hi
  obtain ⟨hit, hindex, he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  exact (g.mem_cellTops _ _ _ _ _ _ _).2
    ⟨hit, g.index_eq_of_le hle hindex, g.eligible_of_le (hp i hit) hle he⟩

/-- The extra tops come from nearby next-level cells outside the immediate
parent, and all belong to the same block ancestor. -/
def outsideNearTops (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) : Finset ι := by
  classical
  exact (g.cellTops tops slope precision cutoff base (g.index base s)).filter fun i =>
    g.eligible cutoff (precision i) (level + 1) ∧
    g.neighbors (level + 1) gap (g.index (level + 1) s) (g.index (level + 1) (slope i)) ∧
    g.index level (slope i) ≠ g.index level s

def boundaryTops (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) : Finset ι := by
  classical
  exact g.cellTops tops slope precision cutoff level (g.index level s) ∪
    g.outsideNearTops tops slope precision cutoff base level gap s

theorem parent_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  exact Finset.subset_union_left

theorem boundary_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) :
    g.boundaryTops tops slope precision cutoff base level gap s ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  classical
  apply Finset.union_subset
  · exact g.cellTops_subset_ancestor tops slope precision cutoff hp hle s
  · exact Finset.filter_subset _ _

/-- Each neighboring child within the block ancestor is fully included in
this boundary mass. This is the inclusion used by weighted selection. -/
theorem neighbor_cell_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s t : ℝ)
    (hancestor : g.index base t = g.index base s)
    (hnear : g.neighbors (level + 1) gap (g.index (level + 1) s) (g.index (level + 1) t)) :
    g.cellTops tops slope precision cutoff (level + 1) (g.index (level + 1) t) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  intro i hi
  have ht := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  by_cases hparent : g.index level (slope i) = g.index level s
  · apply Finset.mem_union_left
    exact (g.mem_cellTops _ _ _ _ _ _ _).2
      ⟨ht.1, hparent, g.eligible_parent (hp i ht.1) level ht.2.2⟩
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨?_, ht.2.2, ?_, hparent⟩
    · have ha := g.cellTops_subset_ancestor tops slope precision cutoff hp
        (hle.trans (Nat.le_succ level)) t hi
      simpa only [hancestor] using ha
    · simpa only [ht.2.1] using hnear

def boundaryMass (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (base level : ℕ) (gap s : ℝ) (x : X) : ℝ :=
  ∑ i ∈ g.boundaryTops tops slope precision cutoff base level gap s, weight i x

/-- The union defining the boundary has no double counting. -/
theorem boundary_mass_eq (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (base level : ℕ) (gap s : ℝ) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.mass tops slope precision cutoff weight level (g.index level s) x +
      ∑ i ∈ g.outsideNearTops tops slope precision cutoff base level gap s, weight i x := by
  classical
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro i hi hnear
  have hparent := ((g.mem_cellTops _ _ _ _ _ _ _).1 hi).2.1
  exact (Finset.mem_filter.mp hnear).2.2.2 hparent

/-- The immediate child, parent, boundary and block ancestor have ordered masses. -/
theorem boundary_mass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) (g.index (level + 1) s) x ≤
        g.mass tops slope precision cutoff weight level (g.index level s) x ∧
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
        g.boundaryMass tops slope precision cutoff weight base level gap s x ∧
    g.boundaryMass tops slope precision cutoff weight base level gap s x ≤
        g.mass tops slope precision cutoff weight base (g.index base s) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := g.mass_le_parent tops slope precision cutoff weight hp hw level
      (g.index (level + 1) s) x
    simpa only [g.index_parent] using h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.parent_subset_boundary tops slope precision cutoff base level gap s)
      (fun i _ _ => hw i x)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.boundary_subset_ancestor tops slope precision cutoff hp hle gap s)
      (fun i _ _ => hw i x)

/-- Distinct angular cells have disjoint eligible top sets. -/
theorem cellTops_disjoint (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (level : ℕ) {a b : ℤ} (hab : a ≠ b) :
    Disjoint (g.cellTops tops slope precision cutoff level a)
      (g.cellTops tops slope precision cutoff level b) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i ha hb
  exact hab (((g.mem_cellTops _ _ _ _ _ _ _).1 ha).2.1.symm.trans
    ((g.mem_cellTops _ _ _ _ _ _ _).1 hb).2.1)

/-- A finite collection of child cells included in the boundary consumes
at most its mass. In particular this pays for a closed graph neighborhood. -/
theorem sum_cell_mass_le_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hw : ∀ i x, 0 ≤ weight i x) (base level : ℕ) (gap s : ℝ) (cells : Finset ℤ)
    (hsub : ∀ c ∈ cells, g.cellTops tops slope precision cutoff (level + 1) c ⊆
      g.boundaryTops tops slope precision cutoff base level gap s) (x : X) :
    (∑ c ∈ cells, g.mass tops slope precision cutoff weight (level + 1) c x) ≤
      g.boundaryMass tops slope precision cutoff weight base level gap s x := by
  classical
  have hdisjoint : (cells : Set ℤ).PairwiseDisjoint
      (g.cellTops tops slope precision cutoff (level + 1)) := by
    intro a _ b _ hab
    exact g.cellTops_disjoint tops slope precision cutoff (level + 1) hab
  change (∑ c ∈ cells, ∑ i ∈ g.cellTops tops slope precision cutoff (level + 1) c,
    weight i x) ≤ _
  rw [← Finset.sum_biUnion hdisjoint]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.biUnion_subset.mpr hsub)
    (fun i _ _ => hw i x)

end LipschitzHilbert.AngularGrid

end

end OAI
