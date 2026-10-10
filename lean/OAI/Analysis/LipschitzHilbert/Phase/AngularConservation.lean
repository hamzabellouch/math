import OAI.Analysis.LipschitzHilbert.Phase.AngularGrid

namespace OAI

/-! Exact finite conservation of angular mass, including tops that stop. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

def continuingTops (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (level : ℕ) (cell : ℤ) : Finset ι := by
  classical
  exact (g.cellTops tops slope precision cutoff level cell).filter
    fun i => g.eligible cutoff (precision i) (level + 1)

def children (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (level : ℕ) (cell : ℤ) : Finset ℤ := by
  classical
  exact (g.continuingTops tops slope precision cutoff level cell).image
    fun i => g.index (level + 1) (slope i)

theorem child_parent (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (level : ℕ) (cell child : ℤ)
    (hchild : child ∈ g.children tops slope precision cutoff level cell) :
    child / (g.branching : ℤ) = cell := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hchild
  have hmem := (g.mem_cellTops _ _ _ _ _ _ _).1 (Finset.mem_filter.mp hi).1
  rw [g.index_parent, hmem.2.1]

theorem continuing_fiber (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i) (level : ℕ) (cell child : ℤ)
    (hparent : child / (g.branching : ℤ) = cell) :
    (g.continuingTops tops slope precision cutoff level cell).filter
      (fun i => g.index (level + 1) (slope i) = child) =
        g.cellTops tops slope precision cutoff (level + 1) child := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨hcont, hindex⟩ := Finset.mem_filter.mp hi
    obtain ⟨hmem, he⟩ := Finset.mem_filter.mp hcont
    have htop := (g.mem_cellTops _ _ _ _ _ _ _).1 hmem
    exact (g.mem_cellTops _ _ _ _ _ _ _).2 ⟨htop.1, hindex, he⟩
  · intro hi
    have htop := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
    have hmem := g.cellTops_subset_parent tops slope precision cutoff hp level child hi
    rw [hparent] at hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, htop.2.2⟩, htop.2.1⟩

/-- The next-level child masses partition precisely the continuing tops. -/
theorem sum_child_mass (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (level : ℕ) (cell : ℤ) (x : X) :
    (∑ child ∈ g.children tops slope precision cutoff level cell,
      g.mass tops slope precision cutoff weight (level + 1) child x) =
        ∑ i ∈ g.continuingTops tops slope precision cutoff level cell, weight i x := by
  classical
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := g.continuingTops tops slope precision cutoff level cell)
    (t := g.children tops slope precision cutoff level cell)
    (fun i hi => Finset.mem_image_of_mem (fun j => g.index (level + 1) (slope j)) hi)
    (fun i => weight i x)
  change (∑ child ∈ (g.continuingTops tops slope precision cutoff level cell).image
    (fun i => g.index (level + 1) (slope i)), _) = _
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro child hchild
  rw [g.continuing_fiber tops slope precision cutoff hp level cell child
    (g.child_parent tops slope precision cutoff level cell child hchild)]
  rfl

/-- The actual parent mass splits into next-level child masses and the
positive weights of tops whose eligibility stops at this level. -/
theorem parent_mass_conservation (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (level : ℕ) (cell : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight level cell x =
      (∑ child ∈ g.children tops slope precision cutoff level cell,
        g.mass tops slope precision cutoff weight (level + 1) child x) +
      ∑ i ∈ (g.cellTops tops slope precision cutoff level cell).filter
        (fun i => ¬g.eligible cutoff (precision i) (level + 1)), weight i x := by
  classical
  rw [g.sum_child_mass tops slope precision cutoff weight hp]
  exact (Finset.sum_filter_add_sum_filter_not
    (g.cellTops tops slope precision cutoff level cell)
    (fun i => g.eligible cutoff (precision i) (level + 1)) (fun i => weight i x)).symm

end LipschitzHilbert.AngularGrid

end

end OAI
