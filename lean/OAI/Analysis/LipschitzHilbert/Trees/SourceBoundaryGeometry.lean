import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundaryLocality

namespace OAI

/-! Translation-independent radial masses and the literal distance to the
nearest angular boundary. Eligibility is retained in every radial set. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*}

def boundaryDistance (g : AngularGrid) (level : ℕ) (s : ℝ) : ℝ :=
  min (s-g.left level (g.index level s))
    (g.left level (g.index level s)+g.width level-s)

def nearbyEligibleTops (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (level : ℕ) (radius s : ℝ) : Finset τ :=
  tops.filter fun t => g.eligible cutoff (precision t) level ∧ |slope t-s| < radius

def nearbyEligibleMass (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ) (radius s : ℝ) (x : X) : ℝ :=
  ∑ t ∈ g.nearbyEligibleTops tops slope precision cutoff level radius s, weight t x

theorem boundaryDistance_nonneg (g : AngularGrid) (level : ℕ) (s : ℝ) :
    0 ≤ g.boundaryDistance level s := by
  have hs := g.slope_mem_cell level s
  exact le_min (sub_nonneg.mpr hs.1) (sub_nonneg.mpr hs.2.le)

theorem boundaryDistance_le_half (g : AngularGrid) (level : ℕ) (s : ℝ) :
    g.boundaryDistance level s ≤ g.width level/2 := by
  unfold boundaryDistance
  rcases le_total (s-g.left level (g.index level s)) (g.width level/2) with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem index_eq_of_mem_cell (g : AngularGrid) (level : ℕ) (cell : ℤ) (s : ℝ)
    (hl : g.left level cell ≤ s) (hr : s < g.left level cell+g.width level) :
    g.index level s = cell := by
  have hG : (g.branching:ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((s-g.origin)/g.rootWidth)*(g.branching:ℝ)^level =
      (s-g.origin)/g.width level := by
    unfold width
    field_simp
  rw [index,heq]
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ (g.width_pos level)).mpr
    dsimp only [left] at hl
    nlinarith
  · apply (div_lt_iff₀ (g.width_pos level)).mpr
    dsimp only [left] at hr
    nlinarith

theorem index_eq_of_dist_lt_boundary (g : AngularGrid) (level : ℕ) (s t r : ℝ)
    (hr : r ≤ g.boundaryDistance level s) (hst : |t-s| < r) :
    g.index level t = g.index level s := by
  have hl := hr.trans (min_le_left _ _)
  have hh := hr.trans (min_le_right _ _)
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hst
  exact g.index_eq_of_mem_cell level (g.index level s) t (by linarith) (by linarith)

theorem nearbyEligibleTops_subset_cell (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (level : ℕ) (radius s : ℝ)
    (hr : radius ≤ g.boundaryDistance level s) :
    g.nearbyEligibleTops tops slope precision cutoff level radius s ⊆
      g.cellTops tops slope precision cutoff level (g.index level s) := by
  intro t ht
  obtain ⟨htt,he,hd⟩ := Finset.mem_filter.mp ht
  exact (g.mem_cellTops _ _ _ _ _ _ _).mpr
    ⟨htt,g.index_eq_of_dist_lt_boundary level s (slope t) radius hr hd,he⟩

theorem nearbyEligibleTops_mono (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (level : ℕ) (s : ℝ)
    {r R : ℝ} (hr : r ≤ R) :
    g.nearbyEligibleTops tops slope precision cutoff level r s ⊆
      g.nearbyEligibleTops tops slope precision cutoff level R s := by
  intro t ht
  obtain ⟨htt,he,hd⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨htt,he,hd.trans_le hr⟩

theorem outsideNearTops_subset_radial (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (base level : ℕ) (gap s R : ℝ) (hR : gap+2*g.width (level+1) < R) :
    g.outsideNearTops tops slope precision cutoff base level gap s ⊆
      g.nearbyEligibleTops tops slope precision cutoff level R s := by
  intro t ht
  obtain ⟨hbase,he,hnear,_⟩ := Finset.mem_filter.mp ht
  have htt := ((g.mem_cellTops _ _ _ _ _ _ _).mp hbase).1
  refine Finset.mem_filter.mpr ⟨htt,g.eligible_parent (hp t htt) level he,?_⟩
  rw [abs_sub_comm]
  exact (g.slopes_close_of_neighbors (level+1) gap s (slope t) hnear).trans_lt hR

end LipschitzHilbert.AngularGrid

end

end OAI
