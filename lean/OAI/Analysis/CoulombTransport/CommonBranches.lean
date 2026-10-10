import Mathlib

namespace OAI

universe uE uM uIndex uF

/-!
# Reparametrizing local branches by their common central component

For local homeomorphisms `X,Z` on the parameter component, the central
parametrizations are `X.symm` and `X.symm.trans Z`. Their common source is
open, contains the central base point, and inherits both smooth inverses.
-/

noncomputable section
open Set Metric

namespace Problem356.CommonBranches

variable {E : Type uE} [TopologicalSpace E]

/-- Reparametrization of the second outer branch by the central coordinate. -/
def outer (X Z : OpenPartialHomeomorph E E) : OpenPartialHomeomorph E E :=
  X.symm.trans Z

@[simp] theorem outer_apply (X Z : OpenPartialHomeomorph E E) (x : E) :
    outer X Z x = Z (X.symm x) := rfl

/-- Both local maps being defined at the parameter base point puts the
central image in the source of the reparametrized outer branch. -/
theorem image_mem_outer_source (X Z : OpenPartialHomeomorph E E) {a : E}
    (haX : a ∈ X.source) (haZ : a ∈ Z.source) :
    X a ∈ (outer X Z).source := by
  change X a ∈ X.symm.source ∩ X.symm ⁻¹' Z.source
  refine ⟨X.map_source haX, ?_⟩
  change X.symm (X a) ∈ Z.source
  rw [X.left_inv haX]
  exact haZ

/-- The common source permits both the inverse branch and the second outer
branch, with their expected component containment and inverse identity. -/
theorem outer_source_properties (X Z : OpenPartialHomeomorph E E) {x : E}
    (hx : x ∈ (outer X Z).source) :
    x ∈ X.target ∧ X.symm x ∈ X.source ∧ X.symm x ∈ Z.source ∧
      outer X Z x ∈ Z.target ∧ X (X.symm x) = x := by
  change x ∈ X.symm.source ∩ X.symm ⁻¹' Z.source at hx
  exact ⟨hx.1, X.symm.map_source hx.1, hx.2, Z.map_source hx.2,
    X.right_inv hx.1⟩

/-- Every contact predicate on the original graph transfers to the central
parametrization. This includes both supporting equality and stationarity. -/
theorem contact_reparametrize (X Z : OpenPartialHomeomorph E E)
    {C : E × (E × E) → Prop}
    (hC : ∀ y ∈ X.source, C (X y, (y, Z y))) {x : E}
    (hx : x ∈ (outer X Z).source) :
    C (x, (X.symm x, outer X Z x)) := by
  have hp := outer_source_properties X Z hx
  simpa only [hp.2.2.2.2, outer_apply] using hC (X.symm x) hp.2.1

/-- The four ordered outer branches associated with two local families. -/
def four (X Z : Fin 2 → OpenPartialHomeomorph E E) :
    Fin 4 → OpenPartialHomeomorph E E :=
  ![(X 0).symm, outer (X 0) (Z 0), (X 1).symm, outer (X 1) (Z 1)]

/-- A common domain for both composed branches is a common domain for all
four outer branches, in the indexing used by the smooth marginal construction. -/
theorem subset_four_sources (X Z : Fin 2 → OpenPartialHomeomorph E E)
    {B : Set E} (hB : ∀ i, B ⊆ (outer (X i) (Z i)).source) :
    ∀ j, B ⊆ (four X Z j).source := by
  intro j
  fin_cases j
  · intro x hx
    exact (outer_source_properties (X 0) (Z 0) (hB 0 hx)).1
  · exact hB 0
  · intro x hx
    exact (outer_source_properties (X 1) (Z 1) (hB 1 hx)).1
  · exact hB 1

/-- Image containment in the four prescribed outer components. -/
theorem four_images_subset (X Z : Fin 2 → OpenPartialHomeomorph E E)
    {B : Set E} (hB : ∀ i, B ⊆ (outer (X i) (Z i)).source)
    (P Q : Fin 2 → Set E)
    (hP : ∀ i, (X i).source ⊆ P i) (hQ : ∀ i, (Z i).target ⊆ Q i) :
    ∀ j, four X Z j '' B ⊆ ![P 0, Q 0, P 1, Q 1] j := by
  intro j y hy
  obtain ⟨x, hx, rfl⟩ := hy
  fin_cases j
  · exact hP 0 (outer_source_properties (X 0) (Z 0) (hB 0 hx)).2.1
  · exact hQ 0 (outer_source_properties (X 0) (Z 0) (hB 0 hx)).2.2.2.1
  · exact hP 1 (outer_source_properties (X 1) (Z 1) (hB 1 hx)).2.1
  · exact hQ 1 (outer_source_properties (X 1) (Z 1) (hB 1 hx)).2.2.2.1

section Metric

variable {M : Type uM} [PseudoMetricSpace M]

/-- Finitely many pairs of local branches sharing a central base point admit
one positive-radius central ball on which all inverse parametrizations are
defined. The ball may also be kept inside any prescribed central neighborhood. -/
theorem exists_common_central_ball {ι : Type uIndex} [Finite ι]
    (X Z : ι → OpenPartialHomeomorph M M) (a : ι → M) (x : M)
    (haX : ∀ i, a i ∈ (X i).source) (haZ : ∀ i, a i ∈ (Z i).source)
    (hcenter : ∀ i, X i (a i) = x)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      ∀ i, ball x r ⊆ (outer (X i) (Z i)).source := by
  have hopen : IsOpen (U ∩ ⋂ i, (outer (X i) (Z i)).source) :=
    hU.inter (isOpen_iInter_of_finite fun i => (outer (X i) (Z i)).open_source)
  have hx : x ∈ U ∩ ⋂ i, (outer (X i) (Z i)).source := by
    refine ⟨hxU, mem_iInter.mpr ?_⟩
    intro i
    rw [← hcenter i]
    exact image_mem_outer_source (X i) (Z i) (haX i) (haZ i)
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen x hx
  exact ⟨r, hr, fun y hy => (hsub hy).1,
    fun i y hy => mem_iInter.mp (hsub hy).2 i⟩

/-- The central ball can simultaneously keep the inverse and composed
branches inside arbitrary prescribed outer neighborhoods. Thus shrinking the
global certificate components does not require changing either local chart. -/
theorem exists_common_central_ball_in_components {ι : Type uIndex} [Finite ι]
    (X Z : ι → OpenPartialHomeomorph M M) (a : ι → M) (x : M)
    (haX : ∀ i, a i ∈ (X i).source) (haZ : ∀ i, a i ∈ (Z i).source)
    (hcenter : ∀ i, X i (a i) = x)
    (P Q : ι → Set M) (hP : ∀ i, IsOpen (P i)) (hQ : ∀ i, IsOpen (Q i))
    (haP : ∀ i, a i ∈ P i) (haQ : ∀ i, Z i (a i) ∈ Q i)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      ∀ i, ∀ y ∈ ball x r,
        y ∈ (outer (X i) (Z i)).source ∧
        (X i).symm y ∈ P i ∧ outer (X i) (Z i) y ∈ Q i := by
  have hbase : ∀ i, x ∈ (outer (X i) (Z i)).source := by
    intro i
    rw [← hcenter i]
    exact image_mem_outer_source (X i) (Z i) (haX i) (haZ i)
  have hinv : ∀ i, (X i).symm x = a i := by
    intro i
    rw [← hcenter i, (X i).left_inv (haX i)]
  have houter : ∀ i, outer (X i) (Z i) x = Z i (a i) := by
    intro i
    rw [outer_apply, hinv i]
  have hnear : ∀ i, ∀ᶠ y in nhds x,
      y ∈ (outer (X i) (Z i)).source ∧
      (X i).symm y ∈ P i ∧ outer (X i) (Z i) y ∈ Q i := by
    intro i
    have hys : x ∈ (X i).symm.source :=
      (outer_source_properties (X i) (Z i) (hbase i)).1
    have hyP := ((X i).symm.continuousAt hys).eventually
      ((hP i).mem_nhds (by rw [hinv i]; exact haP i))
    have hwQ := ((outer (X i) (Z i)).continuousAt (hbase i)).eventually
      ((hQ i).mem_nhds (by rw [houter i]; exact haQ i))
    have hs : ∀ᶠ y in nhds x, y ∈ (outer (X i) (Z i)).source :=
      (outer (X i) (Z i)).open_source.mem_nhds (hbase i)
    exact hs.and (hyP.and hwQ)
  have hu : ∀ᶠ y in nhds x, y ∈ U := hU.mem_nhds hxU
  have hall := hu.and (Filter.eventually_all.mpr hnear)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  exact ⟨r, hr, fun y hy => (hball y hy).1,
    fun i y hy => (hball y hy).2 i⟩

end Metric

section Smooth

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smoothness of the inverse central branch and original outer branch
makes the reparametrized branch smooth on its actual open source. -/
theorem contDiffOn_outer {n : WithTop ENat} (X Z : OpenPartialHomeomorph F F)
    (hX : ContDiffOn ℝ n X.symm X.target)
    (hZ : ContDiffOn ℝ n Z Z.source) :
    ContDiffOn ℝ n (outer X Z) (outer X Z).source := by
  exact hZ.comp_inter hX

/-- The inverse of the reparametrized branch is smooth on its actual target. -/
theorem contDiffOn_outer_symm {n : WithTop ENat} (X Z : OpenPartialHomeomorph F F)
    (hX : ContDiffOn ℝ n X X.source)
    (hZ : ContDiffOn ℝ n Z.symm Z.target) :
    ContDiffOn ℝ n (outer X Z).symm (outer X Z).target := by
  exact hX.comp_inter hZ

/-- Forward smoothness of all four centrally parametrized branches. -/
theorem contDiffOn_four {n : WithTop ENat}
    (X Z : Fin 2 → OpenPartialHomeomorph F F)
    (hX : ∀ i, ContDiffOn ℝ n (X i).symm (X i).target)
    (hZ : ∀ i, ContDiffOn ℝ n (Z i) (Z i).source) :
    ∀ j, ContDiffOn ℝ n (four X Z j) (four X Z j).source := by
  intro j
  fin_cases j
  · exact hX 0
  · exact contDiffOn_outer (X 0) (Z 0) (hX 0) (hZ 0)
  · exact hX 1
  · exact contDiffOn_outer (X 1) (Z 1) (hX 1) (hZ 1)

/-- Inverse smoothness of all four centrally parametrized branches. -/
theorem contDiffOn_four_symm {n : WithTop ENat}
    (X Z : Fin 2 → OpenPartialHomeomorph F F)
    (hX : ∀ i, ContDiffOn ℝ n (X i) (X i).source)
    (hZ : ∀ i, ContDiffOn ℝ n (Z i).symm (Z i).target) :
    ∀ j, ContDiffOn ℝ n (four X Z j).symm (four X Z j).target := by
  intro j
  fin_cases j
  · exact hX 0
  · exact contDiffOn_outer_symm (X 0) (Z 0) (hX 0) (hZ 0)
  · exact hX 1
  · exact contDiffOn_outer_symm (X 1) (Z 1) (hX 1) (hZ 1)

end Smooth
end Problem356.CommonBranches

end

end OAI
