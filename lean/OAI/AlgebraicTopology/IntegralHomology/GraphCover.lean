import OAI.AlgebraicTopology.IntegralHomology.AffineAvoidance

namespace OAI

noncomputable section

namespace Kaplansky

/-! Projective graph denominators, intersections, and finite graph covers. -/

section
open Set
namespace ComplexGrassmann

theorem horizontalOne_eq_smul (v : GraphHorizontal 1) :
    v = v 0 • (fun _ => (1 : ℂ)) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi]

/-- An actual complex endomorphism of a one-dimensional horizontal
space is invertible exactly when its scalar coefficient is nonzero. -/
theorem horizontalOne_isUnit_iff (L : GraphHorizontal 1 →L[ℂ] GraphHorizontal 1) :
    IsUnit L ↔ L (fun _ => 1) 0 ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have happ (v : GraphHorizontal 1) (i : Fin 1) :
      L v i = v 0 * L (fun _ => 1) 0 := by
    have h := congrArg (fun v : GraphHorizontal 1 => L v i) (horizontalOne_eq_smul v)
    rw [map_smul] at h
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h
  constructor
  · intro h hz
    have he : L (fun _ => 1) = L 0 := by
      ext i
      rw [happ, hz]
      simp
    have he' := congrFun (h.1 he) 0
    exact one_ne_zero he'
  · intro hz
    constructor
    · intro v w h
      have he := congrFun h 0
      rw [happ v 0, happ w 0] at he
      have he' := mul_right_cancel₀ hz he
      rw [horizontalOne_eq_smul v, horizontalOne_eq_smul w, he']
    · intro w
      refine ⟨fun _ => w 0 / L (fun _ => 1) 0, ?_⟩
      ext i
      rw [happ, div_mul_cancel₀ _ hz]
      exact congrArg w (Subsingleton.elim _ _)

variable {k : ℕ}

/-- The variable part of the graph-overlap denominator. -/
def graphDenominatorLinear (F G : GraphFrame 1 k) : GraphSlope 1 k →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A => (G (F.symm (0,A (fun _ => 1)))).1 0
    map_add' := by
      intro A B
      have h : ((0 : GraphHorizontal 1),(A+B) (fun _ => 1)) =
          (0,A (fun _ => 1)) + (0,B (fun _ => 1)) := by ext <;> simp
      rw [h, map_add, map_add]
      rfl
    map_smul' := by
      intro c A
      have h : ((0 : GraphHorizontal 1),(c • A) (fun _ => 1)) =
          c • (0,A (fun _ => 1)) := by ext <;> simp
      rw [h, map_smul, map_smul]
      rfl }

def graphDenominatorConstant (F G : GraphFrame 1 k) : ℂ :=
  (G (F.symm ((fun _ => 1),0))).1 0

theorem graphDenominator_eq (F G : GraphFrame 1 k) (A : GraphSlope 1 k) :
    graphTop F G A (fun _ => 1) 0 =
      graphDenominatorLinear F G A + graphDenominatorConstant F G := by
  rw [graphTop_apply]
  have h : ((fun _ : Fin 1 => (1 : ℂ)),A (fun _ => 1)) =
      (0,A (fun _ => 1)) + ((fun _ => 1),0) := by ext <;> simp
  rw [h, map_add, map_add]
  rfl

/-- The actual projective overlap is precisely the complement of an
affine scalar zero set, for arbitrary complex graph frames. -/
theorem projective_inGraphChart_iff_denominator (F G : GraphFrame 1 k) (A : GraphSlope 1 k) :
    InGraphChart G (slopePoint F A).val ↔
      graphDenominatorLinear F G A + graphDenominatorConstant F G ≠ 0 := by
  change InGraphChart G (graphPlane F A.toLinearMap) ↔ _
  rw [inGraphChart_iff_unit, horizontalOne_isUnit_iff, graphDenominator_eq]

end ComplexGrassmann

end

section
open Set Topology
namespace ComplexGrassmann
variable {ι J : Type} [Fintype ι] [Fintype J] (K : ι → ℕ)

def projectiveProductGraphChart (F : ∀ i, GraphFrame 1 (K i)) :
    OpenPartialHomeomorph (ProjectiveProduct K) (ProjectiveProductModel K) :=
  OpenPartialHomeomorph.pi (fun i => grassmannChart (F i))

theorem projectiveProductGraphChart_target (F : ∀ i, GraphFrame 1 (K i)) :
    (projectiveProductGraphChart K F).target = univ := by
  ext A
  simp [projectiveProductGraphChart]

def projectiveProductGraphHomeomorph (F : ∀ i, GraphFrame 1 (K i)) :
    (projectiveProductGraphChart K F).source ≃ₜ ProjectiveProductModel K :=
  (projectiveProductGraphChart K F).toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr (projectiveProductGraphChart_target K F)).trans (Homeomorph.Set.univ _))

theorem projectiveProductGraphHomeomorph_symm_apply (F : ∀ i, GraphFrame 1 (K i))
    (A : ProjectiveProductModel K) (i : ι) :
    ((projectiveProductGraphHomeomorph K F).symm A).val i = slopePoint (F i) (A i) := rfl

def productGraphDenominatorLinear (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) (ji : J × ι) : ProjectiveProductModel K →L[ℝ] ℂ :=
  ((graphDenominatorLinear (F ji.2) (G ji.1 ji.2)).restrictScalars ℝ).comp
    (ContinuousLinearMap.proj ji.2)

def productGraphDenominatorConstant (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) (ji : J × ι) : ℂ :=
  graphDenominatorConstant (F ji.2) (G ji.1 ji.2)

omit [Fintype J] in
/-- Simultaneous membership in any finite family of actual graph charts
is exactly a finite affine nonvanishing condition in a fixed graph chart. -/
theorem productGraph_multi_overlap_iff (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) (A : ProjectiveProductModel K) :
    (∀ j, ((projectiveProductGraphHomeomorph K F).symm A).val ∈
      (projectiveProductGraphChart K (G j)).source) ↔
    A ∈ affineAvoidanceSet (productGraphDenominatorLinear K F G)
      (productGraphDenominatorConstant K F G) := by
  change (∀ j, ∀ i ∈ (univ : Set ι), InGraphChart (G j i)
      (slopePoint (F i) (A i)).val) ↔
    ∀ ji : J × ι, graphDenominatorLinear (F ji.2) (G ji.1 ji.2) (A ji.2) +
      graphDenominatorConstant (F ji.2) (G ji.1 ji.2) ≠ 0
  simp only [mem_univ, forall_true_left, projective_inGraphChart_iff_denominator]
  exact ⟨fun h ji => h ji.1 ji.2, fun h j i => h (j,i)⟩

def projectiveProductGraphIntersection (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) : Set (ProjectiveProduct K) :=
  (projectiveProductGraphChart K F).source ∩ ⋂ j, (projectiveProductGraphChart K (G j)).source

/-- Actual iterated graph-chart intersections, with their subspace
topology, have the explicit affine-complement coordinates. -/
def projectiveProductGraphIntersectionHomeomorph (F : ∀ i, GraphFrame 1 (K i))
    (G : J → ∀ i, GraphFrame 1 (K i)) :
    projectiveProductGraphIntersection K F G ≃ₜ
      affineAvoidanceSet (productGraphDenominatorLinear K F G)
        (productGraphDenominatorConstant K F G) :=
  (subspaceSubsetHomeomorph (projectiveProductGraphIntersection K F G)
    (projectiveProductGraphChart K F).source inter_subset_left).symm.trans
    ((projectiveProductGraphHomeomorph K F).subtype
      (q := fun A => A ∈ affineAvoidanceSet (productGraphDenominatorLinear K F G)
        (productGraphDenominatorConstant K F G)) (fun P => by
      have h := productGraph_multi_overlap_iff K F G (projectiveProductGraphHomeomorph K F P)
      rw [Homeomorph.symm_apply_apply] at h
      change (P.val ∈ (projectiveProductGraphChart K F).source ∧
        P.val ∈ ⋂ j, (projectiveProductGraphChart K (G j)).source) ↔ _
      simpa only [P.property, true_and, mem_iInter] using h))

end ComplexGrassmann

end

open Set
namespace ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

theorem projectiveProductGraphCharts_cover :
    (⋃ F : ∀ i, GraphFrame 1 (K i), (projectiveProductGraphChart K F).source) = univ := by
  ext P
  simp only [mem_iUnion, mem_univ, iff_true]
  choose F hF using fun i => grassmann_atlas_covers (P i)
  exact ⟨F,fun i _ => hF i⟩

/-- Compactness supplies a genuine finite cover of the actual projective
product by graph charts. Any specified chart can be retained in the cover. -/
theorem projectiveProduct_finiteGraphCover (F₀ : ∀ i, GraphFrame 1 (K i)) :
    ∃ S : Finset (∀ i, GraphFrame 1 (K i)), F₀ ∈ S ∧
      (⋃ F ∈ S, (projectiveProductGraphChart K F).source) = univ := by
  classical
  obtain ⟨S,hS⟩ := isCompact_univ.elim_finite_subcover
    (fun F : ∀ i, GraphFrame 1 (K i) => (projectiveProductGraphChart K F).source)
    (fun F => (projectiveProductGraphChart K F).open_source)
    (by rw [projectiveProductGraphCharts_cover])
  refine ⟨insert F₀ S, by simp, subset_antisymm (subset_univ _) ?_⟩
  intro P hP
  obtain ⟨F,hF,hPF⟩ := mem_iUnion.mp (hS hP) |>.imp fun _ => mem_iUnion.mp
  exact mem_iUnion.mpr ⟨F,mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hF,hPF⟩⟩

end ComplexGrassmann

end Kaplansky

end

end OAI
