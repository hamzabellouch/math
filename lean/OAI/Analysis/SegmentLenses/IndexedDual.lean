import OAI.Analysis.SegmentLenses.IndexedForest

namespace OAI

/-!
# Indexed forest duals and unbounded-height obstructions
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex


section DualIsometries
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def dualTransport (e : E ≃ₗᵢ[ℝ] F) : StrongDual ℝ E ≃ₗᵢ[ℝ] StrongDual ℝ F where
  toLinearEquiv := (e.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toLinearEquiv
  norm_map' f := by
    let g := e.toContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) f
    change ‖g‖ = ‖f‖
    apply le_antisymm
    · apply g.opNorm_le_bound (norm_nonneg f)
      intro y
      change ‖f (e.symm y)‖ ≤ _
      simpa only [e.symm.norm_map] using f.le_opNorm (e.symm y)
    · apply f.opNorm_le_bound (norm_nonneg g)
      intro x
      have h := g.le_opNorm (e x)
      change ‖f (e.symm (e x))‖ ≤ ‖g‖ * ‖e x‖ at h
      simpa only [e.symm_apply_apply, e.norm_map] using h

@[simp] theorem dualTransport_apply (e : E ≃ₗᵢ[ℝ] F) (f : StrongDual ℝ E) (y : F) :
    dualTransport e f y = f (e.symm y) := rfl

end DualIsometries

section L2DualInverse
variable {I : Type*} [DecidableEq I] (E : I → Type*) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

@[simp] theorem l2DualEquiv_symm_apply (f : StrongDual ℝ (L2Sum E)) :
    (l2DualEquiv E).symm f = l2DualRestrictions E f := by
  apply (l2DualEquiv E).injective
  rw [(l2DualEquiv E).apply_symm_apply]
  exact (l2DualPair_restrictions E f).symm

end L2DualInverse

namespace IndexedForest
variable {I : Type*} [DecidableEq I] {height : I → ℕ}
local instance : DecidableEq (Vertex height) := Classical.decEq _
local instance : ∀ i, NormedAddCommGroup (HeightPrimal (height := height) i) := fun _i => inferInstance
local instance : ∀ i, NormedSpace ℝ (HeightPrimal (height := height) i) := fun _i => inferInstance


def dualL2Equiv : X height ≃ₗᵢ[ℝ] L2Sum (fun i => StrongDual ℝ (HeightPrimal (height := height) i)) :=
  (dualTransport (forestL2Equiv (height := height))).trans (l2DualEquiv (HeightPrimal (height := height))).symm

@[simp] theorem dualL2Equiv_apply (f : X height) (i : I) (u : HeightPrimal (height := height) i) :
    dualL2Equiv f i u = f ((forestL2Equiv (height := height)).symm (lp.single 2 i u)) := by
  change ((l2DualEquiv (HeightPrimal (height := height))).symm
    (dualTransport (forestL2Equiv (height := height)) f)) i u = _
  rw [l2DualEquiv_symm_apply]
  rfl

@[simp] theorem dualL2Equiv_on_test (f : X height) (i : I) (u : heightTests (height := height) i) :
    dualL2Equiv f i (u : HeightPrimal (height := height) i) = f (u.val : J height) := by
  rw [dualL2Equiv_apply]
  congr 1
  apply (forestL2Equiv (height := height)).injective
  rw [(forestL2Equiv (height := height)).apply_symm_apply, forestL2Equiv_test,
    forestTestBlocks_of_height]


theorem coordinateSpan_eq_top : coordinateSpan (Vertex height) = ⊤ :=
  coordinateSpan_eq_top_of_reflexive (forest_primal_reflexive (height := height))

theorem separable [Countable I] : TopologicalSpace.SeparableSpace (X height) :=
  fullDual_separable_of_coordinateSpan coordinateSpan_eq_top

end IndexedForest

namespace IndexedForest
variable {I : Type*} [decidableEqI : DecidableEq I] {height : I → ℕ}
local instance : DecidableEq (Vertex height) := Classical.decEq _
section ForestPaths

def forestRoot (h : I) : (Vertex height) := ⟨(h, []), by simp⟩
def forestNode (h : I) (v : List ℕ) (hv : v.length ≤ height h) : (Vertex height) :=
  ⟨(h, v), hv⟩

theorem forest_iic_segment (v : (Vertex height)) : SegmentSystem.isSegment (Finset.Iic v) := by
  have _ := decidableEqI
  apply (IntervalSegments.iff_interval _).mpr
  refine ⟨forestRoot (height := height) v.val.1, v, ⟨rfl, List.nil_prefix⟩, ?_⟩
  intro w
  simp only [Finset.mem_Iic]
  constructor
  · intro h
    exact ⟨⟨h.1.symm, List.nil_prefix⟩, h⟩
  · exact And.right



def forestPath (h : I) (v : List ℕ) : X height :=
  if hv : v.length ≤ height h then segmentFunctional (Finset.Iic (forestNode h v hv)) else 0

@[simp] theorem norm_forestPath (h : I) (v : List ℕ) (hv : v.length ≤ height h) :
    ‖forestPath (height := height) h v‖ = 1 := by
  classical
  rw [forestPath, dite_eq_left hv]
  exact norm_segmentFunctional _ (forest_iic_segment _) ⟨_, Finset.mem_Iic.mpr le_rfl⟩

theorem forestPath_child (h : I) (v : List ℕ) (hv : v.length < height h) (n : ℕ) :
    forestPath h (v ++ [n]) = forestPath h v +
      coordinate (forestNode h (v ++ [n]) (by simp; omega)) := by
  have _ := decidableEqI
  classical
  let a := forestNode h v hv.le
  let b := forestNode h (v ++ [n]) (by simp; omega)
  have he : Finset.Iic b = insert b (Finset.Iic a) := by
    ext w
    simp only [Finset.mem_Iic, Finset.mem_insert]
    change (w.val.1 = h ∧ w.val.2.IsPrefix (v ++ [n])) ↔
      w = b ∨ (w.val.1 = h ∧ w.val.2.IsPrefix v)
    rw [prefix_append_single_iff]
    constructor
    · rintro ⟨hc, hw | hw⟩
      · exact Or.inr ⟨hc, hw⟩
      · exact Or.inl (Subtype.ext (Prod.ext hc hw))
    · rintro (rfl | ⟨hc, hw⟩)
      · exact ⟨rfl, Or.inr rfl⟩
      · exact ⟨hc, Or.inl hw⟩
  have hn : b ∉ Finset.Iic a := by
    intro hx
    have hl := (Finset.mem_Iic.mp hx).2.length_le
    change (v ++ [n]).length ≤ v.length at hl
    simp at hl
  rw [forestPath, dite_eq_left (by simp; omega), forestPath, dite_eq_left hv.le]
  change segmentFunctional (Finset.Iic b) = segmentFunctional (Finset.Iic a) + coordinate b
  rw [he, segmentFunctional, Finset.sum_insert hn, add_comm]
  rfl

theorem forestPath_children_weakly_null (h : I) (v : List ℕ) (hv : v.length < height h) :
    WeaklyNull (fun n => forestPath (height := height) h (v ++ [n]) - forestPath h v) := by
  classical
  have hw := fullDual_distinct_coordinates_weakly_null
    (fun n => forestNode h (v ++ [n]) (by simp; omega)) (by
      intro n m hn
      have hlist := congrArg (fun w : (Vertex height) => w.val.2) hn
      simpa only [forestNode, List.append_cancel_left_eq, List.singleton_inj] using hlist)
  convert hw using 1
  funext n
  rw [forestPath_child h v hv n, add_sub_cancel_left]

end ForestPaths


theorem unbounded_unit_finite_paths (hunbounded : ∀ n : ℕ, ∃ i : I, n ≤ height i) :
    UnitFinitePaths (X height) := by
  intro n hn
  obtain ⟨i, hi⟩ := hunbounded n
  refine ⟨forestPath i, ?_, ?_, ?_⟩
  · intro v hv
    exact norm_forestPath i v (hv.trans hi)
  · intro v hv
    exact forestPath_children_weakly_null i v (hv.trans_le hi)
  · intro v hv k
    rw [forestPath_child i v (hv.trans_le hi) k, add_sub_cancel_left, norm_coordinate]

theorem unbounded_vertices_infinite (hunbounded : ∀ n : ℕ, ∃ i : I, n ≤ height i) :
    Infinite (Vertex height) := by
  have _ := decidableEqI
  obtain ⟨i, hi⟩ := hunbounded 1
  let f : ℕ → Vertex height := fun n => ⟨(i,[n]), by simpa using hi⟩
  apply Infinite.of_injective f
  intro n m h
  have he := congrArg (fun v : Vertex height => v.val.2) h
  simpa only [f, List.singleton_inj] using he


theorem unbounded_equivalent_modulus_zero (hunbounded : ∀ n : ℕ, ∃ i : I, n ≤ height i)
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (e : X height ≃L[ℝ] D)
    {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hlower : ∀ x : X height, a * ‖x‖ ≤ ‖e x‖)
    (hupper : ∀ x : X height, ‖e x‖ ≤ b * ‖x‖)
    (hr : 0 < r) (hrab : r ≤ a/b) : oneSidedModulus D r = 0 := by
  let := unbounded_vertices_infinite hunbounded
  exact equivalent_paths_modulus_zero fullDual_not_finite (unbounded_unit_finite_paths hunbounded)
    e ha hab hlower hupper hr hrab

theorem unbounded_no_equivalent_AUC (hunbounded : ∀ n : ℕ, ∃ i : I, n ≤ height i)
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] (e : X height ≃L[ℝ] D) : ¬ AUC D := by
  let := unbounded_vertices_infinite hunbounded
  exact equivalent_paths_not_auc fullDual_not_finite (unbounded_unit_finite_paths hunbounded) e

end IndexedForest



end SegmentLenses

end

end OAI
