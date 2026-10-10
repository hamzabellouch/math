import OAI.Analysis.SphereIsometry.PositiveScheduling
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

/-!
A closed invariant convex set from proved finite-prefix growth. The input
growth theorem is instantiated by the geometric common-support argument;
the recursion, positive scheduling, density and invariance are proved here.
-/

noncomputable section

open scoped BigOperators
open Set

namespace Tingley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Ordinary finite-prefix recursion; no admissibility proof enters the data. -/
def recursivePrefix (G : X → X) (v₀ : X) : (n : ℕ) → (Fin (n+1) → X)
  | 0 => fun _ => v₀
  | n+1 => Fin.snoc (α := fun _ : Fin (n+2) => X) (recursivePrefix G v₀ n)
      (G (∑ i, positiveStageWeights n i • recursivePrefix G v₀ n i))

def recursiveVector (G : X → X) (v₀ : X) (n : ℕ) : X :=
  recursivePrefix G v₀ n (Fin.last n)

@[simp] theorem recursiveVector_zero (G : X → X) (v₀ : X) :
    recursiveVector G v₀ 0 = v₀ := rfl

theorem recursivePrefix_eq_vector (G : X → X) (v₀ : X)
    (n : ℕ) (i : Fin (n+1)) :
    recursivePrefix G v₀ n i = recursiveVector G v₀ i.val := by
  induction n with
  | zero =>
      have hi : i.val = 0 := by omega
      simp [recursivePrefix]
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rfl
      · simpa only [recursivePrefix, Fin.snoc_castSucc, Fin.val_castSucc] using ih j

theorem recursiveVector_succ (G : X → X) (v₀ : X) (n : ℕ) :
    recursiveVector G v₀ (n+1) = G (stageMean (recursiveVector G v₀) n) := by
  unfold recursiveVector
  rw [recursivePrefix, Fin.snoc_last]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [recursivePrefix_eq_vector]
  rfl

/-- The geometric one-step conclusion for the invariant convex set. -/
def PositivePrefixGrowth (G : X → X) (E : Set X) : Prop :=
  ∀ (n : ℕ) (p : Fin (n+1) → X) (w : Fin (n+1) → ℝ),
    convexHull ℝ (Set.range p) ⊆ E →
    (∀ i, 0 < w i) → (∑ i, w i = 1) →
    convexHull ℝ (Set.range
      (Fin.snoc (α := fun _ : Fin (n+2) => X) p (G (∑ i, w i • p i)))) ⊆ E

theorem recursivePrefix_hull_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    convexHull ℝ (Set.range (recursivePrefix G v₀ n)) ⊆ E := by
  induction n with
  | zero =>
      have hr : Set.range (recursivePrefix G v₀ 0) = {v₀} := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩; rfl
        · intro hx
          exact ⟨0, hx.symm⟩
      rw [hr, convexHull_singleton]
      exact Set.singleton_subset_iff.mpr hv₀
  | succ n ih =>
      exact hstep n (recursivePrefix G v₀ n) (positiveStageWeights n) ih
        (positiveStageWeights_pos n) (positiveStageWeights_sum n)

theorem recursiveVector_prefix_hull_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    convexHull ℝ (Set.range (fun i : Fin (n+1) => recursiveVector G v₀ i.val)) ⊆ E := by
  have he : (fun i : Fin (n+1) => recursiveVector G v₀ i.val) =
      recursivePrefix G v₀ n := by
    funext i
    exact (recursivePrefix_eq_vector G v₀ n i).symm
  rw [he]
  exact recursivePrefix_hull_subset G E v₀ hv₀ hstep n

theorem recursiveVector_mem (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    recursiveVector G v₀ n ∈ E :=
  recursivePrefix_hull_subset G E v₀ hv₀ hstep n
    (subset_convexHull ℝ _ ⟨Fin.last n, rfl⟩)

theorem recursiveStageMean_mem (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hstep : PositivePrefixGrowth G E) (n : ℕ) :
    stageMean (recursiveVector G v₀) n ∈ E := by
  apply recursiveVector_prefix_hull_subset G E v₀ hv₀ hstep n
  exact mem_convexHull_of_exists_fintype (positiveStageWeights n)
    (fun i : Fin (n+1) => recursiveVector G v₀ i.val)
    (fun i => (positiveStageWeights_pos n i).le) (positiveStageWeights_sum n)
    (fun i => ⟨i, rfl⟩) rfl

/-- The closed convex hull of the one actual recursively constructed sequence. -/
def recursiveConvexSet (G : X → X) (v₀ : X) : Set X :=
  closure (convexHull ℝ (Set.range (recursiveVector G v₀)))

theorem recursiveConvexSet_subset (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hstep : PositivePrefixGrowth G E) :
    recursiveConvexSet G v₀ ⊆ E := by
  apply closure_minimal _ hE
  exact convexHull_range_subset_of_prefixes _ E
    (recursiveVector_prefix_hull_subset G E v₀ hv₀ hstep)

theorem recursiveConvexSet_nonempty (G : X → X) (v₀ : X) :
    (recursiveConvexSet G v₀).Nonempty := by
  refine ⟨recursiveVector G v₀ 0, subset_closure ?_⟩
  exact subset_convexHull ℝ _ ⟨0, rfl⟩

theorem isClosed_recursiveConvexSet (G : X → X) (v₀ : X) :
    IsClosed (recursiveConvexSet G v₀) := isClosed_closure

theorem convex_recursiveConvexSet (G : X → X) (v₀ : X) :
    Convex ℝ (recursiveConvexSet G v₀) := (convex_convexHull ℝ _).closure

theorem recursiveConvexSet_invariant (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hunit : ∀ x ∈ E, ‖x‖ = 1)
    (hG : ContinuousOn G E) (hstep : PositivePrefixGrowth G E) :
    Set.MapsTo G (recursiveConvexSet G v₀) (recursiveConvexSet G v₀) := by
  let v := recursiveVector G v₀
  have hv : ∀ n, ‖v n‖ ≤ (1 : ℝ) :=
    fun n => (hunit _ (recursiveVector_mem G E v₀ hv₀ hstep n)).le
  have hdense : closure (Set.range (stageMean v)) = recursiveConvexSet G v₀ :=
    closure_range_stageMean_eq v 1 (by norm_num) hv
  have himage : Set.MapsTo G (Set.range (stageMean v)) (recursiveConvexSet G v₀) := by
    rintro x ⟨n, rfl⟩
    rw [← recursiveVector_succ G v₀ n]
    exact subset_closure (subset_convexHull ℝ _ ⟨n+1, rfl⟩)
  have hcont : ContinuousOn G (closure (Set.range (stageMean v))) := by
    rw [hdense]
    exact hG.mono (recursiveConvexSet_subset G E v₀ hv₀ hE hstep)
  have h := himage.closure_of_continuousOn hcont
  rw [hdense, (isClosed_recursiveConvexSet G v₀).closure_eq] at h
  exact h

/-- No density or invariant-set premise: both are obtained from the positive recursion. -/
theorem exists_invariant_closed_convex (G : X → X) (E : Set X) (v₀ : X)
    (hv₀ : v₀ ∈ E) (hE : IsClosed E) (hunit : ∀ x ∈ E, ‖x‖ = 1)
    (hG : ContinuousOn G E) (hstep : PositivePrefixGrowth G E) :
    ∃ C : Set X, C.Nonempty ∧ IsClosed C ∧ Bornology.IsBounded C ∧
      Convex ℝ C ∧ C ⊆ E ∧ Set.MapsTo G C C := by
  have hsub := recursiveConvexSet_subset G E v₀ hv₀ hE hstep
  refine ⟨recursiveConvexSet G v₀, recursiveConvexSet_nonempty G v₀,
    isClosed_recursiveConvexSet G v₀, ?_, convex_recursiveConvexSet G v₀, hsub,
    recursiveConvexSet_invariant G E v₀ hv₀ hE hunit hG hstep⟩
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨1, fun x hx => (hunit x (hsub hx)).le⟩

end Tingley

end

end OAI
