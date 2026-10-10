import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteLinearSymmetries
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-!
# Finite linear symmetry group of a spanning polytope

The support body in the height argument is a convex hull of finitely many
covectors. Preserving that body permutes its extreme points. We prove that
these form a finite spanning set, so the symmetry family is finite.
-/

namespace PolycyclicRecognition

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A finite spanning polytope has finitely many linear symmetries. Its given
generators need not themselves be vertices. -/
theorem finite_polytope_symmetries (s : Finset W)
    (hspan : Submodule.span ℝ (s : Set W) = ⊤) :
    Set.Finite {A : W ≃L[ℝ] W | A '' convexHull ℝ (s : Set W) = convexHull ℝ (s : Set W)} := by
  classical
  let C := convexHull ℝ (s : Set W)
  let V := Set.extremePoints ℝ C
  have hV : V.Finite := s.finite_toSet.subset extremePoints_convexHull_subset
  have hC : convexHull ℝ V = C := by
    calc
      convexHull ℝ V = closure (convexHull ℝ V) := (hV.isClosed_convexHull ℝ).closure_eq.symm
      _ = C := closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
        (convex_convexHull ℝ (s : Set W))
  have hVspan : Submodule.span ℝ (hV.toFinset : Set W) = ⊤ := by
    rw [hV.coe_toFinset]
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    have hxC : x ∈ C := subset_convexHull ℝ (s : Set W) hx
    rw [← hC] at hxC
    exact (convexHull_min (Submodule.subset_span : V ⊆ Submodule.span ℝ V)
      (Submodule.convex _)) hxC
  apply (finite_linear_symmetries hV.toFinset hVspan).subset
  intro A hA v hv
  have himage : A '' V = V := by
    change A '' Set.extremePoints ℝ C = Set.extremePoints ℝ C
    rw [image_extremePoints, hA]
  have hAv : A v ∈ V := himage ▸ Set.mem_image_of_mem A (hV.mem_toFinset.mp hv)
  exact hV.mem_toFinset.mpr hAv

end PolycyclicRecognition

end OAI
