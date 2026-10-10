import OAI.GroupTheory.PolycyclicRecognition.Geometry.HorizontalLinearDerivative
import Mathlib.Analysis.LocallyConvex.Separation

namespace OAI

/-! # Finite convex-orbit constraints extend from dense directions -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

theorem isClosed_mem_finite_convexHull
    {X W I : Type*} [TopologicalSpace X] [Finite I]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : X → W) (hf : Continuous f) (A : I → X → W) (hA : ∀ i, Continuous (A i)) :
    IsClosed {x | f x ∈ convexHull ℝ (range fun i => A i x)} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨l, r, hr, hx'⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range fun i => A i x))
    ((Set.finite_range (fun i => A i x)).isClosed_convexHull (𝕜 := ℝ)) hx
  have he : ∀ᶠ y in 𝓝 x, r < l (f y) :=
    (isOpen_lt continuous_const (l.continuous.comp hf)).mem_nhds hx'
  have ha : ∀ᶠ y in 𝓝 x, ∀ i, l (A i y) < r := by
    apply eventually_all.mpr
    intro i
    exact (isOpen_lt (l.continuous.comp (hA i)) continuous_const).mem_nhds
      (hr _ (subset_convexHull ℝ _ (mem_range_self i)))
  filter_upwards [he, ha] with y hy hay
  intro hmem
  have hbound : l (f y) ≤ r :=
    (convexHull_min (by rintro _ ⟨i, rfl⟩; exact (hay i).le)
      (convex_halfSpace_le l.toLinearMap.isLinear r)) hmem
  exact (not_lt_of_ge hbound) hy

theorem mem_finite_convexHull_of_dense
    {X W I : Type*} [TopologicalSpace X] [Finite I]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : X → W) (hf : Continuous f) (A : I → X → W) (hA : ∀ i, Continuous (A i))
    {S : Set X} (hS : Dense S)
    (h : ∀ x ∈ S, f x ∈ convexHull ℝ (range fun i => A i x)) :
    ∀ x, f x ∈ convexHull ℝ (range fun i => A i x) := by
  have hsub : S ⊆ {x | f x ∈ convexHull ℝ (range fun i => A i x)} := h
  have hc := (isClosed_mem_finite_convexHull f hf A hA).closure_subset_iff.mpr hsub
  intro x
  exact hc (by rw [hS.closure_eq]; trivial)

end PolycyclicRecognition

end

end OAI
