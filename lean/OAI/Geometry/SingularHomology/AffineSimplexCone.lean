import OAI.Geometry.SingularHomology.SimplexCoordinates
import OAI.Geometry.SingularHomology.AffineSimplexGeometry
import Mathlib.AlgebraicTopology.TopologicalSimplex

namespace OAI

noncomputable section

namespace Problem340.AffineSimplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem realize_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : κ → E) (f : ι → κ) (p : Convexity.StdSimplex ℝ ι) :
    realize v (Convexity.StdSimplex.map f p) = realize (v ∘ f) p :=
  realize_comp_map f v p

theorem realize_delta {n : ℕ} (v : Fin (n + 2) → E) (i : Fin (n + 2))
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    realize v (Convexity.StdSimplex.map (SimplexCategory.δ i) p) = realize (face i v) p := by
  simpa only [SimplexCategory.coe_δ, face] using realize_map v (SimplexCategory.δ i) p

theorem realize_cone_mem {n : ℕ} (x : E) (v : Fin n → E)
    (p : Convexity.StdSimplex ℝ (Fin (n + 1))) {s : Set E} (hs : Convex ℝ s)
    (hx : x ∈ s) (hv : ∀ i, v i ∈ s) : realize (cone x v) p ∈ s := by
  apply realize_mem hs
  intro i
  exact Fin.cases hx hv i

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

abbrev realization {ι : Type*} [Fintype ι] (v : ι → E) := realizeMap v

theorem realization_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : κ → E) (f : ι → κ) :
    (realization v).comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ =
      realization (v ∘ f) := realizeMap_comp_map f v

end Topology

section SimplexValued

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

abbrev simplexRealize (v : ι → Convexity.StdSimplex ℝ κ) (p : Convexity.StdSimplex ℝ ι) :
    Convexity.StdSimplex ℝ κ := simplexRealizeMap v p

abbrev simplexRealization (v : ι → Convexity.StdSimplex ℝ κ) := simplexRealizeMap v

@[simp] theorem simplexRealize_apply (v : ι → Convexity.StdSimplex ℝ κ)
    (p : Convexity.StdSimplex ℝ ι) (j : κ) :
    simplexRealize v p j = ∑ i, p i * v i j := simplexRealizeMap_apply v p j

@[simp] theorem simplexRealize_vertex [DecidableEq ι]
    (v : ι → Convexity.StdSimplex ℝ κ) (i : ι) :
    simplexRealize v (Convexity.StdSimplex.single i) = v i := simplexRealizeMap_vertex v i

theorem simplexRealize_map (v : κ → Convexity.StdSimplex ℝ τ) (f : ι → κ)
    (p : Convexity.StdSimplex ℝ ι) :
    simplexRealize v (Convexity.StdSimplex.map f p) = simplexRealize (v ∘ f) p :=
  DFunLike.congr_fun (simplexRealizeMap_comp_map f v) p

theorem realize_simplexRealize (w : κ → E) (v : ι → Convexity.StdSimplex ℝ κ)
    (p : Convexity.StdSimplex ℝ ι) :
    realize w (simplexRealize v p) = realize (fun i => realize w (v i)) p :=
  realize_simplexRealizeMap w v p

theorem simplexRealize_assoc (w : κ → Convexity.StdSimplex ℝ τ) (v : ι → Convexity.StdSimplex ℝ κ)
    (p : Convexity.StdSimplex ℝ ι) :
    simplexRealize w (simplexRealize v p) =
      simplexRealize (fun i => simplexRealize w (v i)) p := simplexRealizeMap_assoc w v p

@[simp] theorem simplexRealize_vertices [DecidableEq ι] (p : Convexity.StdSimplex ℝ ι) :
    simplexRealize (Convexity.StdSimplex.single (R := ℝ) (X := ι)) p = p := by
  ext j
  simp [simplexRealize_apply, Convexity.StdSimplex.single, Finsupp.single_apply]

theorem continuous_simplexRealize (v : ι → Convexity.StdSimplex ℝ κ) :
    Continuous (simplexRealize v) := (simplexRealizeMap v).continuous

theorem simplexRealization_map (v : κ → Convexity.StdSimplex ℝ τ) (f : ι → κ) :
    (simplexRealization v).comp ⟨Convexity.StdSimplex.map f, Convexity.StdSimplex.continuous_map ℝ f⟩ =
      simplexRealization (v ∘ f) := simplexRealizeMap_comp_map f v

theorem simplexRealization_comp (w : κ → Convexity.StdSimplex ℝ τ) (v : ι → Convexity.StdSimplex ℝ κ) :
    (simplexRealization w).comp (simplexRealization v) =
      simplexRealization (fun i => simplexRealize w (v i)) := by
  apply ContinuousMap.ext
  intro p
  exact simplexRealize_assoc w v p

end SimplexValued

end Problem340.AffineSimplex

end

end OAI
