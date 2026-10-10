import OAI.CategoryTheory.Thomason.Simplicial.RealizationTopology

namespace OAI

section

/-! # Positivity after support restriction and epimorphic simplex maps -/

namespace Thomason.Construction.HornBarycentric

open Convexity

noncomputable section

/-- All coordinates on the ordered support are nonzero. -/
theorem supportCoordinates_nonzero {n : ℕ} (x : StdSimplex ℝ (Fin (n+1)))
    (k : Fin (supportLen x+1)) : (supportCoordinates x).weights k ≠ 0 := by
  have he := congrArg (fun p : StdSimplex ℝ (Fin (n+1)) => p.weights (supportMap x k))
    (support_recover x)
  change (supportCoordinates x).weights.mapDomain (supportMap x) (supportMap x k) =
    x.weights (supportMap x k) at he
  rw [Finsupp.mapDomain_apply_of_injective (supportMap x).injective] at he
  rw [he]
  exact Finsupp.mem_support_iff.mp (supportMap_mem x k)

/-- A surjective vertex map preserves nonvanishing of all barycentric coordinates. -/
theorem map_nonzero {m n : ℕ} (f : Fin (m+1) → Fin (n+1))
    (hf : Function.Surjective f) (x : StdSimplex ℝ (Fin (m+1)))
    (hx : ∀ i, x.weights i ≠ 0) (j : Fin (n+1)) :
    (StdSimplex.map f x).weights j ≠ 0 := by
  apply Finsupp.mem_support_iff.mp
  rw [support_map]
  obtain ⟨i, rfl⟩ := hf j
  exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr (hx i), rfl⟩

end

end Thomason.Construction.HornBarycentric

end

end OAI
