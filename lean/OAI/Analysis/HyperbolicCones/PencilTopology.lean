import OAI.Analysis.HyperbolicCones.PencilOrder

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

def quadraticEvaluation {n : ℕ} (v : Fin n → ℝ) : Sym n →ₗ[ℝ] ℝ where
  toFun X := v ⬝ᵥ ((X : Mat n ℝ) *ᵥ v)
  map_add' X Y := by simp [add_mulVec, dotProduct_add]
  map_smul' c X := by simp [smul_mulVec, dotProduct_smul]

theorem isClosed_posSemidef (n : ℕ) : IsClosed {X : Sym n | (X : Mat n ℝ).PosSemidef} := by
  have heq : {X : Sym n | (X : Mat n ℝ).PosSemidef} =
      ⋂ v : Fin n → ℝ, {X | 0 ≤ quadraticEvaluation v X} := by
    ext X
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h.dotProduct_mulVec_nonneg v
    · intro h
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg X.property
      intro v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    (quadraticEvaluation v).continuous_of_finiteDimensional

theorem posSemidef_of_tendsto {α : Type u} {f : Filter α} [f.NeBot] {n : ℕ}
    {A : α → Sym n} {H : Sym n} (hA : Tendsto A f (𝓝 H))
    (h : ∀ᶠ x in f, (A x : Mat n ℝ).PosSemidef) : (H : Mat n ℝ).PosSemidef :=
  (isClosed_posSemidef n).mem_of_tendsto hA h

end Paper256

end

end OAI
