import OAI.Analysis.HyperbolicCones.BlockScaling
import OAI.Analysis.HyperbolicCones.FiniteTopology

namespace OAI

noncomputable section

open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

def scaledSelfAdjoint {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) :
    selfAdjoint (Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ) :=
  ⟨P.scaled X Z y s, P.scaled_isHermitian X Z y s⟩

def limitSelfAdjoint {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    selfAdjoint (Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ) :=
  ⟨P.limit X Z y, P.limit_isHermitian X Z y⟩

theorem scaled_polynomial {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) :
    P.scaled X Z y s = P.limit X Z y +
      s • Matrix.fromBlocks (P.A y : Mat P.a ℝ) (P.C Z) (P.C Z)ᵀ (0 : Mat P.c ℝ) +
      s ^ 2 • Matrix.fromBlocks (P.F Z : Mat P.a ℝ) 0 0 (0 : Mat P.c ℝ) := by
  ext (i | i) (j | j) <;> simp [scaled, limit, Matrix.fromBlocks]

theorem scaled_continuous {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : Continuous (P.scaled X Z y) := by
  change Continuous (fun s : ℝ => P.scaled X Z y s)
  simp_rw [P.scaled_polynomial X Z y]
  fun_prop

theorem scaledSelfAdjoint_continuous {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : Continuous (P.scaledSelfAdjoint X Z y) :=
  (P.scaled_continuous X Z y).subtype_mk _

theorem scaledSelfAdjoint_zero {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    P.scaledSelfAdjoint X Z y 0 = P.limitSelfAdjoint X Z y := by
  apply Subtype.ext
  exact P.scaled_zero X Z y

theorem scaled_tendsto {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    Tendsto (P.scaledSelfAdjoint X Z y) (𝓝 0) (𝓝 (P.limitSelfAdjoint X Z y)) := by
  simpa only [P.scaledSelfAdjoint_zero X Z y] using
    (P.scaledSelfAdjoint_continuous X Z y).tendsto (0 : ℝ)

theorem limit_posSemidef_of_target {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef)
    (hZ : ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef) :
    (P.limit X Z y).PosSemidef := by
  have hsne : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    simpa using hs
  apply FiniteMatrix.posSemidef_of_tendsto (f := 𝓝[≠] (0 : ℝ))
    ((P.scaled_tendsto X Z y).mono_left inf_le_left)
  filter_upwards [hsne] with s hs
  exact (P.scaled_posSemidef_iff hSlice X Z y hX s hs).mpr hZ

end Paper256.BlockPencil

end

end OAI
