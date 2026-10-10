import OAI.Analysis.HyperbolicCones.PencilLimit
import OAI.Analysis.HyperbolicCones.PositiveMaps
import OAI.Analysis.HyperbolicCones.StrictBlock

namespace OAI

noncomputable section

open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem limit_add_identity {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (δ : ℝ) :
    P.limit X (Z + δ • 1) y =
      Matrix.fromBlocks (P.D X : Mat P.a ℝ) (P.B y) (P.B y)ᵀ
        ((P.E Z : Mat P.c ℝ) + δ • 1) := by
  simp [limit, P.E_unital]

theorem limit_add_identity_posDef {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef)
    (hM : (P.limit X Z y).PosSemidef) (δ : ℝ) (hδ : 0 < δ) :
    (P.limit X (Z + δ • 1) y).PosDef := by
  rw [P.limit_add_identity]
  exact fromBlocks_add_lower_posDef (P.D X) (P.E Z) (P.B y)
    (positive_unital_map_posDef P.D P.D_positive P.D_unital X hX) hM δ hδ

theorem target_of_limit_posSemidef {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef)
    (hM : (P.limit X Z y).PosSemidef) :
    ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
  have hregular (δ : ℝ) (hδ : 0 < δ) :
      (((Z + δ • 1 : Sym 4) : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
    have hp := P.limit_add_identity_posDef X Z y hX hM δ hδ
    have hnb : {H : selfAdjoint (Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ) |
        (H : Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ).PosDef} ∈
        𝓝 (P.limitSelfAdjoint X (Z + δ • 1) y) :=
      (FiniteMatrix.isOpen_posDef (Fin P.a ⊕ Fin P.c)).mem_nhds hp
    have he := (P.scaled_tendsto X (Z + δ • 1) y).eventually hnb
    have hsne : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := by
      filter_upwards [eventually_mem_nhdsWithin] with s hs
      simpa using hs
    have he' := (he.filter_mono nhdsWithin_le_nhds).and hsne
    obtain ⟨s, hps, hs⟩ := he'.exists
    exact (P.scaled_posSemidef_iff hSlice X (Z + δ • 1) y hX s hs).mp hps.posSemidef
  let T : Sym 4 := ⟨phi y (X : Mat 4 ℝ)⁻¹, phi_isHermitian y _ hX.inv.isHermitian⟩
  have hcont : Continuous (fun δ : ℝ => Z + δ • (1 : Sym 4) - T) := by fun_prop
  have hconv : Tendsto (fun δ : ℝ => Z + δ • (1 : Sym 4) - T)
      (𝓝[>] 0) (𝓝 (Z - T)) := by
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ((Z + δ • 1 - T : Sym 4) : Mat 4 ℝ).PosSemidef := by
    filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    simpa [T] using hregular δ hδ
  have hclosed := posSemidef_of_tendsto hconv hevent
  simpa [T] using hclosed

theorem limit_posSemidef_iff {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) :
    (P.limit X Z y).PosSemidef ↔
      ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef :=
  ⟨P.target_of_limit_posSemidef hSlice X Z y hX,
    P.limit_posSemidef_of_target hSlice X Z y hX⟩

theorem normalized_exists {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef)) :
    Nonempty NormalizedPencil := by
  refine ⟨{
    a := P.a
    c := P.c
    a_pos := P.a_pos
    c_pos := P.c_pos
    D := P.D
    E := P.E
    B := P.B
    D_positive := P.D_positive
    E_positive := P.E_positive
    D_unital := P.D_unital
    E_unital := P.E_unital
    schur_equivalence := ?_
  }⟩
  intro X Z y hX
  have hD := positive_unital_map_posDef P.D P.D_positive P.D_unital X hX
  let := hD.isUnit.invertible
  rw [← P.limit_posSemidef_iff hSlice X Z y hX]
  simpa only [limit, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.fromBlocks₁₁ (P.B y) (P.E Z : Mat P.c ℝ) hD

end Paper256.BlockPencil

end

end OAI
