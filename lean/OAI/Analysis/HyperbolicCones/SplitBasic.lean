import OAI.Analysis.HyperbolicCones.RawBlocks
import OAI.Analysis.HyperbolicCones.PencilConjugation
import OAI.Analysis.HyperbolicCones.PositiveMaps

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256

def pencilFirst {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m) : Sym 4 →ₗ[ℝ] Sym m where
  toFun X := L ((X, 0), 0)
  map_add' X Y := by simpa using L.map_add ((X, 0), 0) ((Y, 0), 0)
  map_smul' s X := by simpa using L.map_smul s ((X, 0), 0)

def pencilSecond {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m) : Sym 4 →ₗ[ℝ] Sym m where
  toFun X := L ((0, X), 0)
  map_add' X Y := by simpa using L.map_add ((0, X), 0) ((0, Y), 0)
  map_smul' s X := by simpa using L.map_smul s ((0, X), 0)

def pencilParameter {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m) : (Fin 3 → ℝ) →ₗ[ℝ] Sym m where
  toFun y := L ((0, 0), y)
  map_add' x y := by simpa using L.map_add ((0, 0), x) ((0, 0), y)
  map_smul' s y := by simpa using L.map_smul s ((0, 0), y)

theorem pencil_decomposition {m : ℕ} (L : Ambient →ₗ[ℝ] Sym m)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    L ((X, Z), y) = pencilFirst L X + pencilSecond L Z + pencilParameter L y := by
  change L ((X, Z), y) = L ((X, 0), 0) + L ((0, Z), 0) + L ((0, 0), y)
  rw [← map_add, ← map_add]
  simp

theorem pencil_components_positive {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (pencilFirst L X : Mat m ℝ).PosSemidef) ∧
    (∀ Z : Sym 4, (Z : Mat 4 ℝ).PosSemidef → (pencilSecond L Z : Mat m ℝ).PosSemidef) := by
  constructor
  · intro X hX
    have h := (hzero X 0).mpr ⟨hX, Matrix.PosSemidef.zero⟩
    simpa only [hrep, mem_ofPred_eq] using! h
  · intro Z hZ
    have h := (hzero 0 Z).mpr ⟨Matrix.PosSemidef.zero, hZ⟩
    simpa only [hrep, mem_ofPred_eq] using! h

theorem pencil_first_identity_ne_zero {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    (pencilFirst L 1 : Mat m ℝ) ≠ 0 := by
  intro hz
  have hz' : pencilFirst L 1 = 0 := Subtype.ext hz
  have hpositive := (pencil_components_positive K L hrep hzero).2 1 Matrix.PosSemidef.one
  have heq : L (((-1, 1), 0) : Ambient) = pencilSecond L 1 := by
    rw [pencil_decomposition, map_neg, hz', map_zero]
    simp
  have hmem : (((-1, 1), 0) : Ambient) ∈ K := by
    rw [hrep]
    change (L (((-1, 1), 0) : Ambient) : Mat m ℝ).PosSemidef
    rwa [heq]
  have hh := ((hzero (-1) 1).mp hmem).1.diag_nonneg (i := (0 : Fin 4))
  norm_num at hh

theorem pencil_first_identity_not_posDef {m : ℕ} (K : Set Ambient)
    (L : Ambient →ₗ[ℝ] Sym m) (hrep : K = {x | (L x : Mat m ℝ).PosSemidef})
    (hzero : ∀ X Z : Sym 4, ((X, Z), (0 : Fin 3 → ℝ)) ∈ K ↔
      (X : Mat 4 ℝ).PosSemidef ∧ (Z : Mat 4 ℝ).PosSemidef) :
    ¬ (pencilFirst L 1 : Mat m ℝ).PosDef := by
  intro hpos
  have hi : pencilFirst L 1 ∈ interior {Y : Sym m | (Y : Mat m ℝ).PosDef} := by
    rw [(isOpen_posDef m).interior_eq]
    exact hpos
  obtain ⟨ε, hε, _, hminus⟩ := interior_line_pair hi (pencilSecond L 1)
  have heq : L (((1, -(ε • 1)), 0) : Ambient) =
      pencilFirst L 1 - ε • pencilSecond L 1 := by
    rw [pencil_decomposition, map_neg, map_smul, map_zero]
    simp [sub_eq_add_neg]
  have hmem : (((1, -(ε • 1)), 0) : Ambient) ∈ K := by
    rw [hrep]
    change (L (((1, -(ε • 1)), 0) : Ambient) : Mat m ℝ).PosSemidef
    rw [heq]
    exact hminus.posSemidef
  have hh := ((hzero 1 (-(ε • 1))).mp hmem).2.diag_nonneg (i := (0 : Fin 4))
  have : 0 ≤ -ε := by simpa using hh
  linarith

end Paper256

end

end OAI
