import OAI.Combinatorics.ProgressionColoring.ScalarMesh
import OAI.Combinatorics.ProgressionColoring.AdaptiveMesh

namespace OAI

/-!
# The adaptive mesh with the selected scalar parameters

This adapter instantiates the proved adaptive-mesh construction with `H=k⁻²`
and `alpha=q^(-(D+1))`. Its interval count agrees with the scalar ceiling used
in the numerical size estimates.
-/

noncomputable section

namespace QuantitativeVanDerWaerden.Parameters

theorem selected_meshScale_le_eighth {k : ℕ} (hk : 3 ≤ k) :
    meshScale k ≤ (1 / 8 : ℝ) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  unfold meshScale
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem selected_meshScale_le_one {k : ℕ} (hk : 3 ≤ k) :
    meshScale k ≤ 1 := (selected_meshScale_le_eighth hk).trans (by norm_num)

/-- The actual exponential mesh for the selected progression length and base. -/
def selectedAdaptiveMesh {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) : AdaptiveMesh where
  H := meshScale k
  alpha := scalarAlpha k q
  H_pos := meshScale_pos (by omega)
  H_le := selected_meshScale_le_eighth hk
  alpha_pos := scalarAlpha_pos hq
  alpha_le := scalarAlpha_le_quarter (by omega) hq

@[simp] theorem selectedAdaptiveMesh_H {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).H = meshScale k := rfl

@[simp] theorem selectedAdaptiveMesh_alpha {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).alpha = scalarAlpha k q := rfl

@[simp] theorem selectedAdaptiveMesh_R {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).R = scalarRadius k q := rfl

@[simp] theorem selectedAdaptiveMesh_m {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    (selectedAdaptiveMesh hk hq).m = scalarMeshSize k q := by
  unfold AdaptiveMesh.m scalarMeshSize
  congr 1
  change scalarRadius k q / meshScale k = (k : ℝ) ^ 2 * scalarRadius k q
  simp [meshScale, div_eq_mul_inv, mul_comm]

@[simp] theorem selectedAdaptiveMesh_card {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q) :
    Fintype.card (selectedAdaptiveMesh hk hq).Label = 2 * scalarMeshSize k q := by
  rw [AdaptiveMesh.card_label, selectedAdaptiveMesh_m]

/-- Concrete polynomial bound on the adaptive coordinate-label count. -/
theorem selectedAdaptiveMesh_card_le {k q : ℕ} (hk : 3 ≤ k) (hq : 2 ≤ q)
    (hlog : 1 ≤ Real.log k)
    (hqlog : (dimension k : ℝ) * Real.log q ≤
      c * k * Real.log k + dimension k * Real.log (2 * (k : ℝ) ^ 2)) :
    (Fintype.card (selectedAdaptiveMesh hk hq).Label : ℝ) ≤
      28 * (k : ℝ) ^ 3 * Real.log k := by
  rw [selectedAdaptiveMesh_card]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    scalarMeshSize_upper (by omega) hq hlog hqlog

end QuantitativeVanDerWaerden.Parameters

end

end OAI
