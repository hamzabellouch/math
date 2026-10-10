import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomSourceQuery
import OAI.Combinatorics.EditApproximation.Refinement.ComputedEarlierInputBudget
import OAI.Combinatorics.EditApproximation.Refinement.ComputedGroupNumerical

namespace OAI

/-! Fixed-degree source-read bounds for a refinement entry. These hold on
all stored initial values, including outcomes outside accuracy events. -/

namespace EditApproximation

 theorem computed_source_key_budget {n M : ℕ} (N P : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (hw : 0 ≤ initial q) :
    (groupScalarKeys M (inputSmallLog N) (inputSmallLog N ^ 80)
      (localGroupQueryKeys N (inputSmallLog N) (40 * smallLogExponent N)
        (refinementFactor A (inputSmallLog N)) initial q)).length +
      (localOnlineSourceKeys N P (inputSmallLog N)
        (refinementFactor A (inputSmallLog N)) initial q).length ≤ inputHeight N ^ 91 := by
  let H := inputHeight N
  let ell := inputSmallLog N
  have hF : ell ≤ H := computed_smallLog_le_height N
  have hH : 64 ≤ H := (by omega : 64 ≤ ell).trans hF
  have hMbound : M ≤ H := by
    rw [hM]
    exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hW : (dyadicQueryWindow N (initial q) (refinementFactor A ell) ell).length ≤ H ^ 3 :=
    (computed_refinement_window N hN (by omega) A (initial q) hA).trans
      (computed_window_le_height_cube N hN (by omega) (by omega))
  have hkeys : (localGroupQueryKeys N ell (40 * smallLogExponent N)
      (refinementFactor A ell) initial q).length ≤ H ^ 87 := by
    calc
      _ ≤ (dyadicQueryWindow N (initial q) (refinementFactor A ell) ell).length *
          ((32 * ell + 2) * 2 ^ (40 * smallLogExponent N) + 2) ^ 2 :=
        localGroupQueryKeys_length N ell (40 * smallLogExponent N)
          (refinementFactor A ell) initial q (by omega) hw
      _ ≤ H ^ 3 * H ^ 84 := Nat.mul_le_mul hW (computed_cell_budget_le_height_pow N hH)
      _ = H ^ 87 := by rw [← pow_add]
  have hlabels : ∀ key ∈ localGroupQueryKeys N ell (40 * smallLogExponent N)
      (refinementFactor A ell) initial q, (groupDyadicScales M key.1 ell).length ≤ 2 * ell := by
    intro key hk
    have hb := localGroupQueryKeys_scale hk
    obtain ⟨eb, _, heq⟩ := List.mem_map.mp hb
    rw [hM, ← heq]
    exact computed_group_scale_count N eb hN (by omega)
  have hgroup : (groupScalarKeys M ell (ell ^ 80) (localGroupQueryKeys N ell
      (40 * smallLogExponent N) (refinementFactor A ell) initial q)).length ≤ H ^ 90 := by
    calc
      _ ≤ (localGroupQueryKeys N ell (40 * smallLogExponent N)
          (refinementFactor A ell) initial q).length * (2 * ell) * M :=
        groupScalarKeys_length_le M ell (ell ^ 80) (2 * ell) _ hlabels
      _ ≤ H ^ 87 * (H * H) * H := Nat.mul_le_mul
        (Nat.mul_le_mul hkeys (Nat.mul_le_mul (by omega) hF)) hMbound
      _ = H ^ 90 := by ring
  simp only [localOnlineSourceKeys, List.length_map]
  have hsmall : H ^ 3 ≤ H ^ 90 := pow_le_pow_right₀ (by omega) (by omega)
  calc
    _ ≤ H ^ 90 + H ^ 90 := Nat.add_le_add hgroup (hW.trans hsmall)
    _ = H ^ 90 * 2 := by omega
    _ ≤ H ^ 90 * H := Nat.mul_le_mul_left _ (by omega)
    _ = H ^ 91 := (pow_succ H 90).symm

end EditApproximation

end OAI
