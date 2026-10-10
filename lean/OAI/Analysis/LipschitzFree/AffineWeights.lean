import OAI.Analysis.LipschitzFree.SupportReduction
import OAI.Analysis.LipschitzFree.SignedTests

namespace OAI

/-!
# Affine signed coefficients and quantitative pairing bounds
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

def affineWeights (u : FreeSpace o) (j : S) : ℝ :=
  coordinate o sep j.val u +
    if j = ⟨o,ho⟩ then 1 - ∑ k : S, coordinate o sep k.val u else 0

@[simp] theorem affineWeights_mass (u : FreeSpace o) :
    ∑ j : S, affineWeights o sep S ho u j = 1 := by
  simp [affineWeights, Finset.sum_add_distrib]

theorem affineWeights_pairing (u : FreeSpace o)
    (hu : supportProjection o sep S u = u) (g : M → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ x y, |g x - g y| ≤ C * dist x y) :
    pairing (affineWeights o sep S ho u) (fun j : S => g j.val) =
      dualPairing o (Lip0.center o g C hC hg) u + g o := by
  have he : dualPairing o (Lip0.center o g C hC hg) u =
      ∑ j : S, coordinate o sep j.val u * (g j.val - g o) := by
    conv_lhs => rw [← hu]
    rw [supportProjection_apply]
    simp only [map_sum, map_smul, dualPairing_delta, Lip0.center_apply, smul_eq_mul]
    exact (Finset.sum_coe_sort S _).symm
  rw [he]
  simp only [pairing, affineWeights, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem affineWeights_variation (u : FreeSpace o)
    (hu : supportProjection o sep S u = u) :
    totalVariation (affineWeights o sep S ho u) ≤ 1 + 2*‖u‖ := by
  let μ := affineWeights o sep S ho u
  let g : M → ℝ := fun x => if hx : x ∈ S then
    (if 0 ≤ μ ⟨x,hx⟩ then 1 else -1) else 0
  have hb (x : M) : -1 ≤ g x ∧ g x ≤ 1 := by
    dsimp [g]
    split_ifs <;> norm_num
  have hg (x y : M) : |g x - g y| ≤ 2 * dist x y := by
    convert bounded_test_lipschitz sep hb x y using 1; norm_num
  have hid : pairing μ (fun j : S => g j.val) = totalVariation μ := by
    unfold pairing totalVariation
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g]
    rw [dite_eq_left j.property]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have ha := affineWeights_pairing o sep S ho u hu g 2 (by norm_num) hg
  change pairing μ (fun j : S => g j.val) = _ at ha
  rw [hid] at ha
  have hn := Lip0.center_norm_le o g 2 (by norm_num) hg
  have hp := (dualPairing_bound o (Lip0.center o g 2 (by norm_num) hg) u).trans
    (mul_le_mul_of_nonneg_left hn (norm_nonneg u))
  have hle := (le_abs_self (dualPairing o (Lip0.center o g 2 (by norm_num) hg) u)).trans hp
  linarith [(hb o).2]

theorem affineWeights_operator_variation (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (p B : ℝ) (hp : 0 ≤ p) (hn : ‖T‖ ≤ 2*p) (hb : ∀ x, dist x o ≤ B) (x : M) :
    totalVariation (affineWeights o sep S ho (T (delta o x))) ≤ 1 + 4*p*B := by
  have h := affineWeights_variation o sep S ho (T (delta o x)) (hfixed _)
  have hu : ‖T (delta o x)‖ ≤ (2*p)*B := by
    exact (T.le_opNorm _).trans (mul_le_mul hn (by simpa using hb x) (norm_nonneg _) (by positivity))
  nlinarith

end DiscreteFree
end

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)
    (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y) (S : Finset M) (ho : o ∈ S)

theorem affine_difference_bound (T : FreeSpace o →L[ℝ] FreeSpace o)
    (hfixed : ∀ u, supportProjection o sep S (T u) = T u)
    (c : ℝ) (hn : ‖T‖ ≤ c)
    (g : M → ℝ) (hg : LipschitzWith 1 g) (x y : M) :
    |pairing (affineWeights o sep S ho (T (delta o x))) (fun j : S => g j.val) -
      pairing (affineWeights o sep S ho (T (delta o y))) (fun j : S => g j.val)| ≤
        c * dist x y := by
  have hgl (s t : M) : |g s - g t| ≤ 1 * dist s t := by
    simpa only [Real.dist_eq, NNReal.coe_one] using hg.dist_le_mul s t
  let f := Lip0.center o g 1 (by norm_num) hgl
  have hf : ‖f‖ ≤ 1 := Lip0.center_norm_le o g 1 (by norm_num) hgl
  rw [affineWeights_pairing o sep S ho _ (hfixed _) g 1 (by norm_num) hgl,
    affineWeights_pairing o sep S ho _ (hfixed _) g 1 (by norm_num) hgl]
  rw [show dualPairing o (Lip0.center o g 1 (by norm_num) hgl) (T (delta o x)) + g o -
      (dualPairing o (Lip0.center o g 1 (by norm_num) hgl) (T (delta o y)) + g o) =
      dualPairing o f (T (delta o x - delta o y)) by rw [map_sub, map_sub]; ring]
  calc
    _ ≤ ‖T (delta o x - delta o y)‖ * ‖f‖ := dualPairing_bound o f _
    _ ≤ ‖T (delta o x - delta o y)‖ := mul_le_of_le_one_right (norm_nonneg _) hf
    _ ≤ ‖T‖ * ‖delta o x - delta o y‖ := T.le_opNorm _
    _ ≤ c * dist x y := by rw [delta_sub_norm]; exact mul_le_mul_of_nonneg_right hn dist_nonneg

end DiscreteFree
end

end

end OAI
