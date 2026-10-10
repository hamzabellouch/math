import OAI.Analysis.LipschitzFree.Evaluation

namespace OAI

/-!
# Signed evaluation coefficients and finite-support projections
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped BigOperators Classical
variable {M : Type*} [MetricSpace M] (o : M)

def dualPairing (f : Lip0 o) : FreeSpace o →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ f).comp (freeSubmodule o).subtypeL

@[simp] theorem dualPairing_apply (f : Lip0 o) (u : FreeSpace o) : dualPairing o f u = u.val f := rfl
@[simp] theorem dualPairing_delta (f : Lip0 o) (x : M) : dualPairing o f (delta o x) = f x := rfl

theorem dualPairing_bound (f : Lip0 o) (u : FreeSpace o) : |dualPairing o f u| ≤ ‖u‖ * ‖f‖ :=
  u.val.le_opNorm f

namespace Lip0
@[simp] theorem zero_apply (x : M) : (0 : Lip0 o) x = 0 := rfl
@[simp] theorem add_apply (f g : Lip0 o) (x : M) : (f+g) x = f x + g x := rfl
@[simp] theorem smul_apply (c : ℝ) (f : Lip0 o) (x : M) : (c • f) x = c * f x := rfl

def center (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) : Lip0 o :=
  ofBound o (fun x => g x - g o) (by simp) L hL (by intro x y; simpa using hg x y)

@[simp] theorem center_apply (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) (x : M) :
    center o g L hL hg x = g x - g o := rfl

theorem center_norm_le (g : M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hg : ∀ x y, |g x - g y| ≤ L * dist x y) : ‖center o g L hL hg‖ ≤ L := by
  apply (norm_le_iff _ hL).mpr
  intro x y
  simpa using hg x y
end Lip0

variable (sep : ∀ x y : M, x ≠ y → 1 ≤ dist x y)

include sep in

theorem bounded_test_lipschitz {g : M → ℝ} {a b : ℝ}
    (hg : ∀ x, a ≤ g x ∧ g x ≤ b) (x y : M) :
    |g x - g y| ≤ (b-a) * dist x y := by
  have hab : a ≤ b := (hg x).1.trans (hg x).2
  by_cases h : x = y
  · simp [h]
  · have hd := sep x y h
    have hs : |g x - g y| ≤ b-a := by rw [abs_le]; constructor <;> linarith [(hg x).1, (hg x).2, (hg y).1, (hg y).2]
    exact hs.trans (le_mul_of_one_le_right (sub_nonneg.mpr hab) hd)

omit [MetricSpace M] in
theorem sum_point_test {V : Type*} [AddCommMonoid V] (F : Finset M) (x : M) (v : M → V) :
    (∑ j ∈ F, if x = j ∧ j ≠ o then v j else 0) = if x ∈ F ∧ x ≠ o then v x else 0 := by
  have ht (j : M) : (if x = j ∧ j ≠ o then v j else 0) =
      if j = x then (if x ≠ o then v x else 0) else 0 := by
    by_cases h : j = x
    · subst j; simp
    · simp [h, Ne.symm h]
  simp_rw [ht]
  rw [Finset.sum_ite_eq']
  split_ifs <;> simp_all

def indicator (j : M) : Lip0 o :=
  Lip0.ofBound o (fun x => if x = j ∧ j ≠ o then 1 else 0) (by simp [eq_comm]) 1 (by norm_num)
    (by
      intro x y
      have h := bounded_test_lipschitz sep
        (g := fun x => if x = j ∧ j ≠ o then (1 : ℝ) else 0)
        (a := 0) (b := 1) (by intro z; split_ifs <;> norm_num) x y
      simpa using h)

@[simp] theorem indicator_apply (j x : M) : indicator o sep j x = if x = j ∧ j ≠ o then 1 else 0 := rfl

def coordinate (j : M) : FreeSpace o →L[ℝ] ℝ := dualPairing o (indicator o sep j)

@[simp] theorem coordinate_delta (j x : M) : coordinate o sep j (delta o x) = if x = j ∧ j ≠ o then 1 else 0 := rfl

@[simp] theorem coordinate_base : coordinate o sep o = 0 := by
  ext u
  have hi : indicator o sep o = 0 := by apply Subtype.ext; funext x; simp
  simp [coordinate, hi]

theorem sum_abs_coordinate_le (F : Finset M) (u : FreeSpace o) :
    ∑ j ∈ F, |coordinate o sep j u| ≤ 2 * ‖u‖ := by
  let c : M → ℝ := fun j => if 0 ≤ coordinate o sep j u then 1 else -1
  let f : Lip0 o := ∑ j ∈ F, c j • indicator o sep j
  have hfc (x : M) : f x = if x ∈ F ∧ x ≠ o then c x else 0 := by
    change evaluation o x (∑ j ∈ F, c j • indicator o sep j) = _
    simp only [map_sum, map_smul, evaluation_apply, indicator_apply, smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero]
    exact sum_point_test o F x c
  have hcb (x : M) : -1 ≤ f x ∧ f x ≤ 1 := by
    rw [hfc]
    dsimp [c]
    split_ifs <;> norm_num
  have hf : ‖f‖ ≤ 2 := (Lip0.norm_le_iff f (by norm_num)).mpr (by
    intro x y
    convert bounded_test_lipschitz sep hcb x y using 1; norm_num)
  have hpair : dualPairing o f u = ∑ j ∈ F, |coordinate o sep j u| := by
    change u.val (∑ j ∈ F, c j • indicator o sep j) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    change c j * coordinate o sep j u = _
    dsimp [c]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [neg_one_mul, abs_of_neg (lt_of_not_ge h)]
  have hh := (dualPairing_bound o f u).trans (mul_le_mul_of_nonneg_left hf (norm_nonneg u))
  rw [hpair, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)), mul_comm] at hh
  exact hh

def supportProjection (F : Finset M) : FreeSpace o →L[ℝ] FreeSpace o :=
  ∑ j ∈ F, (coordinate o sep j).smulRight (delta o j)

@[simp] theorem supportProjection_apply (F : Finset M) (u : FreeSpace o) :
    supportProjection o sep F u = ∑ j ∈ F, coordinate o sep j u • delta o j := by
  simp [supportProjection]

theorem supportProjection_delta (F : Finset M) (x : M) :
    supportProjection o sep F (delta o x) = if x ∈ F then delta o x else 0 := by
  rw [supportProjection_apply]
  by_cases hx : x = o
  · subst x
    simp
  · simp only [coordinate_delta, ite_smul, one_smul, zero_smul]
    rw [sum_point_test]
    simp [hx]

theorem supportProjection_bound (F : Finset M) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, dist x o ≤ B) : ‖supportProjection o sep F‖ ≤ 2*B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [supportProjection_apply]
  calc
    ‖∑ j ∈ F, coordinate o sep j u • delta o j‖ ≤
        ∑ j ∈ F, ‖coordinate o sep j u • delta o j‖ := norm_sum_le _ _
    _ = ∑ j ∈ F, |coordinate o sep j u| * dist j o := by simp only [norm_smul, Real.norm_eq_abs, delta_norm]
    _ ≤ ∑ j ∈ F, |coordinate o sep j u| * B := by gcongr with j hj; exact hb j
    _ = (∑ j ∈ F, |coordinate o sep j u|) * B := (Finset.sum_mul ..).symm
    _ ≤ (2 * ‖u‖) * B := mul_le_mul_of_nonneg_right (sum_abs_coordinate_le o sep F u) hB
    _ = (2*B) * ‖u‖ := by ring

end DiscreteFree
end

end

end OAI
