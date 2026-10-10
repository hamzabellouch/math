import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

open scoped BigOperators

namespace Erdos970Dependency.MeshStationary

noncomputable def mesh (m : ℕ) : ℝ := 1/(m : ℝ)
noncomputable def point (m k : ℕ) : ℝ := (k : ℝ)*mesh m
noncomputable def weight (u : ℝ) : ℝ := (u+1)/u^2

theorem mesh_nonneg (m : ℕ) : 0 ≤ mesh m := by unfold mesh; positivity

theorem mesh_pos (m : ℕ) (hm : 1 ≤ m) : 0 < mesh m := by
  have h : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  unfold mesh
  positivity

theorem mesh_le_one (m : ℕ) (hm : 1 ≤ m) : mesh m ≤ 1 := by
  have h : (0 : ℝ) < m := by exact_mod_cast (show 0 < m from hm)
  exact (div_le_one h).mpr (by exact_mod_cast hm)

theorem mesh_mul (m : ℕ) (hm : 1 ≤ m) : (m : ℝ)*mesh m = 1 := by
  have h : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (show 0 < m from hm))
  simp [mesh,h]

theorem point_ge_one (m k : ℕ) (hm : 1 ≤ m) (hkm : m ≤ k) : 1 ≤ point m k := by
  have h := mul_le_mul_of_nonneg_right (show (m : ℝ) ≤ k by exact_mod_cast hkm) (mesh_nonneg m)
  rw [mesh_mul m hm] at h
  exact h

theorem point_ge_two (m j : ℕ) (hm : 1 ≤ m) (hj : 2*m ≤ j) : 2 ≤ point m j := by
  have h := mul_le_mul_of_nonneg_right (show (2 : ℝ)*m ≤ j by exact_mod_cast hj) (mesh_nonneg m)
  rw [mul_assoc,mesh_mul m hm,mul_one] at h
  exact h

theorem point_nonneg (m k : ℕ) : 0 ≤ point m k :=
  mul_nonneg (Nat.cast_nonneg _) (mesh_nonneg _)

theorem point_succ (m k : ℕ) : point m (k+1) = point m k+mesh m := by
  unfold point
  push_cast
  ring

theorem weight_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ weight u := by unfold weight; positivity

theorem weight_le_two {u : ℝ} (hu : 1 ≤ u) : weight u ≤ 2 := by
  unfold weight
  apply (div_le_iff₀ (by positivity : 0 < u^2)).mpr
  nlinarith [sq_nonneg (u-1)]

theorem weight_cost_le_twenty {t : ℝ} (ht : 2 ≤ t) : weight t*(6*t+14) ≤ 20 := by
  calc
    _ = ((t+1)*(6*t+14))/t^2 := by unfold weight; ring
    _ ≤ _ := (div_le_iff₀ (by positivity : 0 < t^2)).mpr (by nlinarith [sq_nonneg (t-2)])

theorem reciprocal_drop_le {u h : ℝ} (hu : 0 < u) (hh : 0 ≤ h) :
    1/u-1/(u+h) ≤ h/u^2 := by
  have hup : 0 < u+h := by linarith
  calc
    _ = h/(u*(u+h)) := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_left hh (by positivity) (by nlinarith)

theorem reciprocal_telescope (m lo hi : ℕ) (hlohi : lo ≤ hi) :
    (∑ k ∈ Finset.Icc lo hi, ((1 : ℝ) / point m k - (1 : ℝ) / point m (k+1))) =
      (1 : ℝ) / point m lo - (1 : ℝ) / point m (hi+1) := by
  simpa only [neg_sub_neg] using!
    Finset.sum_Icc_sub hlohi (fun k => -(1/point m k))

theorem even_row_count (m j : ℕ) (hm : 1 ≤ m) (hj : m ≤ j) :
    mesh m * ((Finset.Icc (2*m) (j+m+1)).card : ℝ) ≤ point m j-1+3*mesh m := by
  have hc : (Finset.Icc (2*m) (j+m+1)).card+m = j+2 := by
    rw [Nat.card_Icc]
    omega
  have hcr : ((Finset.Icc (2*m) (j+m+1)).card : ℝ)+(m : ℝ) = (j : ℝ)+2 := by
    exact_mod_cast hc
  have he := congrArg (fun x : ℝ => x*mesh m) hcr
  have hmul := mesh_mul m hm
  have hn := mesh_nonneg m
  unfold point
  nlinarith

end Erdos970Dependency.MeshStationary

end

section

open scoped BigOperators

namespace Erdos970Dependency.MeshStationary

theorem row_card (m j : ℕ) : (Finset.Icc m (j+m+1)).card = j+2 := by
  rw [Nat.card_Icc]
  omega

theorem point_last (m j : ℕ) (hm : 1 ≤ m) :
    point m (j+m+2) = point m j + 1 + 2*mesh m := by
  unfold point
  push_cast
  nlinarith [mesh_mul m hm]

theorem reciprocal_sum_lower (m j : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) - 1 / point m (j+m+2) ≤
      ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
  have h : (∑ k ∈ Finset.Icc m (j+m+1),
      ((1 : ℝ) / point m k - (1 : ℝ) / point m (k+1))) ≤
      ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
    apply Finset.sum_le_sum
    intro k hk
    rw [point_succ]
    exact reciprocal_drop_le
      (lt_of_lt_of_le zero_lt_one (point_ge_one m k hm (Finset.mem_Icc.mp hk).1))
      (mesh_nonneg m)
  rw [reciprocal_telescope m m (j+m+1) (by omega)] at h
  have hfirst : point m m = 1 := mesh_mul m hm
  simpa only [hfirst,div_one,show j+m+1+1 = j+m+2 by omega] using h

theorem leading_sum_le (m j : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc m (j+m+1), mesh m * (1 - 1 / (point m k)^2)) ≤
      (point m j)^2 / (point m j+1) + 2*mesh m := by
  have ht := point_nonneg m j
  have hh := mesh_nonneg m
  have ht1 : 0 < point m j+1 := by linarith
  have hrec := reciprocal_sum_lower m j hm
  rw [point_last m j hm] at hrec
  have hinv : (1 : ℝ) / (point m j+1+2*mesh m) ≤ 1 / (point m j+1) :=
    div_le_div_of_nonneg_left (by norm_num) ht1 (by linarith)
  calc
    _ = (∑ _k ∈ Finset.Icc m (j+m+1),mesh m) -
        ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = point m j + 2*mesh m -
        ∑ k ∈ Finset.Icc m (j+m+1), mesh m / (point m k)^2 := by
      simp only [Finset.sum_const,row_card,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat,point]
      ring
    _ ≤ point m j + 2*mesh m - (1 - 1 / (point m j+1+2*mesh m)) :=
      sub_le_sub_left hrec _
    _ ≤ point m j - 1 + 1 / (point m j+1) + 2*mesh m := by linarith
    _ = _ := by field_simp; ring

theorem correction_sum_le (m j : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc m (j+m+1), mesh m * (3*mesh m*weight (point m k))) ≤
      6*mesh m*(point m j+2) := by
  have hh := mesh_nonneg m
  have hh1 := mesh_le_one m hm
  calc
    _ ≤ ∑ _k ∈ Finset.Icc m (j+m+1),mesh m*(3*mesh m*2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (weight_le_two (point_ge_one m k hm (Finset.mem_Icc.mp hk).1)) (by positivity))
        hh
    _ = 6*mesh m*(point m j+2*mesh m) := by
      simp only [Finset.sum_const,row_card,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat,point]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem full_row_sum_le (m j : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Icc m (j+m+1),
      mesh m * (1 - 1 / (point m k)^2 + 3*mesh m*weight (point m k))) ≤
      (point m j)^2 / (point m j+1) + 2*mesh m + 6*mesh m*(point m j+2) := by
  calc
    _ = (∑ k ∈ Finset.Icc m (j+m+1),mesh m*(1 - 1 / (point m k)^2)) +
        ∑ k ∈ Finset.Icc m (j+m+1),mesh m*(3*mesh m*weight (point m k)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := add_le_add (leading_sum_le m j hm) (correction_sum_le m j hm)

end Erdos970Dependency.MeshStationary

end

section

open scoped BigOperators

namespace Erdos970Dependency.MeshStationary

theorem odd_row_weighted (m j : ℕ) (hm : 1 ≤ m) (hj : 2*m ≤ j) :
    weight (point m j) *
      (∑ k ∈ Finset.Icc m (j+m+1),
        mesh m * (1 - 1 / (point m k)^2 + 3*mesh m*weight (point m k))) ≤
      1 + 20*mesh m := by
  have ht2 := point_ge_two m j hm hj
  have ht0 : point m j ≠ 0 := by linarith
  have ht1 : point m j+1 ≠ 0 := by linarith
  have hW := weight_nonneg (point_nonneg m j)
  calc
    _ ≤ weight (point m j) *
        ((point m j)^2 / (point m j+1) + 2*mesh m + 6*mesh m*(point m j+2)) :=
      mul_le_mul_of_nonneg_left (full_row_sum_le m j hm) hW
    _ = 1 + mesh m * (weight (point m j)*(6*point m j+14)) := by
      unfold weight
      field_simp
      ring
    _ ≤ 1 + mesh m*20 := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (weight_cost_le_twenty ht2) (mesh_nonneg m))
    _ = _ := by ring

theorem even_row_literal (m j : ℕ) (hm : 1 ≤ m) (hj : m ≤ j) :
    (1/(m : ℝ)) * ((Finset.Icc (2*m) (j+m+1)).card : ℝ) ≤
      (j : ℝ)/(m : ℝ) - 1 + 3/(m : ℝ) := by
  simpa only [mesh,point,div_eq_mul_inv,one_mul] using even_row_count m j hm hj

theorem odd_row_literal (m j : ℕ) (hm : 1 ≤ m) (hj : 2*m ≤ j) :
    (((j : ℝ)/(m : ℝ)+1)/((j : ℝ)/(m : ℝ))^2) *
      (∑ k ∈ Finset.Icc m (j+m+1),
        (1/(m : ℝ)) *
          (1 - 1 / ((k : ℝ)/(m : ℝ))^2 +
            (3/(m : ℝ))*(((k : ℝ)/(m : ℝ)+1)/((k : ℝ)/(m : ℝ))^2))) ≤
      1 + 20/(m : ℝ) := by
  simpa only [mesh,point,weight,div_eq_mul_inv,one_mul,mul_assoc] using
    odd_row_weighted m j hm hj

end Erdos970Dependency.MeshStationary

end

end Erdos970

end OAI
