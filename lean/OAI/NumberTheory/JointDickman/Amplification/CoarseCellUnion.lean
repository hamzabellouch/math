import OAI.NumberTheory.JointDickman.Amplification.CoarseGrid

namespace OAI

/-! # Exact union of the fine cells belonging to a coarse cell -/
namespace JointDickman
open Finset Classical

theorem intervalIndicator_eq_sub {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    (if x ∈ Set.Ioc a b then (1 : ℝ) else 0) =
      (if x ≤ b then 1 else 0)-(if x ≤ a then 1 else 0) := by
  by_cases ha : x ≤ a
  · have hb : x ≤ b := ha.trans hab
    simp [Set.mem_Ioc,ha,hb,not_lt_of_ge ha]
  · have ha' : a < x := lt_of_not_ge ha
    by_cases hb : x ≤ b <;> simp [Set.mem_Ioc,ha,ha',hb]

theorem uniformCell_indicator_sum (a δ x : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    (∑ r ∈ range k, if x ∈ Set.Ioc (a+r*δ) (a+(r+1)*δ) then (1 : ℝ) else 0) =
      if x ∈ Set.Ioc a (a+k*δ) then 1 else 0 := by
  have he (r : ℕ) : (if x ∈ Set.Ioc (a+r*δ) (a+(r+1)*δ) then (1 : ℝ) else 0) =
      (if x ≤ a+(r+1)*δ then 1 else 0)-(if x ≤ a+r*δ then 1 else 0) :=
    intervalIndicator_eq_sub (by linarith) x
  simp_rw [he]
  have hs := sum_range_sub (fun r : ℕ => if x ≤ a+(r : ℝ)*δ then (1 : ℝ) else 0) k
  simp only [Nat.cast_add,Nat.cast_one] at hs
  rw [hs]
  simp only [Nat.cast_zero,zero_mul,add_zero]
  exact (intervalIndicator_eq_sub (le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg k) hδ)) x).symm

theorem channelMesh_mul {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    (k : ℝ)*channelMesh (m*k) = channelMesh m := by
  unfold channelMesh
  rw [Nat.cast_mul]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem groupedLower_eq_coarse {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (d : Fin m) (r : Fin k) :
    groupedLower m k (d,r) = channelLower m d+(r.val : ℝ)*channelMesh (m*k) := by
  have he := channelMesh_mul hm hk
  change 1/2+((r.val+k*d.val : ℕ) : ℝ)*channelMesh (m*k) =
    1/2+(d.val : ℝ)*channelMesh m+(r.val : ℝ)*channelMesh (m*k)
  push_cast
  rw [← he]
  ring

theorem groupedUpper_eq_coarse {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (d : Fin m) (r : Fin k) :
    groupedUpper m k (d,r) = channelLower m d+((r.val : ℝ)+1)*channelMesh (m*k) := by
  have hw := grouped_width m k (d,r)
  rw [groupedLower_eq_coarse hm hk] at hw
  linarith

theorem groupedCell_indicator_sum {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (d : Fin m) (x : ℝ) :
    (∑ r : Fin k, if x ∈ Set.Ioc (groupedLower m k (d,r)) (groupedUpper m k (d,r))
      then (1 : ℝ) else 0) =
      if x ∈ Set.Ioc (channelLower m d) (channelUpper m d) then 1 else 0 := by
  simp_rw [groupedLower_eq_coarse hm hk,groupedUpper_eq_coarse hm hk]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    if x ∈ Set.Ioc (channelLower m d+(r : ℝ)*channelMesh (m*k))
      (channelLower m d+((r : ℝ)+1)*channelMesh (m*k)) then (1 : ℝ) else 0)]
  have he := uniformCell_indicator_sum (channelLower m d) (channelMesh (m*k)) x
    (channelMesh_pos (Nat.mul_pos hm hk)).le k
  rw [channelMesh_mul hm hk] at he
  have hu : channelLower m d+channelMesh m = channelUpper m d := by
    unfold channelUpper channelLower
    ring
  rw [hu] at he
  exact he

end JointDickman

end OAI
