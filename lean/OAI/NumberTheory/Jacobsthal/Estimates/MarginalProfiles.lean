import OAI.NumberTheory.Jacobsthal.Partitions.MeshStationary
import OAI.NumberTheory.Jacobsthal.Primes.PrimeGridGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.MarginalProfiles

open _root_.Set _root_.Finset
open FinitePathGeometry PrimeSideSupport PrimeGridGeometry DerivativeWeights WeightFutureIntegrals

noncomputable def profile (m : ℕ) : Side → ℝ → ℝ
  | .even,_ => 1
  | .odd,t => 1-1/t^2+3*width m*W t

theorem index_regular {m j : ℕ} (hm : 1 ≤ m) (i : Side) (hj : lowerIndex m i ≤ j) :
    regularLower i ≤ point m j := by
  cases i with
  | even => simpa only [regularLower,Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
  | odd => simpa only [regularLower,Nat.cast_one] using (threshold_le_point hm 1 j).mpr (by simpa only [lowerIndex,one_mul] using hj)

theorem index_valid {m j : ℕ} (hm : 1 ≤ m) (i : Side) (hj : lowerIndex m i ≤ j) :
    Valid i (point m j) := by
  have ht := index_regular hm i hj
  cases i <;> dsimp [Valid,regularLower] at * <;> linarith

theorem profile_nonneg (m : ℕ) {i : Side} {t : ℝ} (ht : regularLower i ≤ t) : 0 ≤ profile m i t := by
  cases i with
  | even => exact zero_le_one
  | odd =>
    have ht1 : 1 ≤ t := ht
    have ht0 : 0 < t := by linarith
    have hinv : 1/t^2 ≤ 1 := by
      simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) (one_le_pow₀ ht1 : (1:ℝ) ≤ t^2)
    have hW := (W_pos ht0).le
    have hlead : 0 ≤ 1-1/t^2 := sub_nonneg.mpr hinv
    have hw := width_nonneg m
    change 0 ≤ 1-1/t^2+3*width m*W t
    positivity

theorem even_stationary_profile {m j : ℕ} (hm : 1 ≤ m) (hj : m ≤ j) :
    W (point m j)*(width m*((Finset.Icc (2*m) (j+m+1)).card:ℝ)) ≤ profile m .odd (point m j) := by
  have ht : (1:ℝ) ≤ point m j := by simpa only [Nat.cast_one] using (threshold_le_point hm 1 j).mpr (by simpa only [lowerIndex,one_mul] using hj)
  have ht0 : 0 < point m j := by linarith
  have hcount : width m*((Finset.Icc (2*m) (j+m+1)).card:ℝ) ≤ point m j-1+3*width m := by
    simpa only [width,point,div_eq_mul_inv,one_mul] using
      Erdos970Dependency.MeshStationary.even_row_literal m j hm hj
  calc
    _ ≤ W (point m j)*(point m j-1+3*width m) := mul_le_mul_of_nonneg_left hcount (W_pos ht0).le
    _ = _ := by unfold profile W; field_simp; ring

theorem odd_stationary_profile {m j : ℕ} (hm : 1 ≤ m) (hj : 2*m ≤ j) :
    W (point m j)*(∑ k ∈ Finset.Icc m (j+m+1),width m*profile m .odd (point m k)) ≤ 1+20*width m := by
  simpa only [width,point,profile,W,div_eq_mul_inv,one_mul,mul_assoc] using
    Erdos970Dependency.MeshStationary.odd_row_literal m j hm hj

theorem stationary_profile {m j : ℕ} (hm : 1 ≤ m) (i : Side) (hj : lowerIndex m i.flip ≤ j) :
    W (point m j)*(∑ k ∈ Finset.Icc (lowerIndex m i) (j+m+1),width m*profile m i (point m k)) ≤
      (1+20*width m)*profile m i.flip (point m j) := by
  cases i with
  | even =>
    have hj' : m ≤ j := hj
    have ht := index_regular hm .odd hj'
    have hp := profile_nonneg m ht
    have hsum : (∑ k ∈ Finset.Icc (2*m) (j+m+1),width m*profile m .even (point m k)) =
        width m*((Finset.Icc (2*m) (j+m+1)).card:ℝ) := by
      simp only [profile,mul_one,Finset.sum_const,nsmul_eq_mul]
      ring
    change W (point m j)*(∑ k ∈ Finset.Icc (2*m) (j+m+1),width m*profile m .even (point m k)) ≤
      (1+20*width m)*profile m .odd (point m j)
    rw [hsum]
    apply (even_stationary_profile hm hj').trans
    have hw := width_nonneg m
    have h := mul_nonneg (show 0 ≤ 20*width m by positivity) hp
    nlinarith
  | odd =>
    have hj' : 2*m ≤ j := hj
    simpa only [lowerIndex,Side.flip,profile,mul_one] using odd_stationary_profile hm hj'

theorem W_le_six {t : ℝ} (ht : (1/2:ℝ) ≤ t) : W t ≤ 6 := by
  have ht0 : 0 < t := by linarith
  unfold W
  apply (div_le_iff₀ (sq_pos_of_pos ht0)).mpr
  nlinarith [sq_nonneg (t-1/2)]

theorem W_initial_cost {t : ℝ} (ht : 2 ≤ t) : W t*(t+3) ≤ 4 := by
  have ht0 : 0 < t := by linarith
  calc
    _ = ((t+1)*(t+3))/t^2 := by unfold W; ring
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos ht0)).mpr (by nlinarith [sq_nonneg (t-2)])

theorem first_row_sum {m j : ℕ} (hm : 1 ≤ m) (hj : 2*m ≤ j) (I : Finset ℕ)
    (hI : I ⊆ Finset.Icc 0 (j+m+1)) (hpoints : ∀ k ∈ I,(1/2:ℝ) ≤ point m k) :
    W (point m j)*(∑ k ∈ I,width m*W (point m k)) ≤ 24 := by
  have ht : (2:ℝ) ≤ point m j := by simpa only [Nat.cast_ofNat] using (threshold_le_point hm 2 j).mpr hj
  have hW := (W_pos (show 0 < point m j by linarith)).le
  have hw := width_nonneg m
  have hw1 : width m ≤ 1 := Erdos970Dependency.MeshStationary.mesh_le_one m hm
  have hc : I.card ≤ j+m+2 := by
    have h := Finset.card_le_card hI
    rw [Nat.card_Icc] at h
    omega
  have hcR : (I.card:ℝ) ≤ ((j+m+2:ℕ):ℝ) := by exact_mod_cast hc
  have hs : (∑ k ∈ I,width m*W (point m k)) ≤ 6*(point m j+3) := by
    calc
      _ ≤ ∑ _k ∈ I,width m*6 := Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (W_le_six (hpoints k hk)) hw)
      _ = (6*width m)*(I.card:ℝ) := by rw [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ (6*width m)*((j+m+2:ℕ):ℝ) := mul_le_mul_of_nonneg_left hcR (by positivity)
      _ = 6*point m (j+m+2) := by unfold point width; ring
      _ = 6*(point m j+1+2*width m) := by rw [incoming_grid_end hm j]
      _ ≤ _ := by linarith
  calc
    _ ≤ W (point m j)*(6*(point m j+3)) := mul_le_mul_of_nonneg_left hs hW
    _ = 6*(W (point m j)*(point m j+3)) := by ring
    _ ≤ 6*4 := mul_le_mul_of_nonneg_left (W_initial_cost ht) (by norm_num)
    _ = _ := by norm_num

end NumberTheoryLean.MarginalProfiles

end

end Erdos970

end OAI
