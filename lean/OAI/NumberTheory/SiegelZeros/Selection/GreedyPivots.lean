import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
namespace WeightedTorusJets

theorem pivot_floor_square_bound {t : ℝ} (ht : 1 ≤ t) :
    ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2 ≤ 97 ^ 2 * t ^ 2 := by
  have hf := Nat.floor_le (show 0 ≤ 96 * t by positivity)
  have hupper : ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ≤ 97 * t := by
    push_cast
    linarith
  nlinarith [sq_nonneg (((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) - 97 * t)]

theorem pivot_second_sum_bound {ι : Type*} (s : Finset ι) (b c : ι → ℕ)
    {t : ℝ} (hb : ∀ i ∈ s, (b i : ℝ) ≤ 96 * t)
    (hc : ∀ i ∈ s, (c i : ℝ) ≤ 96 * t) :
    ∑ i ∈ s, ((b i : ℝ) + c i) ≤ 192 * s.card * t := by
  calc
    ∑ i ∈ s, ((b i : ℝ) + c i) ≤ ∑ _i ∈ s, (192 * t) :=
      Finset.sum_le_sum fun i hi => by linarith [hb i hi, hc i hi]
    _ = 192 * s.card * t := by simp; ring

theorem pivot_lower_bound_quarter {M Q S : ℝ} (hQ : 0 < Q) (hM : 2 * Q ≤ M)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) : M ^ 2 / (4 * Q) ≤ S := by
  have hnonneg : 0 ≤ M * (M - 2 * Q) := mul_nonneg (by linarith) (by linarith)
  have h : M ^ 2 / (4 * Q) ≤ M ^ 2 / (2 * Q) - M / 2 := by
    apply (div_le_iff₀ (show 0 < 4 * Q by positivity)).mpr
    field_simp
    nlinarith
  exact h.trans hS

theorem pivot_lower_constant {M Q H t S : ℝ} (hQ : 0 < Q) (ht : 0 < t)
    (hH : 0 < H) (hM : M = H * t ^ 3) (hMQ : 2 * Q ≤ M)
    (hQt : Q ≤ 97 ^ 2 * t ^ 2)
    (hS : M ^ 2 / (2 * Q) - M / 2 ≤ S) :
    M * H * t / (4 * 97 ^ 2) ≤ S := by
  have hquarter := pivot_lower_bound_quarter hQ hMQ hS
  have hlower : M * H * t / (4 * 97 ^ 2) ≤ M ^ 2 / (4 * Q) := by
    apply (le_div_iff₀ (show 0 < 4 * Q by positivity)).mpr
    have hnonneg : 0 ≤ M * H * t := by rw [hM]; positivity
    have h := mul_le_mul_of_nonneg_left hQt hnonneg
    rw [hM] at h ⊢
    nlinarith
  exact hlower.trans hquarter

theorem pivot_ratio_bound {M H t S₁ S₂ : ℝ} (hM : 0 < M) (hH : 0 < H)
    (ht : 0 < t) (hS₁ : M * H * t / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * t) : S₂ / S₁ ≤ (192 * (4 * 97 ^ 2)) / H := by
  have hpos : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁
  apply (div_le_iff₀ hpos).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hH).mpr
  have h := mul_le_mul_of_nonneg_left hS₁ (show (0 : ℝ) ≤ 192 * (4 * 97 ^ 2) by norm_num)
  have h' := mul_le_mul_of_nonneg_right hS₂ hH.le
  nlinarith

theorem pivot_ratio_le_twelfth {M H t S₁ S₂ : ℝ} (hM : 0 < M)
    (hH : 86713344 ≤ H) (ht : 0 < t)
    (hS₁ : M * H * t / (4 * 97 ^ 2) ≤ S₁)
    (hS₂ : S₂ ≤ 192 * M * t) : S₂ / S₁ ≤ 1 / 12 := by
  have hHpos : 0 < H := by linarith
  apply (pivot_ratio_bound hM hHpos ht hS₁ hS₂).trans
  apply (div_le_iff₀ hHpos).mpr
  norm_num at *
  linarith

theorem pivot_scale_ge_one {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N) :
    1 ≤ H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ) := by
  have hHpos : 0 < H := by linarith
  calc
    1 ≤ H := hH
    _ = H ^ (-(1 / 3 : ℝ)) * H ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_add hHpos]
      norm_num
    _ ≤ H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hHpos.le _)
      exact Real.rpow_le_rpow hHpos.le hHN (by norm_num)

theorem pivot_dimension_eq_cube {N : ℝ} (hN : 0 ≤ N) :
    (N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
  norm_num

theorem pivot_scale_cube {H N : ℝ} (hH : 0 < H) (hN : 0 ≤ N) :
    H * (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ)) ^ 3 = N ^ 4 := by
  rw [mul_pow, pivot_dimension_eq_cube hN, ← Real.rpow_natCast,
    ← Real.rpow_mul hH.le]
  norm_num
  rw [Real.rpow_neg_one, ← mul_assoc, mul_inv_cancel₀ hH.ne']
  simp

theorem pivot_primary_scale {H U : ℝ} (hH : 0 < H) :
    H * (H ^ (-(1 / 3 : ℝ)) * U) = H ^ (2 / 3 : ℝ) * U := by
  rw [← mul_assoc]
  have hp := Real.rpow_add hH (1 : ℝ) (-(1 / 3 : ℝ))
  norm_num at hp
  rw [← hp]

theorem pivot_count_threshold {H t Q : ℝ} (hQ : Q ≤ 97 ^ 2 * t ^ 2)
    (hscale : 2 * 97 ^ 2 ≤ H * t) : 2 * Q ≤ H * t ^ 3 := by
  nlinarith [mul_le_mul_of_nonneg_right hscale (sq_nonneg t)]

theorem pivot_primary_scale_ge_N {H N : ℝ} (hH : 1 ≤ H) (hN : 1 ≤ N) :
    N ≤ H ^ (2 / 3 : ℝ) * N ^ (4 / 3 : ℝ) := by
  have hHp : 1 ≤ H ^ (2 / 3 : ℝ) := Real.one_le_rpow hH (by norm_num)
  have hNp : N ≤ N ^ (4 / 3 : ℝ) := Real.self_le_rpow_of_one_le hN (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hHp (show 0 ≤ N ^ (4 / 3 : ℝ) by positivity)
  simp only [one_mul] at hprod
  exact hNp.trans hprod

theorem pivot_floor_count_eventually {H N : ℝ} (hH : 1 ≤ H) (hHN : H ≤ N)
    (hN : 18818 ≤ N) :
    2 * (((⌊96 * (H ^ (-(1 / 3 : ℝ)) * N ^ (4 / 3 : ℝ))⌋₊ + 1 : ℕ) : ℝ) ^ 2)
      ≤ N ^ 4 := by
  have hHpos : 0 < H := by linarith
  have hNnonneg : 0 ≤ N := by linarith
  rw [← pivot_scale_cube hHpos hNnonneg]
  apply pivot_count_threshold (pivot_floor_square_bound (pivot_scale_ge_one hH hHN))
  rw [pivot_primary_scale hHpos]
  have h := pivot_primary_scale_ge_N hH (show 1 ≤ N by linarith)
  norm_num
  linarith

theorem pivot_coordinates_of_weight {H U : ℝ} (hH : 0 < H) (a b c : ℕ)
    (hw : (a : ℝ) + H * b + H * c ≤ 96 * H ^ (2 / 3 : ℝ) * U) :
    (b : ℝ) ≤ 96 * (H ^ (-(1 / 3 : ℝ)) * U) ∧
      (c : ℝ) ≤ 96 * (H ^ (-(1 / 3 : ℝ)) * U) := by
  have hs := pivot_primary_scale (U := U) hH
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : 0 ≤ H * b := mul_nonneg hH.le (Nat.cast_nonneg b)
  have hc : 0 ≤ H * c := mul_nonneg hH.le (Nat.cast_nonneg c)
  constructor
  · apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith
  · apply (mul_le_mul_iff_right₀ hH).mp
    nlinarith

theorem pivot_weight_of_rectangle {H U : ℝ} (hH : 0 < H) (a b c : ℕ)
    (ha : (a : ℝ) ≤ 32 * H ^ (2 / 3 : ℝ) * U)
    (hb : (b : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U)
    (hc : (c : ℝ) ≤ 32 * H ^ (-(1 / 3 : ℝ)) * U) :
    (a : ℝ) + H * b + H * c ≤ 96 * H ^ (2 / 3 : ℝ) * U := by
  have hs := pivot_primary_scale (U := U) hH
  have hbH := mul_le_mul_of_nonneg_left hb hH.le
  have hcH := mul_le_mul_of_nonneg_left hc hH.le
  nlinarith

end WeightedTorusJets

open scoped BigOperators

namespace WeightedTorusJets

theorem card_filter_lt_le_mul {ι : Type*} (s : Finset ι) (a : ι → ℕ) (Q t : ℕ)
    (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    (s.filter fun i => a i < t).card ≤ Q * t := by
  classical
  have h := Finset.card_le_mul_card_image_of_maps_to
    (s := s.filter fun i => a i < t) (t := Finset.range t) (f := a)
    (fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2) Q
    (fun k _ => le_trans (Finset.card_le_card (by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1,
          (Finset.mem_filter.mp hi).2⟩)) (hQ k))
  simpa using h

theorem card_sq_le_twice_mul_sum_add {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (Q : ℕ) (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    s.card * s.card ≤ 2 * Q * (∑ i ∈ s, a i) + Q * s.card := by
  classical
  have hswap :
      (∑ i ∈ s, (s.filter fun j => a i < a j).card) =
        ∑ i ∈ s, (s.filter fun j => a j < a i).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have hsplit : s.card * s.card =
      2 * (∑ i ∈ s, (s.filter fun j => a j < a i).card) +
        ∑ i ∈ s, (s.filter fun j => a j = a i).card := by
    calc
      s.card * s.card = ∑ i ∈ s, ∑ j ∈ s, (1 : ℕ) := by simp
      _ = ∑ i ∈ s, ∑ j ∈ s,
          ((if a j < a i then 1 else 0) + (if a i < a j then 1 else 0) +
            (if a j = a i then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> omega
      _ = (∑ i ∈ s, (s.filter fun j => a j < a i).card) +
          (∑ i ∈ s, (s.filter fun j => a i < a j).card) +
          ∑ i ∈ s, (s.filter fun j => a j = a i).card := by
        simp only [Finset.sum_add_distrib, ← Finset.card_filter]
      _ = _ := by rw [hswap]; omega
  have hlt : (∑ i ∈ s, (s.filter fun j => a j < a i).card) ≤
      Q * (∑ i ∈ s, a i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => card_filter_lt_le_mul s a Q (a i) hQ
  have heq : (∑ i ∈ s, (s.filter fun j => a j = a i).card) ≤ Q * s.card := by
    calc
      _ ≤ ∑ i ∈ s, Q := Finset.sum_le_sum fun i _ => hQ (a i)
      _ = _ := by simp [mul_comm]
  nlinarith

theorem sum_lower_of_bounded_multiplicity {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    (Q : ℕ) (hQpos : 0 < Q)
    (hQ : ∀ k, (s.filter fun i => a i = k).card ≤ Q) :
    (s.card : ℝ) ^ 2 / (2 * Q) - s.card / 2 ≤ ∑ i ∈ s, (a i : ℝ) := by
  have h : (s.card : ℝ) * s.card ≤
      2 * (Q : ℝ) * (∑ i ∈ s, (a i : ℝ)) + (Q : ℝ) * s.card := by
    exact_mod_cast card_sq_le_twice_mul_sum_add s a Q hQ
  have hQpos' : (0 : ℝ) < Q := by exact_mod_cast hQpos
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Q)]
  nlinarith

theorem coordinate_fiber_card_le (s : Finset (Fin 3 → ℕ)) (B k : ℕ)
    (hB : ∀ a ∈ s, a 1 ≤ B ∧ a 2 ≤ B) :
    (s.filter fun a => a 0 = k).card ≤ (B + 1) ^ 2 := by
  classical
  have h := Finset.card_le_card_of_injOn (s := s.filter fun a => a 0 = k)
    (t := Finset.range (B + 1) ×ˢ Finset.range (B + 1))
    (fun a => (a 1, a 2)) ?_ ?_
  · simpa [pow_two] using h
  · intro a ha
    have ha' := (Finset.mem_filter.mp ha).1
    obtain ⟨h1, h2⟩ := hB a ha'
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (show a 1 < B + 1 by omega),
      Finset.mem_range.mpr (show a 2 < B + 1 by omega)⟩
  · intro a ha b hb hab
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    have ha1 := congrArg Prod.fst hab
    have ha2 := congrArg Prod.snd hab
    funext i
    fin_cases i <;> simp_all

theorem first_coordinate_sum_lower (s : Finset (Fin 3 → ℕ)) (B : ℕ)
    (hB : ∀ a ∈ s, a 1 ≤ B ∧ a 2 ≤ B) :
    (s.card : ℝ) ^ 2 / (2 * ((B + 1 : ℕ) : ℝ) ^ 2) - s.card / 2 ≤
      ∑ a ∈ s, (a 0 : ℝ) := by
  have h := sum_lower_of_bounded_multiplicity s (fun a => a 0) ((B + 1)^2)
    (by positivity) (coordinate_fiber_card_le s B · hB)
  simpa using h



theorem weighted_pivot_bounds (P : Finset (Fin 3 → ℕ)) (H N : ℕ)
    (hH : 0 < H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hcard : P.card = N ^ 4)
    (hw : ∀ a ∈ P, (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) /
        (4 * 97 ^ 2) ≤ ∑ a ∈ P, (a 0 : ℝ) ∧
      (∑ a ∈ P, ((a 1 : ℝ) + a 2)) ≤
        192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ) := by
  let t : ℝ := (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHNreal : (H : ℝ) ≤ N := by exact_mod_cast hHN
  have hNreal : (18818 : ℝ) ≤ N := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have htone : 1 ≤ t := pivot_scale_ge_one hHone hHNreal
  have htpos : 0 < t := by linarith
  have hcardreal : (P.card : ℝ) = (N : ℝ) ^ 4 := by exact_mod_cast hcard
  have hcoords : ∀ a ∈ P, (a 1 : ℝ) ≤ 96 * t ∧ (a 2 : ℝ) ≤ 96 * t := by
    intro a ha
    exact pivot_coordinates_of_weight hHpos (a 0) (a 1) (a 2) (hw a ha)
  have hcoordsNat : ∀ a ∈ P, a 1 ≤ ⌊96 * t⌋₊ ∧ a 2 ≤ ⌊96 * t⌋₊ := by
    intro a ha
    exact ⟨Nat.le_floor (hcoords a ha).1, Nat.le_floor (hcoords a ha).2⟩
  have hlower := first_coordinate_sum_lower P ⌊96 * t⌋₊ hcoordsNat
  have hlarge : 2 * (((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2) ≤ P.card := by
    rw [hcardreal]
    exact pivot_floor_count_eventually hHone hHNreal hNreal
  have hscale : (P.card : ℝ) = (H : ℝ) * t ^ 3 := by
    rw [hcardreal]
    exact (pivot_scale_cube hHpos hNnonneg).symm
  have hfirst := pivot_lower_constant
    (show 0 < ((⌊96 * t⌋₊ + 1 : ℕ) : ℝ) ^ 2 by positivity)
    htpos hHpos hscale hlarge (pivot_floor_square_bound htone) hlower
  constructor
  · have hs := pivot_primary_scale (U := (N : ℝ) ^ (4 / 3 : ℝ)) hHpos
    change (H : ℝ) * t = _ at hs
    rw [hcardreal] at hfirst
    simpa only [mul_assoc, hs] using hfirst
  · have hsecond := pivot_second_sum_bound P (fun a => a 1) (fun a => a 2)
      (fun a ha => (hcoords a ha).1) (fun a ha => (hcoords a ha).2)
    rw [hcardreal] at hsecond
    simpa [t, mul_assoc] using hsecond

theorem weighted_pivot_ratio_le_twelfth (P : Finset (Fin 3 → ℕ)) (H N : ℕ)
    (hH : 86713344 ≤ H) (hHN : H ≤ N) (hcard : P.card = N ^ 4)
    (hw : ∀ a ∈ P, (a 0 : ℝ) + (H : ℝ) * a 1 + (H : ℝ) * a 2 ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    (∑ a ∈ P, ((a 1 : ℝ) + a 2)) / (∑ a ∈ P, (a 0 : ℝ)) ≤ 1 / 12 := by
  have hHpos : 0 < H := by omega
  have hHposreal : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hNposreal : (0 : ℝ) < N := by exact_mod_cast (hHpos.trans_le hHN)
  obtain ⟨hfirst, hsecond⟩ := weighted_pivot_bounds P H N hHpos hHN (by omega) hcard hw
  have hs := pivot_primary_scale (U := (N : ℝ) ^ (4 / 3 : ℝ)) hHposreal
  apply pivot_ratio_le_twelfth
    (M := (N : ℝ) ^ 4) (H := H)
    (t := (H : ℝ) ^ (-(1 / 3 : ℝ)) * (N : ℝ) ^ (4 / 3 : ℝ))
    (by positivity) (by exact_mod_cast hH) (by positivity)
  · simpa only [mul_assoc, hs] using hfirst
  · simpa only [mul_assoc] using hsecond



open Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

noncomputable def greedyPivots
    {V : Type u_1} [AddCommGroup V] (K : Type u_2) [DivisionRing K] (v : ℕ → V)
    [Module K V] : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => by
      classical
      exact if v n ∈ span K (v '' (greedyPivots K v n : Set ℕ))
        then greedyPivots K v n else insert n (greedyPivots K v n)

theorem greedyPivots_subset_range (v : ℕ → V) (n : ℕ) :
    greedyPivots K v n ⊆ Finset.range n := by
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs
      · exact ih.trans (Finset.range_mono (Nat.le_succ n))
      · exact Finset.insert_subset (Finset.mem_range.mpr (Nat.lt_succ_self n))
          (ih.trans (Finset.range_mono (Nat.le_succ n)))

theorem greedyPivots_linearIndepOn (v : ℕ → V) (n : ℕ) :
    LinearIndepOn K v (greedyPivots K v n : Set ℕ) := by
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs with h
      · exact ih
      · simpa only [Finset.coe_insert] using ih.insert h

theorem span_greedyPivots (v : ℕ → V) (n : ℕ) :
    span K (v '' (greedyPivots K v n : Set ℕ)) =
      span K (v '' (Finset.range n : Set ℕ)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      classical
      simp only [greedyPivots]
      split_ifs with h
      · rw [Finset.range_add_one, Finset.coe_insert, Set.image_insert_eq,
          span_insert_eq_span (ih ▸ h), ih]
      · rw [Finset.coe_insert, Finset.range_add_one, Finset.coe_insert,
          Set.image_insert_eq, Set.image_insert_eq, span_insert, span_insert, ih]

theorem mem_greedyPivots_succ_self (v : ℕ → V) (n : ℕ) :
    n ∈ greedyPivots K v (n + 1) ↔
      v n ∉ span K (v '' (Finset.range n : Set ℕ)) := by
  classical
  have hn : n ∉ greedyPivots K v n := fun h =>
    (Nat.lt_irrefl n) (Finset.mem_range.mp (greedyPivots_subset_range v n h))
  rw [greedyPivots, span_greedyPivots]
  split_ifs with h
  · exact iff_of_false hn (not_not_intro h)
  · exact iff_of_true (Finset.mem_insert_self _ _) h

theorem greedyPivots_mono (v : ℕ → V) : Monotone (greedyPivots K v) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  simp only [greedyPivots]
  split_ifs
  · rfl
  · exact Finset.subset_insert _ _

theorem mem_greedyPivots_iff (v : ℕ → V) (i n : ℕ) :
    i ∈ greedyPivots K v n ↔
      i < n ∧ v i ∉ span K (v '' (Finset.range i : Set ℕ)) := by
  classical
  induction n with
  | zero => simp [greedyPivots]
  | succ n ih =>
      by_cases hin : i < n
      · have hne : i ≠ n := Nat.ne_of_lt hin
        rw [greedyPivots]
        split_ifs
        · simpa only [hin, Nat.lt_succ_of_lt hin, true_and] using ih
        · simpa only [Finset.mem_insert, hne, false_or, hin,
            Nat.lt_succ_of_lt hin, true_and] using ih
      · by_cases hieq : i = n
        · subst i
          simpa only [Nat.lt_succ_self, true_and] using mem_greedyPivots_succ_self v n
        · have hnle : n + 1 ≤ i := by omega
          have hi : i ∉ greedyPivots K v (n + 1) := fun h =>
            (Nat.not_lt.mpr hnle)
              (Finset.mem_range.mp (greedyPivots_subset_range v (n + 1) h))
          exact iff_of_false hi (fun h => Nat.not_lt.mpr hnle h.1)

theorem card_greedyPivots (v : ℕ → V) (n : ℕ) :
    (greedyPivots K v n).card =
      Module.finrank K (span K (v '' (Finset.range n : Set ℕ))) := by
  classical
  have h := finrank_span_eq_card (greedyPivots_linearIndepOn (K := K) v n)
  rw [← Set.image_eq_range, span_greedyPivots] at h
  rw [Fintype.card_of_finset' (greedyPivots K v n) (fun _ => Iff.rfl)] at h
  exact h.symm

theorem earlier_row_mem_span_greedyPivots (v : ℕ → V) {i n : ℕ} (hi : i < n) :
    v i ∈ span K (v '' (greedyPivots K v n : Set ℕ)) := by
  rw [span_greedyPivots]
  exact subset_span ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem smaller_weight_row_mem_span_greedyPivots (v : ℕ → V) (w : ℕ → ℕ)
    (hw : Monotone w) {i n : ℕ} (hi : w i < w n) :
    v i ∈ span K (v '' (greedyPivots K v n : Set ℕ)) := by
  apply earlier_row_mem_span_greedyPivots
  exact lt_of_not_ge (fun h => (not_le_of_gt hi) (hw h))

theorem card_greedyPivots_of_span_eq_top (v : ℕ → V) (n : ℕ)
    (hspan : span K (v '' (Finset.range n : Set ℕ)) = ⊤) :
    (greedyPivots K v n).card = Module.finrank K V := by
  rw [card_greedyPivots, hspan, finrank_top]

theorem greedyPivots_eq_of_span_eq_top (v : ℕ → V) {n m : ℕ} (hnm : n ≤ m)
    (hspan : span K (v '' (Finset.range n : Set ℕ)) = ⊤) :
    greedyPivots K v n = greedyPivots K v m := by
  have hspanm : span K (v '' (Finset.range m : Set ℕ)) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact span_mono (Set.image_mono (Finset.range_mono hnm))
  apply Finset.eq_of_subset_of_card_le (greedyPivots_mono v hnm)
  rw [card_greedyPivots_of_span_eq_top v n hspan,
    card_greedyPivots_of_span_eq_top v m hspanm]

end WeightedTorusJets

namespace WeightedTorusJets

theorem exists_weight_sorted_enumeration {α : Type*} (s : Finset α) (w : α → ℕ) :
    ∃ e : Fin s.card ≃ s, Monotone (fun i => w (e i)) := by
  classical
  let l : List s := (Finset.univ : Finset s).toList.mergeSort
    (fun a b => decide (w a ≤ w b))
  have hlen : l.length = s.card := by simp [l]
  have hnd : l.Nodup :=
    ((Finset.univ : Finset s).nodup_toList).mergeSort
  have hmem : ∀ x : s, x ∈ l := by simp [l]
  have hpw : l.Pairwise (fun a b : s => w a ≤ w b) := by
    have h := List.pairwise_mergeSort
      (le := fun a b : s => decide (w a ≤ w b))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hab hbc)
      (fun a b => by simp [le_total (w a) (w b)]) (Finset.univ : Finset s).toList
    simpa only [decide_eq_true_eq] using h
  refine ⟨(finCongr hlen.symm).trans (hnd.getEquivOfForallMemList l hmem), ?_⟩
  intro i j hij
  change w (l.get (Fin.cast hlen.symm i)) ≤ w (l.get (Fin.cast hlen.symm j))
  exact hpw.rel_get_of_le hij

def extendFiniteFamily {α : Type*} {n : ℕ} (f : Fin n → α) (fallback : α) (i : ℕ) : α :=
  if hi : i < n then f ⟨i, hi⟩ else fallback

theorem image_extendFiniteFamily_range {α : Type*} {n : ℕ} (f : Fin n → α)
    (fallback : α) :
    extendFiniteFamily f fallback '' (Finset.range n : Set ℕ) = Set.range f := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hin : i < n := Finset.mem_range.mp hi
    exact ⟨⟨i, hin⟩, by simp [extendFiniteFamily, hin]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, Finset.mem_range.mpr i.isLt, by simp [extendFiniteFamily, i.isLt]⟩

theorem monotone_extendFiniteFamily {α : Type*} [Preorder α] {n : ℕ}
    (f : Fin n → α) (fallback : α) (hf : Monotone f) (hb : ∀ i, f i ≤ fallback) :
    Monotone (extendFiniteFamily f fallback) := by
  intro i j hij
  simp only [extendFiniteFamily]
  split_ifs with hi hj hj
  · exact hf hij
  · exact hb _
  · exact (hi (lt_of_le_of_lt hij hj)).elim
  · exact le_rfl

theorem exists_weight_sorted_cutoff_sequence {α β : Type*} (s : Finset α)
    (w : α → ℕ) (R : α → β) (fallback : β) (B : ℕ)
    (hs : ∀ a, a ∈ s ↔ w a ≤ B) :
    ∃ (v : ℕ → β) (wt : ℕ → ℕ), Monotone wt ∧
      v '' (Finset.range s.card : Set ℕ) = R '' (s : Set α) ∧
      (∀ a, w a ≤ B → ∃ i < s.card, v i = R a ∧ wt i = w a) ∧
      (∀ i < s.card, ∃ a ∈ s, v i = R a ∧ wt i = w a) := by
  classical
  obtain ⟨e, he⟩ := exists_weight_sorted_enumeration s w
  let v := extendFiniteFamily (fun i => R (e i)) fallback
  let wt := extendFiniteFamily (fun i => w (e i)) B
  have hb : ∀ i, w (e i) ≤ B := fun i => (hs _).mp (e i).property
  refine ⟨v, wt, monotone_extendFiniteFamily _ _ he hb, ?_, ?_, ?_⟩
  · change extendFiniteFamily (fun i => R (e i)) fallback '' _ = _
    rw [image_extendFiniteFamily_range]
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, (e i).property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨e.symm ⟨a, ha⟩, by simp⟩
  · intro a ha
    let i := e.symm ⟨a, (hs a).mpr ha⟩
    refine ⟨i, i.isLt, ?_, ?_⟩
    · simp [v, extendFiniteFamily, i.isLt, i]
    · simp [wt, extendFiniteFamily, i.isLt, i]
  · intro i hi
    refine ⟨e ⟨i, hi⟩, (e ⟨i, hi⟩).property, ?_, ?_⟩
    · simp [v, extendFiniteFamily, hi]
    · simp [wt, extendFiniteFamily, hi]

end WeightedTorusJets


end SiegelZeros

end OAI
