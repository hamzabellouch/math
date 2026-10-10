import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval

namespace CannonGrid

def hat (x y : ℝ) : ℝ := max 0 (1 - max |x| (max |y| |x-y|))

lemma hat_nonneg (x y : ℝ) : 0 ≤ hat x y := le_max_left ..

lemma continuous_hat : Continuous (fun p : ℝ × ℝ => hat p.1 p.2) := by
  exact continuous_const.max (continuous_const.sub
    (continuous_fst.abs.max (continuous_snd.abs.max (continuous_fst.sub continuous_snd).abs)))

lemma hat_ne_zero {x y : ℝ} (h : hat x y ≠ 0) : |x| < 1 ∧ |y| < 1 := by
  have hh : 0 < hat x y := lt_of_le_of_ne (hat_nonneg x y) h.symm
  rw [hat, lt_max_iff] at hh
  have ht : max |x| (max |y| |x-y|) < 1 := by rcases hh with hh | hh <;> linarith
  exact ⟨(le_max_left ..).trans_lt ht, ((le_max_left ..).trans (le_max_right ..)).trans_lt ht⟩

lemma hat_zero_of_one_le_abs_left {x y : ℝ} (h : 1 ≤ |x|) : hat x y = 0 := by
  by_contra hn
  exact (not_lt_of_ge h) (hat_ne_zero hn).1

lemma hat_zero_of_one_le_abs_right {x y : ℝ} (h : 1 ≤ |y|) : hat x y = 0 := by
  by_contra hn
  exact (not_lt_of_ge h) (hat_ne_zero hn).2

lemma hat_neg (x y : ℝ) : hat (-x) (-y) = hat x y := by
  simp only [hat, abs_neg]
  congr 3
  rw [show -x - -y = -(x-y) by ring, abs_neg]

lemma hat_on_square {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat x y = 1-max x y := by
  have ha : |x-y| ≤ max x y := abs_le.mpr ⟨by
    have := le_max_right x y
    linarith [hx.1], by
    have := le_max_left x y
    linarith [hy.1]⟩
  have he : max |x| (max |y| |x-y|) = max x y := by
    rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]
    apply le_antisymm
    · exact max_le (le_max_left ..) (max_le (le_max_right ..) ha)
    · exact max_le (le_max_left ..) ((le_max_left ..).trans (le_max_right ..))
  rw [hat, he, max_eq_right]
  exact sub_nonneg.mpr (max_le hx.2 hy.2)

lemma hat_on_square_right {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat (x-1) y = max 0 (x-y) := by
  have hx' : x-1 ≤ 0 := by linarith [hx.2]
  have hxy : x-1-y ≤ 0 := by linarith [hx.2,hy.1]
  have hm : max (-(x-1)) (max y (-(x-1-y))) = -(x-1-y) := by
    have h₁ : y ≤ -(x-1-y) := by linarith [hx.2]
    rw [max_eq_right h₁, max_eq_right (by linarith [hy.1])]
  simp only [hat, abs_of_nonpos hx', abs_of_nonneg hy.1, abs_of_nonpos hxy, hm]
  congr 1
  ring

lemma hat_comm (x y : ℝ) : hat x y = hat y x := by
  unfold hat
  rw [abs_sub_comm x y, max_left_comm |x| |y|]

lemma hat_on_square_top {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat x (y-1) = max 0 (y-x) := by
  rw [hat_comm]
  exact hat_on_square_right hy hx

lemma hat_on_square_diag {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat (x-1) (y-1) = min x y := by
  rw [show x-1 = -(1-x) by ring, show y-1 = -(1-y) by ring, hat_neg]
  rw [hat_on_square ⟨by linarith [hx.2],by linarith [hx.1]⟩
    ⟨by linarith [hy.2],by linarith [hy.1]⟩]
  by_cases h : x ≤ y
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · have hh := le_of_not_ge h
    rw [min_eq_right hh, max_eq_right (by linarith)]
    ring

lemma four_hats {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    hat x y + hat x (y-1) + (hat (x-1) y + hat (x-1) (y-1)) = 1 := by
  rw [hat_on_square hx hy, hat_on_square_right hx hy,
    hat_on_square_top hx hy, hat_on_square_diag hx hy]
  by_cases h : x ≤ y
  · rw [max_eq_right h, min_eq_left h, max_eq_right (by linarith : 0 ≤ y-x),
      max_eq_left (by linarith : x-y ≤ 0)]
    ring
  · have hh := le_of_not_ge h
    rw [max_eq_left hh, min_eq_right hh, max_eq_left (by linarith : y-x ≤ 0),
      max_eq_right (by linarith : 0 ≤ x-y)]
    ring

lemma grid_cell {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Icc 0 (N:ℝ)) :
    ∃ k : ℕ, k < N ∧ (k:ℝ) ≤ x ∧ x ≤ k+1 := by
  by_cases h : x < N
  · exact ⟨Nat.floor x, (Nat.floor_lt hx.1).mpr h, Nat.floor_le hx.1,
      (Nat.lt_floor_add_one x).le⟩
  · have hxN : x = N := le_antisymm hx.2 (le_of_not_gt h)
    refine ⟨N-1, by omega, ?_, ?_⟩
    all_goals rw [hxN, Nat.cast_sub (by omega : 1 ≤ N)]; norm_num

lemma nat_eq_or_succ_of_abs_lt {k i : ℕ} {x : ℝ}
    (hx : (k:ℝ) ≤ x ∧ x ≤ k+1) (hi : |x-i| < 1) : i = k ∨ i = k+1 := by
  have hi' := abs_lt.mp hi
  by_contra h
  push Not at h
  have hcases : i+1 ≤ k ∨ k+2 ≤ i := by omega
  rcases hcases with h | h
  · have hh : (i:ℝ)+1 ≤ k := by exact_mod_cast h
    linarith [hx.1,hi'.2]
  · have hh : (k:ℝ)+2 ≤ i := by exact_mod_cast h
    linarith [hx.2,hi'.1]

lemma sum_two {ι : Type*} [Fintype ι] (f : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = 0) : (∑ k, f k) = f i + f j := by
  classical
  have he : ∑ k ∈ ({i,j} : Finset ι), f k = ∑ k, f k := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    exact h k (fun he => hk (by simp [he])) (fun he => hk (by simp [he]))
  rw [← he]
  simp [hij]

theorem grid_partition {N : ℕ} (hN : 0 < N) {x y : ℝ}
    (hx : x ∈ Icc 0 (N:ℝ)) (hy : y ∈ Icc 0 (N:ℝ)) :
    (∑ i : Fin (N+1), ∑ j : Fin (N+1), hat (x-i) (y-j)) = 1 := by
  obtain ⟨k,hk,hkx⟩ := grid_cell hN hx
  obtain ⟨l,hl,hly⟩ := grid_cell hN hy
  let k₀ : Fin (N+1) := ⟨k,by omega⟩
  let k₁ : Fin (N+1) := ⟨k+1,by omega⟩
  let l₀ : Fin (N+1) := ⟨l,by omega⟩
  let l₁ : Fin (N+1) := ⟨l+1,by omega⟩
  have hkne : k₀ ≠ k₁ := by intro h; have := congrArg Fin.val h; dsimp [k₀,k₁] at this; omega
  have hlne : l₀ ≠ l₁ := by intro h; have := congrArg Fin.val h; dsimp [l₀,l₁] at this; omega
  have hrow : ∀ i : Fin (N+1), i ≠ k₀ → i ≠ k₁ → ∀ j : Fin (N+1),
      hat (x-i) (y-j) = 0 := by
    intro i hi₀ hi₁ j
    by_contra hh
    rcases nat_eq_or_succ_of_abs_lt hkx (hat_ne_zero hh).1 with hh | hh
    · exact hi₀ (Fin.ext hh)
    · exact hi₁ (Fin.ext hh)
  have hcol : ∀ j : Fin (N+1), j ≠ l₀ → j ≠ l₁ → ∀ i : Fin (N+1),
      hat (x-i) (y-j) = 0 := by
    intro j hj₀ hj₁ i
    by_contra hh
    rcases nat_eq_or_succ_of_abs_lt hly (hat_ne_zero hh).2 with hh | hh
    · exact hj₀ (Fin.ext hh)
    · exact hj₁ (Fin.ext hh)
  rw [sum_two _ k₀ k₁ hkne (by intro i hi₀ hi₁; simp [hrow i hi₀ hi₁])]
  rw [sum_two _ l₀ l₁ hlne (by intro j hj₀ hj₁; exact hcol j hj₀ hj₁ k₀)]
  rw [sum_two _ l₀ l₁ hlne (by intro j hj₀ hj₁; exact hcol j hj₀ hj₁ k₁)]
  change hat (x-(k:ℝ)) (y-(l:ℝ)) + hat (x-k) (y-(l+1:ℕ)) +
    (hat (x-(k+1:ℕ)) (y-l) + hat (x-(k+1:ℕ)) (y-(l+1:ℕ))) = 1
  simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]
  exact four_hats ⟨by linarith [hkx.1],by linarith [hkx.2]⟩
    ⟨by linarith [hly.1],by linarith [hly.2]⟩

end CannonGrid

namespace CannonGrid

open unitInterval

abbrev Square := I × I

abbrev Index (N : ℕ) := Fin (N+1) × Fin (N+1)

def vertex (N : ℕ) (hN : 0 < N) (i : Index N) : Square :=
  (⟨(i.1:ℝ)/N, ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.1.isLt)⟩⟩,
   ⟨(i.2:ℝ)/N, ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast Nat.le_of_lt_succ i.2.isLt)⟩⟩)

def weight (N : ℕ) (z : Square) (i : Index N) : ℝ :=
  hat (N*(z.1:ℝ)-i.1) (N*(z.2:ℝ)-i.2)

def interpolate (N : ℕ) (hN : 0 < N) (f : Square → ℝ) (z : Square) : ℝ :=
  ∑ i : Index N, weight N z i * f (vertex N hN i)

lemma weight_nonneg (N : ℕ) (z : Square) (i : Index N) : 0 ≤ weight N z i :=
  hat_nonneg ..

lemma weight_partition (N : ℕ) (hN : 0 < N) (z : Square) :
    (∑ i : Index N, weight N z i) = 1 := by
  rw [Fintype.sum_prod_type]
  apply grid_partition hN
  · exact ⟨mul_nonneg (Nat.cast_nonneg _) z.1.property.1,
      by simpa using mul_le_mul_of_nonneg_left z.1.property.2 (Nat.cast_nonneg N : (0:ℝ) ≤ N)⟩
  · exact ⟨mul_nonneg (Nat.cast_nonneg _) z.2.property.1,
      by simpa using mul_le_mul_of_nonneg_left z.2.property.2 (Nat.cast_nonneg N : (0:ℝ) ≤ N)⟩

lemma continuous_weight (N : ℕ) (i : Index N) : Continuous (fun z : Square => weight N z i) := by
  unfold weight
  exact continuous_hat.comp (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
      continuous_const).prodMk
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))

theorem continuous_interpolate (N : ℕ) (hN : 0 < N) (f : Square → ℝ) :
    Continuous (interpolate N hN f) := by
  apply continuous_finsetSum
  intro i _
  exact (continuous_weight N i).mul continuous_const

lemma interpolate_bounds_of_support (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (z : Square) (a b : ℝ)
    (hf : ∀ i, weight N z i ≠ 0 → f (vertex N hN i) ∈ Icc a b) :
    interpolate N hN f z ∈ Icc a b := by
  constructor
  · calc
      a = (∑ i : Index N, weight N z i)*a := by rw [weight_partition N hN z,one_mul]
      _ = ∑ i : Index N, weight N z i*a := Finset.sum_mul ..
      _ ≤ interpolate N hN f z := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : weight N z i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left (hf i hi).1 (weight_nonneg ..)
  · calc
      interpolate N hN f z ≤ ∑ i : Index N, weight N z i*b := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : weight N z i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left (hf i hi).2 (weight_nonneg ..)
      _ = (∑ i : Index N, weight N z i)*b := (Finset.sum_mul ..).symm
      _ = b := by rw [weight_partition N hN z,one_mul]

lemma interpolate_bounds (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (hf : ∀ z, f z ∈ Icc 0 1) (z : Square) :
    interpolate N hN f z ∈ Icc 0 1 :=
  interpolate_bounds_of_support N hN f z 0 1 (fun _ _ => hf _)

lemma interpolate_eq_of_support (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (z : Square) (c : ℝ) (hf : ∀ i, weight N z i ≠ 0 → f (vertex N hN i) = c) :
    interpolate N hN f z = c := by
  have hh := interpolate_bounds_of_support N hN f z c c (by intro i hi; simp [hf i hi])
  exact le_antisymm hh.2 hh.1

lemma support_below {N : ℕ} {z : Square} {i : Index N} {k : ℕ}
    (hz : N*(z.2:ℝ) ≤ k) (hi : weight N z i ≠ 0) : i.2.val ≤ k := by
  have hh := (abs_lt.mp (hat_ne_zero hi).2).1
  have hr : (i.2.val:ℝ) < (k:ℝ)+1 := by linarith
  have hn : i.2.val < k+1 := by exact_mod_cast hr
  omega

lemma support_above {N : ℕ} {z : Square} {i : Index N} {k : ℕ}
    (hz : (k:ℝ) ≤ N*(z.2:ℝ)) (hi : weight N z i ≠ 0) : k ≤ i.2.val := by
  have hh := (abs_lt.mp (hat_ne_zero hi).2).2
  have hr : (k:ℝ) < (i.2.val:ℝ)+1 := by linarith
  have hn : k < i.2.val+1 := by exact_mod_cast hr
  omega

theorem interpolate_const_below (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (c : ℝ) (k : ℕ) (hf : ∀ i, i.2.val ≤ k → f (vertex N hN i) = c)
    (z : Square) (hz : N*(z.2:ℝ) ≤ k) : interpolate N hN f z = c := by
  apply interpolate_eq_of_support
  intro i hi
  exact hf i (support_below hz hi)

theorem interpolate_const_above (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (c : ℝ) (k : ℕ) (hf : ∀ i, k ≤ i.2.val → f (vertex N hN i) = c)
    (z : Square) (hz : (k:ℝ) ≤ N*(z.2:ℝ)) : interpolate N hN f z = c := by
  apply interpolate_eq_of_support
  intro i hi
  exact hf i (support_above hz hi)

theorem interpolate_preserves_bands (n : ℕ) (hn : 0 < n) (f : Square → ℝ)
    (hT : ∀ z, (z.2:ℝ) ≤ 1/3 → f z = 0)
    (hB : ∀ z, 2/3 ≤ (z.2:ℝ) → f z = 1) :
    (∀ z : Square, (z.2:ℝ) ≤ 1/3 → interpolate (3*n) (by omega) f z = 0) ∧
    (∀ z : Square, 2/3 ≤ (z.2:ℝ) → interpolate (3*n) (by omega) f z = 1) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hden : (0:ℝ) < (3*n:ℕ) := by positivity
  constructor
  · intro z hz
    apply interpolate_const_below (3*n) (by omega) f 0 n
    · intro i hi
      apply hT
      change (i.2.val:ℝ)/(3*n:ℕ) ≤ 1/3
      apply (div_le_iff₀ hden).mpr
      have hh : (i.2.val:ℝ) ≤ n := by exact_mod_cast hi
      push_cast
      nlinarith
    · push_cast
      nlinarith
  · intro z hz
    apply interpolate_const_above (3*n) (by omega) f 1 (2*n)
    · intro i hi
      apply hB
      change 2/3 ≤ (i.2.val:ℝ)/(3*n:ℕ)
      apply (le_div_iff₀ hden).mpr
      have hh : ((2*n:ℕ):ℝ) ≤ i.2.val := by exact_mod_cast hi
      push_cast at hh ⊢
      nlinarith
    · push_cast
      nlinarith

theorem support_dist {N : ℕ} (hN : 0 < N) {z : Square} {i : Index N}
    (hi : weight N z i ≠ 0) : dist z (vertex N hN i) < 1/(N:ℝ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hx := (hat_ne_zero hi).1
  have hy := (hat_ne_zero hi).2
  rw [Prod.dist_eq, max_lt_iff]
  change |(z.1:ℝ)-(i.1.val:ℝ)/N| < 1/(N:ℝ) ∧
    |(z.2:ℝ)-(i.2.val:ℝ)/N| < 1/(N:ℝ)
  have helper : ∀ a b : ℝ, |(N:ℝ)*a-b| < 1 → |a-b/N| < 1/(N:ℝ) := by
    intro a b h
    rw [show a-b/N = ((N:ℝ)*a-b)/N by field_simp, abs_div,
      abs_of_pos hn, div_lt_div_iff_of_pos_right hn]
    exact h
  exact ⟨helper _ _ hx, helper _ _ hy⟩

end CannonGrid

namespace CannonGrid

lemma one_le_abs_nat_sub {i j : ℕ} (h : i ≠ j) : (1:ℝ) ≤ |(i:ℝ)-j| := by
  rcases lt_or_gt_of_ne h with hh | hh
  · have hr : (i:ℝ)+1 ≤ j := by exact_mod_cast hh
    have := neg_le_abs ((i:ℝ)-j)
    linarith
  · have hr : (j:ℝ)+1 ≤ i := by exact_mod_cast hh
    have := le_abs_self ((i:ℝ)-j)
    linarith

lemma weight_vertex (N : ℕ) (hN : 0 < N) (i j : Index N) :
    weight N (vertex N hN i) j = if i = j then 1 else 0 := by
  classical
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hx : (N:ℝ)*((i.1.val:ℝ)/N) = i.1.val := by field_simp
  have hy : (N:ℝ)*((i.2.val:ℝ)/N) = i.2.val := by field_simp
  change hat ((N:ℝ)*((i.1.val:ℝ)/N)-j.1.val)
    ((N:ℝ)*((i.2.val:ℝ)/N)-j.2.val) = _
  rw [hx,hy]
  by_cases hij : i = j
  · subst j
    simp [hat]
  · rw [ite_eq_right hij]
    by_cases h₁ : i.1.val = j.1.val
    · have h₂ : i.2.val ≠ j.2.val := by
        intro h₂
        exact hij (Prod.ext (Fin.ext h₁) (Fin.ext h₂))
      exact hat_zero_of_one_le_abs_right (one_le_abs_nat_sub h₂)
    · exact hat_zero_of_one_le_abs_left (one_le_abs_nat_sub h₁)

theorem interpolate_vertex (N : ℕ) (hN : 0 < N) (f : Square → ℝ) (i : Index N) :
    interpolate N hN f (vertex N hN i) = f (vertex N hN i) := by
  classical
  simp [interpolate,weight_vertex]

theorem interpolate_variation (N : ℕ) (hN : 0 < N) (f : Square → ℝ)
    (z w : Square) (E : ℝ)
    (hf : ∀ i j, weight N z i ≠ 0 → weight N w j ≠ 0 →
      |f (vertex N hN i)-f (vertex N hN j)| ≤ E) :
    |interpolate N hN f z-interpolate N hN f w| ≤ E := by
  have hi : ∀ i, weight N z i ≠ 0 → f (vertex N hN i) ∈
      Set.Icc (interpolate N hN f w-E) (interpolate N hN f w+E) := by
    intro i hi
    have hh := interpolate_bounds_of_support N hN f w
      (f (vertex N hN i)-E) (f (vertex N hN i)+E) (by
        intro j hj
        have hb := abs_sub_le_iff.mp (hf i j hi hj)
        constructor <;> linarith [hb.1,hb.2])
    constructor <;> linarith [hh.1,hh.2]
  have hh := interpolate_bounds_of_support N hN f z _ _ hi
  exact abs_sub_le_iff.mpr ⟨by linarith [hh.2],by linarith [hh.1]⟩

theorem exists_metric_mesh {X : Type*} [PseudoMetricSpace X] (e : Square → X)
    (he : Continuous e) {r : ℝ} (hr : 0 < r) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∀ z : Square, ∀ i : Index (3*n),
      weight (3*n) z i ≠ 0 → dist (e z) (e (vertex (3*n) (by omega) i)) < r := by
  obtain ⟨δ,hδ,hcont⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous he) r hr
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m+1,by omega,?_⟩
  intro z i hi
  apply hcont
  have hs := support_dist (by omega : 0 < 3*(m+1)) hi
  apply hs.trans
  apply lt_of_le_of_lt _ hm
  have hh : (0:ℝ) < m+1 := by positivity
  push_cast
  apply one_div_le_one_div_of_le hh
  nlinarith

end CannonGrid

end
end
end
end
end
end
end
end
end

end OAI
