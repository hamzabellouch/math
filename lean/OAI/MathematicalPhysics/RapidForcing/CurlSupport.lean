import OAI.MathematicalPhysics.RapidForcing.Support
import OAI.MathematicalPhysics.RapidForcing.Profiles

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma supportBox_subset_of_center {c c' : Space} {r R : ℝ}
    (h : ∀ i : Fin 3, |c' i - c i| + r ≤ R) :
    supportBox c' r ⊆ supportBox c R := by
  intro x hx i
  calc
    |x i - c i| = |(x i - c' i) + (c' i - c i)| := by congr 1; ring
    _ ≤ |x i - c' i| + |c' i - c i| := abs_add_le _ _
    _ ≤ R := by have := hx i; have := h i; linarith

lemma supportBox_subset_K {c : Space} {r : ℝ} (hr : r ≤ 1)
    (hx : -1 ≤ c 0 ∧ c 0 ≤ 0) (hy : 0 ≤ c 1 ∧ c 1 ≤ 1) (hz : c 2 = 0) :
    supportBox c r ⊆ K := by
  intro x hxbox
  have h0 := abs_le.mp (hxbox 0)
  have h1 := abs_le.mp (hxbox 1)
  have h2 := abs_le.mp (hxbox 2)
  change -2 ≤ x 0 ∧ x 0 ≤ 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ 2 ∧
    -1 ≤ x 2 ∧ x 2 ≤ 1
  constructor
  · linarith [hx.1]
  constructor
  · linarith [hx.2]
  constructor
  · linarith [hy.1]
  constructor
  · linarith [hy.2]
  constructor <;> linarith

lemma grid_coordinate_mem {d : ScaleData} {n m : ℕ} (hm : m ≤ d.D n) :
    0 ≤ (m : ℝ) * d.δ n ∧ (m : ℝ) * d.δ n ≤ 1 := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (d.delta_nonneg _), ?_⟩
  rw [d.delta_eq_inv_D, ← div_eq_mul_inv]
  exact (div_le_one (Nat.cast_pos.mpr (d.D_pos _))).mpr (Nat.cast_le.mpr hm)

lemma addressDisplacement_bound (M : Machine) (w : M.Input) (n m : ℕ) (i : Fin 3) :
    |addressDisplacement M (M.scaleData w) n m i| ≤ (M.scaleData w).b n := by
  let d := M.scaleData w
  have hb := (d.b_pos n).le
  have hδ := d.delta_nonneg (n + 1)
  have hd : (M.terminalDigit d (m % d.capacity n) : ℝ) ≤ 1 :=
    Nat.cast_le_one.mpr (M.terminalDigit_le_one _ _)
  have hd0 : (0 : ℝ) ≤ (M.terminalDigit d (m % d.capacity n) : ℝ) := Nat.cast_nonneg _
  have hn : (M.nextDigit d n (m % d.capacity n) : ℝ) ≤ (d.capacity (n + 1) : ℝ) :=
    Nat.cast_le.mpr (M.nextDigit_lt w (Nat.mod_lt _ (d.capacity_pos n))).le
  fin_cases i
  · change |-d.b n * (M.terminalDigit d (m % d.capacity n) : ℝ)| ≤ d.b n
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) hd0)]
    nlinarith
  · change |d.δ (n + 1) * (M.nextDigit d n (m % d.capacity n) : ℝ)| ≤ d.b n
    rw [abs_of_nonneg (mul_nonneg hδ (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left hn hδ
  · change |(0 : ℝ)| ≤ d.b n
    simpa using hb

lemma addressPath_bound (M : Machine) (w : M.Input) (n m : ℕ) (σ : ℝ) (i : Fin 3) :
    |addressPath M (M.scaleData w) n m σ i - addressCenter (M.scaleData w) n m i| ≤
      (M.scaleData w).b n := by
  have h := addressDisplacement_bound M w n m i
  change |(addressCenter (M.scaleData w) n m i +
    θ σ * addressDisplacement M (M.scaleData w) n m i) -
      addressCenter (M.scaleData w) n m i| ≤ _
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (theta_nonneg σ)]
  exact (mul_le_mul_of_nonneg_left h (theta_nonneg σ)).trans
    (mul_le_of_le_one_left (M.scaleData w |>.b_pos n).le (theta_le_one σ))

lemma addressCurl_tsupport_subset_box (M : Machine) (w : M.Input)
    (n m : ℕ) (σ : ℝ) :
    tsupport (movingCurl (addressPath M (M.scaleData w) n m)
      ((M.scaleData w).δ n) σ) ⊆
        supportBox (addressCenter (M.scaleData w) n m) ((M.scaleData w).δ n / 4) := by
  apply (movingCurl_tsupport_subset _ ((M.scaleData w).delta_pos n) _).trans
  apply supportBox_subset_of_center
  intro i
  have := addressPath_bound M w n m σ i
  have := (M.scaleData w).b_lt_delta_div_eight n
  linarith

lemma addressCurl_tsupport_subset_K (M : Machine) (w : M.Input)
    (n m : ℕ) (hm : m ≤ (M.scaleData w).D n) (σ : ℝ) :
    tsupport (movingCurl (addressPath M (M.scaleData w) n m)
      ((M.scaleData w).δ n) σ) ⊆ K := by
  apply (addressCurl_tsupport_subset_box M w n m σ).trans
  apply supportBox_subset_K
  · have := (M.scaleData w).delta_le_one n; linarith
  · exact ⟨le_refl _, by norm_num [addressCenter]⟩
  · exact grid_coordinate_mem hm
  · rfl

lemma initial_coordinate_mem (M : Machine) (w : M.Input) :
    0 ≤ (M.scaleData w).δ 0 * (M.initialDigit w : ℝ) ∧
      (M.scaleData w).δ 0 * (M.initialDigit w : ℝ) < 1 := by
  refine ⟨mul_nonneg ((M.scaleData w).delta_nonneg _) (Nat.cast_nonneg _), ?_⟩
  calc
    (M.scaleData w).δ 0 * (M.initialDigit w : ℝ) <
        (M.scaleData w).δ 0 * ((M.scaleData w).capacity 0 : ℝ) :=
      mul_lt_mul_of_pos_left (Nat.cast_lt.mpr (M.initialDigit_lt w))
        ((M.scaleData w).delta_pos _)
    _ ≤ (1 / 2 : ℝ) ^ (15 * (0 + 1)) := (M.scaleData w).delta_capacity_le 0
    _ < 1 := by norm_num

lemma loadingCurl_tsupport_subset_K (M : Machine) (w : M.Input) (t : ℝ) :
    tsupport (movingCurl (fun s => θ s •
      vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0) 1 t) ⊆ K := by
  apply (movingCurl_tsupport_subset _ (by norm_num : (0 : ℝ) < 1) _).trans
  apply supportBox_subset_K
  · norm_num
  · change -1 ≤ θ t * (-1) ∧ θ t * (-1) ≤ 0
    constructor <;> linarith [theta_nonneg t, theta_le_one t]
  · change 0 ≤ θ t * ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) ∧
      θ t * ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) ≤ 1
    obtain ⟨hy, hy'⟩ := initial_coordinate_mem M w
    exact ⟨mul_nonneg (theta_nonneg t) hy,
      (mul_le_of_le_one_left hy (theta_le_one t)).trans hy'.le⟩
  · simp

theorem addressedVelocity_supported (M : Machine) (w : M.Input) :
    Supported (addressedVelocity M w) := by
  apply supported_iff_zero_off.mpr
  intro t _ x hx
  unfold addressedVelocity
  split_ifs with ht
  · apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hx (loadingCurl_tsupport_subset_K M w t h)
  · apply Finset.sum_eq_zero
    intro m hm
    apply image_eq_zero_of_notMem_tsupport
    intro h
    apply hx
    exact addressCurl_tsupport_subset_K M w _ m
      (Nat.le_of_lt_succ (Finset.mem_range.mp hm)) _ h

lemma Supported.residual {u : Field Space} (hu : Supported u) (ν : ℝ) :
    Supported (residual ν u) := by
  apply supported_iff_zero_off.mpr
  intro t ht x hx
  have htD := hu.timeD.zero_off ht hx
  have hL : laplace u t x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact ((hu.spatialD i).spatialD i).zero_off ht hx
  have hA : advection u t x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [(hu.spatialD i).zero_off ht hx, smul_zero]
  change RapidForcing.timeD u t x + advection u t x - ν • laplace u t x = 0
  rw [htD, hA, hL]
  simp

theorem addressedForce_supported (ν : ℝ) (M : Machine) (w : M.Input) :
    Supported (addressedForce ν M w) :=
  (addressedVelocity_supported M w).residual ν

end RapidForcing

end OAI
