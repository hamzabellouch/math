import OAI.Geometry.CylinderCovering.Angular.EndpointDefinitions
import OAI.Geometry.CylinderCovering.Angular.Sampling

namespace OAI

noncomputable section
namespace AngularEndpoint

@[simp] lemma node_zero (N : ℕ) : node N 0 = -1 := by simp [node]

@[simp] lemma node_last {N : ℕ} (hN : 0 < N) : node N N = 1 := by
  unfold node
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma node_succ (N j : ℕ) : node N (j + 1) = node N j + 2 / (N : ℝ) := by
  simp only [node, Nat.cast_add, Nat.cast_one]
  ring

lemma node_bounds {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    -1 ≤ node N j ∧ node N j ≤ 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  unfold node
  constructor
  · have : 0 ≤ 2 * (j : ℝ) / (N : ℝ) := by positivity
    linarith
  · have := (div_le_iff₀ hn).2 (show 2 * (j : ℝ) ≤ 2 * N by linarith)
    linarith

@[simp] lemma boundary_zero (N : ℕ) : boundary N 0 = -1 := by simp [boundary]

@[simp] lemma boundary_last (N : ℕ) : boundary N (N + 1) = 1 := by simp [boundary]

lemma boundary_interior {N j : ℕ} (hj : 0 < j) (hjN : j ≤ N) :
    boundary N j = node N j - 1 / (N : ℝ) := by
  have hj0 : j ≠ 0 := by omega
  have hjlast : j ≠ N + 1 := by omega
  rw [boundary, ite_eq_right hj0, ite_eq_right hjlast]
  have hpred : j - 1 + 1 = j := by omega
  have hsucc := node_succ N (j - 1)
  rw [hpred] at hsucc
  ring_nf at hsucc ⊢
  linarith

lemma left_boundary {N j : ℕ} (hj : j ≤ N) :
    boundary N j = if j = 0 then -1 else node N j - 1 / (N : ℝ) := by
  by_cases hj0 : j = 0
  · simp [hj0]
  · rw [ite_eq_right hj0]
    exact boundary_interior (by omega) hj

lemma right_boundary {N j : ℕ} (hj : j ≤ N) :
    boundary N (j + 1) = if j = N then 1 else node N j + 1 / (N : ℝ) := by
  by_cases hjN : j = N
  · simp [hjN]
  · rw [ite_eq_right hjN, boundary_interior (by omega) (by omega), node_succ]
    ring

lemma node_in_sector {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    boundary N j ≤ node N j ∧ node N j ≤ boundary N (j + 1) := by
  have hn : 0 ≤ 1 / (N : ℝ) := by positivity
  rw [left_boundary hj, right_boundary hj]
  constructor
  · split_ifs with h
    · simp [h]
    · linarith
  · split_ifs with h
    · simpa [h] using (node_bounds hN hj).2
    · linarith

lemma sector_width_pos {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    boundary N j < boundary N (j + 1) := by
  have hn : 0 < 1 / (N : ℝ) := by positivity
  rw [left_boundary hj, right_boundary hj]
  split_ifs with h0 hlast hlast
  · omega
  · simp only [h0, node_zero]
    linarith
  · subst j
    rw [node_last hN]
    linarith
  · linarith

lemma sector_distance {N j : ℕ} {q : ℝ} (hN : 0 < N) (hj : j ≤ N)
    (hq : q ∈ Set.Icc (boundary N j) (boundary N (j + 1))) :
    |q - node N j| ≤ 1 / (N : ℝ) := by
  have hn : 0 ≤ 1 / (N : ℝ) := by positivity
  rw [abs_le]
  obtain ⟨hql, hqr⟩ := hq
  rw [left_boundary hj] at hql
  rw [right_boundary hj] at hqr
  constructor
  · split_ifs at hql with h0
    · simp only [h0, node_zero] at *
      linarith
    · linarith
  · split_ifs at hqr with hlast
    · subst j
      rw [node_last hN]
      linarith
    · linarith

lemma boundary_bounds {N j : ℕ} (hN : 0 < N) (hj : j ≤ N + 1) :
    -1 ≤ boundary N j ∧ boundary N j ≤ 1 := by
  by_cases h0 : j = 0
  · simp [h0]
  by_cases hlast : j = N + 1
  · simp [hlast]
  have hjN : j ≤ N := by omega
  have hp := node_bounds hN (show j - 1 ≤ N by omega)
  have hc := node_bounds hN hjN
  rw [boundary, ite_eq_right h0, ite_eq_right hlast]
  constructor <;> linarith [hp.1, hp.2, hc.1, hc.2]

lemma sector_point_bounds {N j : ℕ} {q : ℝ} (hN : 0 < N) (hj : j ≤ N)
    (hq : q ∈ Set.Icc (boundary N j) (boundary N (j + 1))) : |q| ≤ 1 := by
  rw [abs_le]
  exact ⟨(boundary_bounds hN (by omega)).1.trans hq.1,
    hq.2.trans (boundary_bounds hN (by omega)).2⟩

lemma coefficient_compatibility {N j : ℕ} (hj : 0 < j) (hjN : j ≤ N) :
    alpha N j - alpha N (j - 1) =
      boundary N j * (beta N j - beta N (j - 1)) := by
  have h0 : j ≠ 0 := by omega
  have hlast : j ≠ N + 1 := by omega
  rw [boundary, ite_eq_right h0, ite_eq_right hlast]
  exact AngularSampling.sampled_compatibility _ _

@[simp] lemma coefficient_outer_left (N : ℕ) :
    alpha N 0 - boundary N 0 * beta N 0 = 0 := by
  norm_num [alpha, beta]

lemma coefficient_outer_right {N : ℕ} (hN : 0 < N) :
    alpha N N - boundary N (N + 1) * beta N N = 0 := by
  simp [alpha, beta, node_last hN]
  norm_num

lemma beta_error {N j : ℕ} {q : ℝ} (hN : 0 < N) (hj : j ≤ N)
    (hq : q ∈ Set.Icc (boundary N j) (boundary N (j + 1))) :
    |beta N j - q / 2| ≤ (1 / (N : ℝ)) / 2 := by
  have h := sector_distance hN hj hq
  unfold beta
  calc
    |node N j / 2 - q / 2| = |q - node N j| / 2 := by
      rw [← sub_div, abs_div, abs_sub_comm]; norm_num
    _ ≤ (1 / (N : ℝ)) / 2 := div_le_div_of_nonneg_right h (by norm_num)

lemma alpha_error {N j : ℕ} {q : ℝ} (hN : 0 < N) (hj : j ≤ N)
    (hq : q ∈ Set.Icc (boundary N j) (boundary N (j + 1))) :
    |alpha N j - (1 + q ^ 2) / 4| ≤ (1 / (N : ℝ)) / 2 := by
  have hd := sector_distance hN hj hq
  have hnabs : |node N j| ≤ 1 := abs_le.mpr (node_bounds hN hj)
  have hqabs := sector_point_bounds hN hj hq
  have hsum : |node N j + q| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith)
  have hdiff : |node N j - q| ≤ 1 / (N : ℝ) := by rwa [abs_sub_comm]
  have hm := mul_le_mul hdiff hsum (abs_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))
  have hid : alpha N j - (1 + q ^ 2) / 4 =
      (node N j - q) * (node N j + q) / 4 := by unfold alpha; ring
  rw [hid, abs_div, abs_mul]
  norm_num at hm ⊢
  linarith

lemma profile_nonneg (q : ℝ) : 0 ≤ profile q := by
  unfold profile
  positivity

lemma profile_lipschitz {p q : ℝ} (hp : |p| ≤ 1) (hq : |q| ≤ 1) :
    |profile p - profile q| ≤ (3 / 8) * |p - q| := by
  have hp2 := (sq_le_one_iff_abs_le_one p).mpr hp
  have hq2 := (sq_le_one_iff_abs_le_one q).mpr hq
  have hsum : |p + q| ≤ 2 := (abs_add_le _ _).trans (by linarith)
  have hscale : |1 + p ^ 2 + q ^ 2| ≤ 3 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hm : |p + q| * |1 + p ^ 2 + q ^ 2| ≤ 6 := by
    calc
      |p + q| * |1 + p ^ 2 + q ^ 2| ≤ 2 * 3 :=
        mul_le_mul hsum hscale (abs_nonneg _) (by norm_num)
      _ = 6 := by norm_num
  have hm' := mul_le_mul_of_nonneg_left hm (abs_nonneg (p - q))
  have hid : profile p - profile q =
      (p - q) * (p + q) * (1 + p ^ 2 + q ^ 2) / 16 := by unfold profile; ring
  rw [hid, abs_div, abs_mul, abs_mul]
  norm_num
  nlinarith only [hm']

lemma radius_error {N j : ℕ} {q τ η : ℝ} (hN : 0 < N) (hj : j ≤ N)
    (hq : q ∈ Set.Icc (boundary N j) (boundary N (j + 1))) :
    |radius τ η N j - (1 / 2 + τ ^ 2 * (profile q + η))| ≤
      (3 / 8) * τ ^ 2 * (1 / (N : ℝ)) := by
  have hl := profile_lipschitz (abs_le.mpr (node_bounds hN hj)) (sector_point_bounds hN hj hq)
  have hd : |node N j - q| ≤ 1 / (N : ℝ) := by
    rw [abs_sub_comm]; exact sector_distance hN hj hq
  have hl' : |profile (node N j) - profile q| ≤ (3 / 8) * (1 / (N : ℝ)) :=
    hl.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  have hid : radius τ η N j - (1 / 2 + τ ^ 2 * (profile q + η)) =
      τ ^ 2 * (profile (node N j) - profile q) := by unfold radius; ring
  rw [hid, abs_mul, abs_of_nonneg (sq_nonneg τ)]
  nlinarith only [mul_le_mul_of_nonneg_left hl' (sq_nonneg τ)]

lemma radius_pos {τ η : ℝ} {N j : ℕ} (hη : 0 ≤ η) : 0 < radius τ η N j := by
  have h := mul_nonneg (sq_nonneg τ) (add_nonneg (profile_nonneg (node N j)) hη)
  unfold radius
  linarith

lemma first_sector_width {N : ℕ} (hN : 0 < N) :
    boundary N 1 - boundary N 0 = 1 / (N : ℝ) := by
  have hnot : (0 : ℕ) ≠ N := by omega
  rw [show 1 = (0 : ℕ) + 1 by rfl, right_boundary (Nat.zero_le N), ite_eq_right hnot]
  simp

lemma last_sector_width {N : ℕ} (hN : 0 < N) :
    boundary N (N + 1) - boundary N N = 1 / (N : ℝ) := by
  rw [boundary_last, boundary_interior hN le_rfl, node_last hN]
  ring

lemma interior_sector_width {N j : ℕ} (hj : 0 < j) (hjN : j < N) :
    boundary N (j + 1) - boundary N j = 2 / (N : ℝ) := by
  rw [right_boundary hjN.le, ite_eq_right (ne_of_lt hjN), boundary_interior hj hjN.le]
  ring

lemma sector_width_le {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) :
    boundary N (j + 1) - boundary N j ≤ 2 / (N : ℝ) := by
  have hn : 0 ≤ 1 / (N : ℝ) := by positivity
  by_cases h0 : j = 0
  · subst j
    rw [first_sector_width hN]
    exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)
  by_cases hlast : j = N
  · subst j
    rw [last_sector_width hN]
    exact div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg N)
  · rw [interior_sector_width (by omega) (by omega)]

lemma reciprocal_square (k : ℕ) :
    1 / ((k ^ 2 : ℕ) : ℝ) = (1 / (k : ℝ)) ^ 2 := by
  simp [Nat.cast_pow, one_div, inv_pow]

theorem reciprocal_mesh_errors {k j : ℕ} {q : ℝ} (hk : 0 < k) (hj : j ≤ k ^ 2)
    (hq : q ∈ Set.Icc (boundary (k ^ 2) j) (boundary (k ^ 2) (j + 1))) :
    |q - node (k ^ 2) j| ≤ (1 / (k : ℝ)) ^ 2 ∧
    |beta (k ^ 2) j - q / 2| ≤ (1 / (k : ℝ)) ^ 2 / 2 ∧
    |alpha (k ^ 2) j - (1 + q ^ 2) / 4| ≤ (1 / (k : ℝ)) ^ 2 / 2 ∧
    ∀ η : ℝ,
      |radius (1 / (k : ℝ)) η (k ^ 2) j -
        (1 / 2 + (1 / (k : ℝ)) ^ 2 * (profile q + η))| ≤
          (3 / 8) * (1 / (k : ℝ)) ^ 4 := by
  have hN : 0 < k ^ 2 := pow_pos hk 2
  have hd := sector_distance hN hj hq
  have hb := beta_error hN hj hq
  have ha := alpha_error hN hj hq
  rw [reciprocal_square] at hd hb ha
  refine ⟨hd, hb, ha, ?_⟩
  intro η
  have h := radius_error (τ := 1 / (k : ℝ)) (η := η) hN hj hq
  rw [reciprocal_square] at h
  convert h using 1
  ring

lemma intercept_sampling_error {N j : ℕ} {S Y : ℝ}
    (hN : 0 < N) (hj : j ≤ N) (hS : 0 ≤ S)
    (hYl : boundary N j * S ≤ Y) (hYr : Y ≤ boundary N (j + 1) * S) :
    |Y - node N j * S| ≤ S * (1 / (N : ℝ)) := by
  have hn : 0 ≤ 1 / (N : ℝ) := by positivity
  have hl : node N j - 1 / (N : ℝ) ≤ boundary N j := by
    rw [left_boundary hj]
    split_ifs with h0
    · simp only [h0, node_zero]
      linarith
    · exact le_rfl
  have hr : boundary N (j + 1) ≤ node N j + 1 / (N : ℝ) := by
    rw [right_boundary hj]
    split_ifs with hlast
    · subst j
      rw [node_last hN]
      linarith
    · exact le_rfl
  have hleft := mul_le_mul_of_nonneg_right hl hS
  have hright := mul_le_mul_of_nonneg_right hr hS
  rw [abs_le]
  constructor <;> nlinarith only [hYl, hYr, hleft, hright]

end AngularEndpoint

end

end OAI
