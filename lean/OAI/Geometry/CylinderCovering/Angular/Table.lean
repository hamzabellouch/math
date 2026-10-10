import OAI.Geometry.CylinderCovering.Angular.TableDefinitions

namespace OAI

noncomputable section
namespace AngularTable

lemma reciprocal_square (x : ℝ) : (x⁻¹) ^ 2 = 1 / x ^ 2 := by
  simp only [one_div, inv_pow]

lemma midpointFour_cost {n : ℕ} (hn : 0 < n) :
    quadraticCost (midpointFour n) = 1 / 2 - 1 / (80 * (n : ℝ) ^ 2) := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  unfold quadraticCost midpointFour
  dsimp only
  field_simp; ring

lemma midpointOne_cost (α : ℝ) :
    quadraticCost (midpointOne α) = 1 / 2 - (13 / 6000 : ℝ) * α ^ 2 := by
  unfold quadraticCost midpointOne
  norm_num
  ring

lemma midpointTwo_cost {n : ℕ} (hn : 0 < n) :
    quadraticCost (midpointTwo n) = 1 / 2 - 13 / (6000 * (n : ℝ) ^ 2) := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  unfold quadraticCost midpointTwo
  dsimp only
  field_simp; ring

lemma continuousTwo_cost (c : ℝ) (m : ℕ) :
    quadraticCost (continuousTwo c m) = 1 / 2 - (13 / 6000 : ℝ) * c ^ 2 := by
  unfold quadraticCost continuousTwo
  norm_num
  ring

lemma squaredTwo_cost {n : ℕ} (hn : 0 < n) :
    quadraticCost (squaredTwo n) = 1 / 2 - 1 / (120 * (n : ℝ) ^ 2) := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  unfold quadraticCost squaredTwo
  dsimp only
  field_simp; ring

lemma maximumOne_cost {n : ℕ} (hn : 0 < n) :
    quadraticCost (maximumOne n) = 1 / 2 - 1 / (7680 * (n : ℝ) ^ 2) := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  unfold quadraticCost maximumOne
  dsimp only
  field_simp; ring

lemma cartesianThreeQuarters_cost (t : ℝ) :
    quadraticCost (cartesianThreeQuarters t) = 1 / 2 - t ^ 2 / 1920 := by
  unfold quadraticCost cartesianThreeQuarters
  norm_num
  ring

lemma cartesianOne_cost {n : ℕ} (hn : 0 < n) :
    quadraticCost (cartesianOne n) = 1 / 2 - 13 / (24000 * (n : ℝ) ^ 2) := by
  have hne : (n : ℝ) ≠ 0 := by positivity
  unfold quadraticCost cartesianOne
  dsimp only
  field_simp; ring

lemma mesh_le_of_inverse_size {τ k : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hk : 0 < k) (hm : k / τ ^ 2 ≤ m) :
    0 < m ∧ 2 / (m : ℝ) ≤ (2 / k) * τ ^ 2 := by
  have ht2 : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hmpos : (0 : ℝ) < m := (div_pos hk ht2).trans_le hm
  have hmn : 0 < m := by exact_mod_cast hmpos
  refine ⟨hmn, ?_⟩
  have hkm : k ≤ (m : ℝ) * τ ^ 2 := (div_le_iff₀ ht2).mp hm
  apply (div_le_iff₀ hmpos).mpr
  calc
    2 = (2 / k) * k := by field_simp
    _ ≤ (2 / k) * ((m : ℝ) * τ ^ 2) := mul_le_mul_of_nonneg_left hkm (by positivity)
    _ = (2 / k) * τ ^ 2 * (m : ℝ) := by ring

lemma ceil_inverse_mesh {τ k : ℝ} (hτ : 0 < τ) (hk : 0 < k) :
    0 < ⌈k / τ ^ 2⌉₊ ∧ 2 / (⌈k / τ ^ 2⌉₊ : ℝ) ≤ (2 / k) * τ ^ 2 :=
  mesh_le_of_inverse_size hτ hk (Nat.le_ceil _)

lemma midpointFour_mesh {n : ℕ} (hn : 0 < n) :
    0 < (midpointFour n).sectors ∧
      mesh (midpointFour n) = (1 / 4 : ℝ) * (midpointFour n).tilt ^ 2 := by
  constructor
  · simp only [midpointFour]
    positivity
  · have hne : (n : ℝ) ≠ 0 := by positivity
    unfold mesh midpointFour
    push_cast
    field_simp; ring

lemma midpointOne_mesh {α : ℝ} (hα : 0 < α) :
    0 < (midpointOne α).sectors ∧ mesh (midpointOne α) ≤ 2 * (midpointOne α).tilt ^ 2 := by
  simpa only [midpointOne, mesh, reciprocal_square, div_one] using
    ceil_inverse_mesh hα (by norm_num : (0 : ℝ) < 1)

lemma midpointTwo_mesh {n : ℕ} (hn : 0 < n) :
    0 < (midpointTwo n).sectors ∧ mesh (midpointTwo n) = 2 * (midpointTwo n).tilt ^ 2 := by
  constructor
  · simp only [midpointTwo]
    positivity
  · have hne : (n : ℝ) ≠ 0 := by positivity
    unfold mesh midpointTwo
    push_cast
    field_simp

lemma continuousTwo_mesh {c : ℝ} {m : ℕ} (hc : 0 < c) (hm : 2 / c ^ 2 ≤ m) :
    0 < (continuousTwo c m).sectors ∧ mesh (continuousTwo c m) ≤ (continuousTwo c m).tilt ^ 2 := by
  simpa only [continuousTwo, mesh, div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul] using
    mesh_le_of_inverse_size hc (by norm_num : (0 : ℝ) < 2) hm

lemma squaredTwo_mesh {n : ℕ} (hn : 0 < n) :
    0 < (squaredTwo n).sectors ∧ mesh (squaredTwo n) = (1 / 2 : ℝ) * (squaredTwo n).tilt ^ 2 := by
  constructor
  · simp only [squaredTwo]
    positivity
  · have hne : (n : ℝ) ≠ 0 := by positivity
    unfold mesh squaredTwo
    push_cast
    field_simp

lemma maximumOne_mesh {n : ℕ} (hn : 0 < n) :
    0 < (maximumOne n).sectors ∧ mesh (maximumOne n) = 32 * (maximumOne n).tilt ^ 2 := by
  constructor
  · simp only [maximumOne]
    positivity
  · have hne : (n : ℝ) ≠ 0 := by positivity
    unfold mesh maximumOne
    push_cast
    field_simp; ring

lemma cartesianThreeQuarters_mesh {t : ℝ} (ht : 0 < t) :
    0 < (cartesianThreeQuarters t).sectors ∧
      mesh (cartesianThreeQuarters t) ≤ 8 * (cartesianThreeQuarters t).tilt ^ 2 := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hm : 1 / t ^ 2 ≤ (⌈Real.sqrt 2 / t ^ 2⌉₊ : ℝ) :=
    (div_le_div_of_nonneg_right hsqrt (sq_nonneg t)).trans (Nat.le_ceil _)
  have hh := mesh_le_of_inverse_size ht (by norm_num : (0 : ℝ) < 1) hm
  refine ⟨hh.1, ?_⟩
  change 2 / (⌈Real.sqrt 2 / t ^ 2⌉₊ : ℝ) ≤ 8 * (t / 2) ^ 2
  nlinarith only [hh.2]

lemma cartesianOne_mesh {n : ℕ} (hn : 0 < n) :
    0 < (cartesianOne n).sectors ∧ mesh (cartesianOne n) = 8 * (cartesianOne n).tilt ^ 2 := by
  constructor
  · simp only [cartesianOne]
    positivity
  · have hne : (n : ℝ) ≠ 0 := by positivity
    unfold mesh cartesianOne
    push_cast
    field_simp; ring

lemma squaredTwo_family_cost {n : ℕ} (hn : 0 < n) (H : ℝ) :
    H * quadraticCost (squaredTwo n) / 2 =
      H * (1 / 4 + (1 / 240 - 1 / 120 : ℝ) / (n : ℝ) ^ 2) := by
  rw [squaredTwo_cost hn]
  have hne : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma cartesianThreeQuarters_family_cost (t c₀ : ℝ) :
    c₀ * quadraticCost (cartesianThreeQuarters t) / 2 =
      c₀ / 4 - c₀ * t ^ 2 / 3840 := by
  rw [cartesianThreeQuarters_cost]
  ring

lemma remainder_rescale {C Q K a t : ℝ}
    (h : |C - Q| ≤ K * (a * t) ^ 4) : |C - Q| ≤ (K * a ^ 4) * t ^ 4 := by
  simpa only [mul_pow, mul_assoc] using h

lemma margins_admissible (n m : ℕ) (a c t : ℝ) :
    (0 < (midpointFour n).margin ∧ (midpointFour n).margin < 1 / 480) ∧
    (0 < (midpointOne a).margin ∧ (midpointOne a).margin < 1 / 480) ∧
    (0 < (midpointTwo n).margin ∧ (midpointTwo n).margin < 1 / 480) ∧
    (0 < (continuousTwo c m).margin ∧ (continuousTwo c m).margin < 1 / 480) ∧
    (0 < (squaredTwo n).margin ∧ (squaredTwo n).margin < 1 / 480) ∧
    (0 < (maximumOne n).margin ∧ (maximumOne n).margin < 1 / 480) ∧
    (0 < (cartesianThreeQuarters t).margin ∧ (cartesianThreeQuarters t).margin < 1 / 480) ∧
    (0 < (cartesianOne n).margin ∧ (cartesianOne n).margin < 1 / 480) := by
  norm_num [midpointFour, midpointOne, midpointTwo, continuousTwo, squaredTwo,
    maximumOne, cartesianThreeQuarters, cartesianOne]

end AngularTable

end

end OAI
