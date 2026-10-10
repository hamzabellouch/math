import OAI.Analysis.PlanarPacking.Cardinal

namespace OAI

namespace SharpPlanar

noncomputable def sinTable : ℕ → ℝ
  | 0 => 0 | 1 => 1/2 | 2 => b | 3 => 1 | 4 => b | 5 => 1/2
  | 6 => 0 | 7 => -1/2 | 8 => -b | 9 => -1 | 10 => -b | 11 => -1/2
  | _ => 0
noncomputable def cosTable : ℕ → ℝ
  | 0 => 1 | 1 => b | 2 => 1/2 | 3 => 0 | 4 => -1/2 | 5 => -b
  | 6 => -1 | 7 => -b | 8 => -1/2 | 9 => 0 | 10 => 1/2 | 11 => b
  | _ => 1

lemma trig_table (n : ℕ) (hn : n ≤ 12) :
    Real.sin (Real.pi * n / 6) = sinTable n ∧
    Real.cos (Real.pi * n / 6) = cosTable n := by
  induction n with
  | zero => norm_num [sinTable, cosTable]
  | succ n ih =>
    have hn' : n ≤ 12 := by omega
    obtain ⟨hs, hc⟩ := ih hn'
    rw [show Real.pi * (n+1 : ℕ) / 6 = Real.pi * n / 6 + Real.pi / 6 by push_cast; ring]
    rw [Real.sin_add, Real.cos_add, hs, hc, Real.sin_pi_div_six, Real.cos_pi_div_six]
    change sinTable n * b + cosTable n * (1/2) = sinTable (n+1) ∧
      cosTable n * b - sinTable n * (1/2) = cosTable (n+1)
    have hn11 : n ≤ 11 := by omega
    interval_cases n <;> norm_num [sinTable, cosTable] <;> constructor <;> nlinarith [b_sq]

lemma squared_sine_to_cos (x : ℝ) : (2 * Real.sin x)^2 = 2 - 2*Real.cos (2*x) := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

lemma divided_cos_to_double (x : ℝ) :
    Real.cos x / Real.sin x = Real.sin (2*x) / (1 - Real.cos (2*x)) := by
  by_cases hs : Real.sin x = 0
  · simp [Real.sin_two_mul, hs]
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have he : 1 - (2 * Real.cos x ^ 2 - 1) = 2 * Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [he]
  field_simp

lemma Q_as_table (n : ℕ) : Q n =
    (Real.pi/6)^2 * ∏ a ∈ residues.erase (n % 12),
      (2 - 2*(cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a)) := by
  unfold Q
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [squared_sine_to_cos,
    show 2 * (Real.pi * (((n%12 : ℕ):ℝ)-a)/12) =
      Real.pi*(n%12 : ℕ)/6 - Real.pi*a/6 by ring, Real.cos_sub]
  rw [(trig_table (n%12) (by omega)).1, (trig_table (n%12) (by omega)).2,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).1,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).2]


lemma D_as_table (n : ℕ) : D n = (Real.pi/6) *
    ∑ a ∈ residues.erase (n%12),
      (sinTable (n%12)*cosTable a - cosTable (n%12)*sinTable a) /
        (1 - (cosTable (n%12)*cosTable a + sinTable (n%12)*sinTable a)) := by
  unfold D
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [divided_cos_to_double,
    show 2 * (Real.pi * (((n%12 : ℕ):ℝ)-a)/12) =
      Real.pi*(n%12 : ℕ)/6 - Real.pi*a/6 by ring, Real.sin_sub, Real.cos_sub]
  rw [(trig_table (n%12) (by omega)).1, (trig_table (n%12) (by omega)).2,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).1,
    (trig_table a (by have := residue_lt (Finset.mem_erase.mp ha).2; omega)).2]

lemma b_lt_one : b < 1 := by nlinarith [b_sq, b_pos]
lemma b_pow_even (n : ℕ) : b^(2*n) = (3/4 : ℝ)^n := by rw [pow_mul, b_sq]
lemma b_pow_odd (n : ℕ) : b^(2*n+1) = (3/4 : ℝ)^n * b := by rw [pow_add, b_pow_even]; simp
lemma b_pow_3 : b^3 = (3/4 : ℝ)^1 * b := b_pow_odd 1
lemma b_pow_4 : b^4 = (3/4 : ℝ)^2 := b_pow_even 2
lemma b_pow_5 : b^5 = (3/4 : ℝ)^2 * b := b_pow_odd 2
lemma b_pow_6 : b^6 = (3/4 : ℝ)^3 := b_pow_even 3
lemma b_pow_7 : b^7 = (3/4 : ℝ)^3 * b := b_pow_odd 3
lemma b_pow_8 : b^8 = (3/4 : ℝ)^4 := b_pow_even 4
lemma b_pow_9 : b^9 = (3/4 : ℝ)^4 * b := b_pow_odd 4
lemma b_pow_10 : b^10 = (3/4 : ℝ)^5 := b_pow_even 5

lemma Q_0 : Q 0 = Real.pi^2/3 := by
  rw [Q_as_table, show 0 % 12 = 0 from rfl,
    show residues.erase 0 = {1, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  ring

lemma Q_1 : Q 1 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table, show 1 % 12 = 1 from rfl,
    show residues.erase 1 = {0, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq, b_pow_3]
  ring

lemma Q_3 : Q 3 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table, show 3 % 12 = 3 from rfl,
    show residues.erase 3 = {0, 1, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

lemma Q_4 : Q 4 = Real.pi^2/3 := by
  rw [Q_as_table, show 4 % 12 = 4 from rfl,
    show residues.erase 4 = {0, 1, 3, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  ring

lemma Q_7 : Q 7 = (2*Real.pi^2/3)*(2+2*b) := by
  rw [Q_as_table, show 7 % 12 = 7 from rfl,
    show residues.erase 7 = {0, 1, 3, 4, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq, b_pow_3]
  ring

lemma Q_9 : Q 9 = (2*Real.pi^2/3)*(2+2*b) := by
  rw [Q_as_table, show 9 % 12 = 9 from rfl,
    show residues.erase 9 = {0, 1, 3, 4, 7} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

lemma one_sub_b_ne : 1 - b ≠ 0 := by linarith [b_lt_one]
lemma one_add_b_ne : 1 + b ≠ 0 := by linarith [b_pos]

lemma D_0 : D 0 = -7 * Real.pi * b / 9 := by
  rw [D_as_table, show 0 % 12 = 0 from rfl,
    show residues.erase 0 = {1, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_pow_3]
  ring

lemma D_1 : D 1 = Real.pi * (3+2*b) / 18 := by
  rw [D_as_table, show 1 % 12 = 1 from rfl,
    show residues.erase 1 = {0, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

lemma D_3 : D 3 = -Real.pi * (3+2*b) / 18 := by
  rw [D_as_table, show 3 % 12 = 3 from rfl,
    show residues.erase 3 = {0, 1, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

lemma D_4 : D 4 = 7 * Real.pi * b / 9 := by
  rw [D_as_table, show 4 % 12 = 4 from rfl,
    show residues.erase 4 = {0, 1, 3, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_pow_3]
  ring

lemma D_7 : D 7 = -Real.pi * (3-2*b) / 18 := by
  rw [D_as_table, show 7 % 12 = 7 from rfl,
    show residues.erase 7 = {0, 1, 3, 4, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

lemma D_9 : D 9 = Real.pi * (3-2*b) / 18 := by
  rw [D_as_table, show 9 % 12 = 9 from rfl,
    show residues.erase 9 = {0, 1, 3, 4, 7} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq]
  ring

lemma b_lt_thirteen_fifteenths : b < 13/15 := by nlinarith [b_sq, b_pos]
lemma pi_lower : (157/50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
lemma pi_upper : Real.pi < 22/7 := by linarith [Real.pi_lt_d4]

lemma Q_small_lower : (7/4 : ℝ) < (2*Real.pi^2/3)*(2-2*b) := by
  have hpi2 : (157/50 : ℝ)^2 < Real.pi^2 := by nlinarith [pi_lower, Real.pi_pos]
  have hf : (4/15 : ℝ) < 2-2*b := by linarith [b_lt_thirteen_fifteenths]
  have hx : (2*(157/50 : ℝ)^2/3)*(4/15) < (2*Real.pi^2/3)*(2-2*b) := by
    gcongr
  norm_num at hx
  linarith


theorem Q_lower (n : ℕ) (hn : n%12 ∈ residues) : (7/4 : ℝ) < Q n := by
  rw [← Q_mod]
  have hb := b_pos
  have hp := Real.pi_pos
  have hp2 : (157/50 : ℝ)^2 < Real.pi^2 := by nlinarith [pi_lower]
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    rw [hn] <;> first | rw [Q_0] | rw [Q_1] | rw [Q_3] | rw [Q_4] | rw [Q_7] | rw [Q_9]
  · nlinarith
  · exact Q_small_lower
  · exact Q_small_lower
  · nlinarith
  · nlinarith [mul_pos (sq_pos_of_pos hp) hb]
  · nlinarith [mul_pos (sq_pos_of_pos hp) hb]


theorem D_abs_bound (n : ℕ) (hn : n%12 ∈ residues) : |D n| < 53/25 := by
  have hpbpos : 0 < Real.pi*b := mul_pos Real.pi_pos b_pos
  have hpb : Real.pi*b < (22/7 : ℝ)*(13/15) := by
    gcongr
    · exact le_of_lt b_pos
    · exact pi_upper
    · exact b_lt_thirteen_fifteenths
  have hp := Real.pi_pos
  have hpu := pi_upper
  rw [← D_mod]
  simp only [residues, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with hn | hn | hn | hn | hn | hn <;>
    rw [hn] <;> first | rw [D_0] | rw [D_1] | rw [D_3] | rw [D_4] | rw [D_7] | rw [D_9]
  all_goals apply abs_lt.mpr; constructor <;> nlinarith

end SharpPlanar

end OAI
