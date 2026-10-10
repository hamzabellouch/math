import OAI.MathematicalPhysics.NavierStokes.Material.Model

namespace OAI

namespace Alternating.Memory
open scoped BigOperators

noncomputable def fraction (b : ℕ) : List ℕ → ℝ
  | [] => 0
  | d :: ds => ((d : ℝ) + fraction b ds) / b

def AllowedDigits (b : ℕ) (ds : List ℕ) : Prop :=
  ∀ d ∈ ds, Even d ∧ d + 2 ≤ b

noncomputable def tailBound (b : ℕ) : ℝ := ((b : ℝ) - 2) / ((b : ℝ) - 1)

@[simp] theorem fraction_nil (b : ℕ) : fraction b [] = 0 := rfl

@[simp] theorem fraction_cons (b d : ℕ) (ds : List ℕ) :
    fraction b (d :: ds) = ((d : ℝ) + fraction b ds) / b := rfl

theorem fraction_nonneg (b : ℕ) (ds : List ℕ) : 0 ≤ fraction b ds := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp only [fraction_cons]; positivity

theorem tailBound_nonneg {b : ℕ} (hb : 2 ≤ b) : 0 ≤ tailBound b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailBound
  exact div_nonneg (by linarith) (by linarith)

theorem tailBound_lt_one {b : ℕ} (hb : 2 ≤ b) : tailBound b < 1 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailBound
  exact (div_lt_one (by linarith)).2 (by linarith)

theorem fraction_le_tailBound {b : ℕ} (hb : 2 ≤ b) {ds : List ℕ}
    (hds : AllowedDigits b ds) : fraction b ds ≤ tailBound b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hpos : (0 : ℝ) < b := by linarith
  have hkey : ((b : ℝ) - 1) * tailBound b = (b : ℝ) - 2 := by
    unfold tailBound
    field_simp [(by linarith : (b : ℝ) - 1 ≠ 0)]
  induction ds with
  | nil => simpa using tailBound_nonneg hb
  | cons d ds ih =>
    have hd : (d : ℝ) + 2 ≤ b := by
      exact_mod_cast (hds d (by simp)).2
    have hrest : AllowedDigits b ds := fun a ha => hds a (by simp [ha])
    rw [fraction_cons]
    apply (div_le_iff₀ hpos).2
    have := ih hrest
    nlinarith

theorem fraction_lt_one {b : ℕ} (hb : 2 ≤ b) {ds : List ℕ}
    (hds : AllowedDigits b ds) : fraction b ds < 1 :=
  (fraction_le_tailBound hb hds).trans_lt (tailBound_lt_one hb)

theorem fraction_mem_digit_interval {b d : ℕ} (hb : 2 ≤ b) {ds : List ℕ}
    (hds : AllowedDigits b ds) :
    fraction b (d :: ds) ∈ Set.Ico ((d : ℝ) / b) (((d : ℝ) + 1) / b) := by
  have hpos : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  rw [fraction_cons]
  exact ⟨div_le_div_of_nonneg_right (le_add_of_nonneg_right (fraction_nonneg b ds)) hpos.le,
    (div_lt_div_iff_of_pos_right hpos).2 (by have := fraction_lt_one hb hds; linarith)⟩

theorem fraction_append {b : ℕ} (_hb : 0 < b) (ds es : List ℕ) :
    fraction b (ds ++ es) = fraction b ds + (b : ℝ)⁻¹ ^ ds.length * fraction b es := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.cons_append, fraction_cons, List.length_cons, pow_succ, ih]
    ring

@[simp] theorem fraction_replicate_zero (b n : ℕ) :
    fraction b (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

def pad (K : ℕ) (ds : List ℕ) : List ℕ :=
  ds ++ List.replicate (K - ds.length) 0

theorem pad_length {ds : List ℕ} {K : ℕ} (h : ds.length ≤ K) :
    (pad K ds).length = K := by simp [pad, Nat.add_sub_of_le h]

theorem fraction_pad {b : ℕ} (hb : 0 < b) (K : ℕ) (ds : List ℕ) :
    fraction b (pad K ds) = fraction b ds := by simp [pad, fraction_append hb]

theorem allowedDigits_pad {b : ℕ} (hb : 2 ≤ b) {ds : List ℕ}
    (hds : AllowedDigits b ds) (K : ℕ) : AllowedDigits b (pad K ds) := by
  intro d hd
  simp only [pad, List.mem_append, List.mem_replicate] at hd
  rcases hd with hd | ⟨_, rfl⟩
  · exact hds d hd
  · exact ⟨by simp, by simpa using hb⟩

theorem fraction_denominator {b : ℕ} (hb : 0 < b) (ds : List ℕ) :
    ∃ k : ℤ, (b : ℝ) ^ ds.length * fraction b ds = k := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  induction ds with
  | nil => exact ⟨0, by simp⟩
  | cons d ds ih =>
    rcases ih with ⟨k, hk⟩
    refine ⟨(b : ℤ) ^ ds.length * (d : ℤ) + k, ?_⟩
    simp only [List.length_cons, fraction_cons, pow_succ, Int.cast_add, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast]
    rw [← hk]
    field_simp

theorem fraction_padded_denominator {b K : ℕ} (hb : 0 < b) (ds : List ℕ)
    (hK : ds.length ≤ K) : ∃ k : ℤ, (b : ℝ) ^ K * fraction b ds = k := by
  simpa [pad_length hK, fraction_pad hb] using fraction_denominator hb (pad K ds)

structure Block (b K : ℕ) where
  stateDigit : ℕ
  left : List ℕ
  right : List ℕ
  state_allowed : Even stateDigit ∧ stateDigit + 2 ≤ b
  left_allowed : AllowedDigits b left
  right_allowed : AllowedDigits b right
  left_length : left.length ≤ K
  right_length : right.length ≤ K

def Block.digits {b K : ℕ} (c : Block b K) : List ℕ :=
  c.stateDigit :: (pad K c.left ++ pad K c.right)

noncomputable def Block.code {b K : ℕ} (c : Block b K) : ℝ := fraction b c.digits
noncomputable def Block.leftCode {b K : ℕ} (c : Block b K) : ℝ := fraction b c.left
noncomputable def Block.rightCode {b K : ℕ} (c : Block b K) : ℝ := fraction b c.right

theorem Block.digits_length {b K : ℕ} (c : Block b K) : c.digits.length = 1 + 2 * K := by
  simp [Block.digits, pad_length c.left_length, pad_length c.right_length]
  omega

theorem Block.digits_allowed {b K : ℕ} (hb : 2 ≤ b) (c : Block b K) :
    AllowedDigits b c.digits := by
  intro d hd
  simp only [Block.digits, List.mem_cons, List.mem_append] at hd
  rcases hd with rfl | h | h
  · exact c.state_allowed
  · exact allowedDigits_pad hb c.left_allowed K d h
  · exact allowedDigits_pad hb c.right_allowed K d h

theorem Block.code_formula {b K : ℕ} (hb : 0 < b) (c : Block b K) :
    c.code = ((c.stateDigit : ℝ) + c.leftCode + (b : ℝ)⁻¹ ^ K * c.rightCode) / b := by
  simp [Block.code, Block.digits, fraction_append hb, pad_length c.left_length,
    fraction_pad hb, Block.leftCode, Block.rightCode, add_assoc]

theorem Block.code_nonneg {b K : ℕ} (c : Block b K) : 0 ≤ c.code :=
  fraction_nonneg _ _

theorem Block.code_le {b K : ℕ} (hb : 2 ≤ b) (c : Block b K) : c.code ≤ tailBound b :=
  fraction_le_tailBound hb (c.digits_allowed hb)

theorem Block.code_denominator {b K : ℕ} (hb : 0 < b) (c : Block b K) :
    ∃ k : ℤ, (b : ℝ) ^ (1 + 2 * K) * c.code = k := by
  simpa [c.digits_length, Block.code] using fraction_denominator hb c.digits

theorem Block.left_denominator {b K : ℕ} (hb : 0 < b) (c : Block b K) :
    ∃ k : ℤ, (b : ℝ) ^ K * c.leftCode = k :=
  fraction_padded_denominator hb c.left c.left_length

theorem Block.right_denominator {b K : ℕ} (hb : 0 < b) (c : Block b K) :
    ∃ k : ℤ, (b : ℝ) ^ K * c.rightCode = k :=
  fraction_padded_denominator hb c.right c.right_length

theorem Block.tail_mem {b K : ℕ} (hb : 2 ≤ b) (c : Block b K) :
    c.leftCode + (b : ℝ)⁻¹ ^ K * c.rightCode ∈ Set.Icc 0 (tailBound b) := by
  have hbpos : 0 < b := by omega
  have hcode : fraction b (pad K c.left ++ pad K c.right) =
      c.leftCode + (b : ℝ)⁻¹ ^ K * c.rightCode := by
    simp [fraction_append hbpos, fraction_pad hbpos, pad_length c.left_length,
      Block.leftCode, Block.rightCode]
  rw [← hcode]
  refine ⟨fraction_nonneg _ _, fraction_le_tailBound hb ?_⟩
  intro d hd
  rcases List.mem_append.1 hd with h | h
  · exact allowedDigits_pad hb c.left_allowed K d h
  · exact allowedDigits_pad hb c.right_allowed K d h

theorem Block.right_mem {b K : ℕ} (hb : 2 ≤ b) (c : Block b K) :
    c.rightCode ∈ Set.Icc 0 (tailBound b) :=
  ⟨fraction_nonneg _ _, fraction_le_tailBound hb c.right_allowed⟩

end Alternating.Memory

end OAI
