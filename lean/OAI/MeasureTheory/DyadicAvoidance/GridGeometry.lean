import Mathlib

namespace OAI

noncomputable section
namespace Problem310

/-- The integer label of the half-open periodic grid cell containing a point. -/
def periodicGridKey (q x : ℝ) : ℤ := ⌊q * Int.fract x⌋

/-- Two points separated from each other in both directions around the circle
cannot occupy the same cell of a periodic grid. -/
theorem periodicGridKey_ne_of_separated {q x y : ℝ} (hq : 2 ≤ q)
    (hlo : q⁻¹ ≤ y - x) (hhi : y - x ≤ 1 - q⁻¹) :
    periodicGridKey q x ≠ periodicGridKey q y := by
  have hqpos : 0 < q := by linarith
  have hi : 0 < q⁻¹ := inv_pos.mpr hqpos
  have hxy : x ≤ y := by linarith
  have hfloorle : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy
  have hfloorupper : ⌊y⌋ < ⌊x⌋ + 2 := by
    apply Int.floor_lt.mpr
    have hx := Int.lt_floor_add_one x
    push_cast
    linarith
  intro heq
  unfold periodicGridKey at heq
  have hxlo := Int.floor_le (q * Int.fract x)
  have hxhi := Int.lt_floor_add_one (q * Int.fract x)
  have hylo := Int.floor_le (q * Int.fract y)
  have hyhi := Int.lt_floor_add_one (q * Int.fract y)
  rw [← heq] at hylo hyhi
  have hdlo : q * (Int.fract y - Int.fract x) < 1 := by linarith
  have hdhi : q * (Int.fract x - Int.fract y) < 1 := by linarith
  have hmul : q * q⁻¹ = 1 := mul_inv_cancel₀ hqpos.ne'
  have hcase : ⌊y⌋ = ⌊x⌋ ∨ ⌊y⌋ = ⌊x⌋ + 1 := by omega
  rcases hcase with h | h
  · unfold Int.fract at hdlo
    rw [h] at hdlo
    have := mul_le_mul_of_nonneg_left hlo hqpos.le
    nlinarith
  · unfold Int.fract at hdhi
    rw [h] at hdhi
    push_cast at hdhi
    have := mul_le_mul_of_nonneg_left hhi hqpos.le
    nlinarith

/-- The periodic label is the residue of the label on the real-line grid. -/
theorem periodicGridKey_eq_emod (q : ℕ) (hq : 0 < q) (x : ℝ) :
    periodicGridKey q x = ⌊(q : ℝ) * x⌋ % (q : ℤ) := by
  unfold periodicGridKey Int.fract
  rw [mul_sub]
  have hc : (q : ℝ) * (⌊x⌋ : ℝ) = (((q : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
    push_cast
    rfl
  rw [hc, Int.floor_sub_intCast, Int.emod_def]
  have hf := Int.natCast_mul_floor_div_cancel (R := ℝ) (Nat.ne_of_gt hq) x
  rw [hf]

/-- Absence of a real-line grid boundary between ordered points preserves keys.
The interval is open at its left end, so a center on a boundary is allowed. -/
theorem periodicGridKey_eq_of_no_crossing (q : ℕ) (hq : 0 < q) {x y : ℝ}
    (hxy : x ≤ y) (hcross : ∀ k : ℤ, (k : ℝ) / q ∉ Set.Ioc x y) :
    periodicGridKey q x = periodicGridKey q y := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hmono : ⌊(q : ℝ) * x⌋ ≤ ⌊(q : ℝ) * y⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_left hxy hqpos.le)
  have hfloors : ⌊(q : ℝ) * x⌋ = ⌊(q : ℝ) * y⌋ := by
    by_contra hne
    have hlt : ⌊(q : ℝ) * x⌋ + 1 ≤ ⌊(q : ℝ) * y⌋ := by omega
    apply hcross (⌊(q : ℝ) * x⌋ + 1)
    constructor
    · apply (lt_div_iff₀ hqpos).mpr
      have h := Int.lt_floor_add_one ((q : ℝ) * x)
      push_cast
      nlinarith
    · apply (div_le_iff₀ hqpos).mpr
      have hcast : ((⌊(q : ℝ) * x⌋ + 1 : ℤ) : ℝ) ≤
          (⌊(q : ℝ) * y⌋ : ℝ) := by exact_mod_cast hlt
      have h := Int.floor_le ((q : ℝ) * y)
      nlinarith
  rw [periodicGridKey_eq_emod q hq, periodicGridKey_eq_emod q hq, hfloors]

/-- Periodic cells used for a dyadic window with last index `b`. -/
def dyadicGridKey (b : ℕ) (x : ℝ) : ℤ := periodicGridKey ((2 : ℝ) ^ (b + 2)) x

@[simp] theorem dyadicGridKey_add_one (b : ℕ) (x : ℝ) :
    dyadicGridKey b (x + 1) = dyadicGridKey b x := by
  simp [dyadicGridKey, periodicGridKey, Int.fract_add_one]

theorem dyadicGridKey_nonneg (b : ℕ) (x : ℝ) : 0 ≤ dyadicGridKey b x := by
  unfold dyadicGridKey periodicGridKey
  exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) (Int.fract_nonneg x))

theorem dyadicGridKey_lt (b : ℕ) (x : ℝ) : dyadicGridKey b x < (2 : ℤ) ^ (b + 2) := by
  unfold dyadicGridKey periodicGridKey
  apply Int.floor_lt.mpr
  push_cast
  nlinarith [Int.fract_lt_one x, pow_pos (by norm_num : (0 : ℝ) < 2) (b + 2)]

/-- Fine dyadic grid labels determine all coarser labels by integer division. -/
theorem dyadicGridKey_nested {b B : ℕ} (hb : b ≤ B) (x : ℝ) :
    dyadicGridKey B x / (2 : ℤ) ^ (B - b) = dyadicGridKey b x := by
  have hp : (2 : ℝ) ^ (B + 2) = ((2 : ℕ) ^ (B - b) : ℝ) * (2 : ℝ) ^ (b + 2) := by
    push_cast
    rw [← pow_add]
    congr 1
    omega
  unfold dyadicGridKey periodicGridKey
  rw [hp, mul_assoc]
  have h := Int.natCast_mul_floor_div_cancel (R := ℝ)
    (n := (2 : ℕ) ^ (B - b)) (by positivity) ((2 : ℝ) ^ (b + 2) * Int.fract x)
  simpa using h

theorem dyadicGridKey_ne_of_coarse_ne {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (h : dyadicGridKey b x ≠ dyadicGridKey b y) :
    dyadicGridKey B x ≠ dyadicGridKey B y := by
  intro hxy
  apply h
  rw [← dyadicGridKey_nested hb x, ← dyadicGridKey_nested hb y, hxy]

private theorem half_pow_antitone : Antitone (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) :=
  pow_right_anti₀ (by norm_num) (by norm_num)

private theorem grid_resolution_bound (b : ℕ) :
    2 ≤ (2 : ℝ) ^ (b + 2) := by
  have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ b + 2 by omega)
  simpa using this

private theorem grid_width_eq (b : ℕ) :
    ((2 : ℝ) ^ (b + 2))⁻¹ = ((2 : ℝ)⁻¹) ^ (b + 2) := by
  simp only [inv_pow]

/-- The center and any requested point in a window occupy different cells. -/
theorem dyadicGridKey_center_ne {a b n : ℕ} {x t : ℝ}
    (ha : 3 ≤ a) (han : a ≤ n) (hnb : n ≤ b)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    dyadicGridKey b x ≠ dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ n) := by
  apply periodicGridKey_ne_of_separated (grid_resolution_bound b)
  · rw [grid_width_eq]
    have hn := half_pow_antitone (show n ≤ b + 2 by omega)
    have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
    nlinarith [ht.1]
  · rw [grid_width_eq]
    have hn := half_pow_antitone (show 3 ≤ n by omega)
    have hb := half_pow_antitone (show 2 ≤ b + 2 by omega)
    norm_num at hn hb
    have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
    nlinarith [ht.2]

/-- Different indices in a window supply different selector addresses. -/
theorem dyadicGridKey_pair_ne {a b n m : ℕ} {x t : ℝ}
    (ha : 3 ≤ a) (han : a ≤ n) (hnm : n < m) (hmb : m ≤ b)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ m) ≠
      dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ n) := by
  apply periodicGridKey_ne_of_separated (grid_resolution_bound b)
  · rw [grid_width_eq]
    have hm := half_pow_antitone (show m ≤ b + 2 by omega)
    have hnm' := half_pow_antitone (show n + 1 ≤ m by omega)
    dsimp only at hnm'
    rw [pow_succ] at hnm'
    norm_num at hnm'
    have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ m := by positivity
    have hd : ((2 : ℝ)⁻¹) ^ m ≤ ((2 : ℝ)⁻¹) ^ n - ((2 : ℝ)⁻¹) ^ m := by
      linarith
    have hmultip := mul_le_mul_of_nonneg_right ht.1 (show 0 ≤ ((2 : ℝ)⁻¹) ^ n - ((2 : ℝ)⁻¹) ^ m by linarith)
    nlinarith
  · rw [grid_width_eq]
    have hn := half_pow_antitone (show 3 ≤ n by omega)
    have hb := half_pow_antitone (show 2 ≤ b + 2 by omega)
    norm_num at hn hb
    have hpn : 0 ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
    have hpm : 0 ≤ t * ((2 : ℝ)⁻¹) ^ m := mul_nonneg (by linarith [ht.1]) (by positivity)
    nlinarith [ht.2]

/-- The no-crossing stability condition for a later window preserves an earlier key. -/
theorem dyadicGridKey_eq_of_stable {a b n : ℕ} {x t : ℝ}
    (han : a ≤ n) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (hstable : ∀ k : ℤ, (k : ℝ) / (2 : ℝ) ^ (b + 2) ∉
      Set.Ioc x (x + 2 * ((2 : ℝ)⁻¹) ^ a)) :
    dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ n) = dyadicGridKey b x := by
  have hp : 0 ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
  have hp' : 0 ≤ ((2 : ℝ)⁻¹) ^ a := by positivity
  have hn := half_pow_antitone han
  have hstep : 0 ≤ t * ((2 : ℝ)⁻¹) ^ n :=
    mul_nonneg (by linarith [ht.1]) hp
  have hbound : t * ((2 : ℝ)⁻¹) ^ n ≤ 2 * ((2 : ℝ)⁻¹) ^ a := by
    nlinarith [ht.2]
  have hkey := periodicGridKey_eq_of_no_crossing ((2 : ℕ) ^ (b + 2))
    (by positivity) (show x ≤ x + t * ((2 : ℝ)⁻¹) ^ n by linarith)
    (fun k hk ↦ hstable k ⟨by simpa using hk.1, by
      have hk' : (k : ℝ) / (2 : ℝ) ^ (b + 2) ≤ x + t * ((2 : ℝ)⁻¹) ^ n := by
        simpa using hk.2
      linarith⟩)
  simpa [dyadicGridKey] using hkey.symm

/-- All the trial addresses in one dyadic window are distinct. -/
theorem dyadicGridKey_injOn_window {a b : ℕ} {x t : ℝ}
    (ha : 3 ≤ a) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    Set.InjOn (fun n : ℕ ↦ dyadicGridKey b (x + t * ((2 : ℝ)⁻¹) ^ n))
      (Set.Icc a b) := by
  intro n hn m hm heq
  rcases lt_trichotomy n m with h | h | h
  · exact False.elim (dyadicGridKey_pair_ne ha hn.1 h hm.2 ht heq.symm)
  · exact h
  · exact False.elim (dyadicGridKey_pair_ne ha hm.1 h hn.2 ht heq)

end Problem310

end

end OAI
