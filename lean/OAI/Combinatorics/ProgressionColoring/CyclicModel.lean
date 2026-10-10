import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.Combinatorics.ProgressionColoring.CyclicBasic

namespace OAI

universe uA

namespace QuantitativeVanDerWaerden

open scoped BigOperators

abbrev CyclicGroup (q D : ℕ) := ZMod (q ^ D)

noncomputable def centered (x : ℝ) : ℝ := x - (⌊x + 1 / 2⌋ : ℤ)

theorem centered_mem (x : ℝ) : -(1 / 2 : ℝ) ≤ centered x ∧ centered x < 1 / 2 := by
  have h₁ := Int.floor_le (x + 1 / 2)
  have h₂ := Int.lt_floor_add_one (x + 1 / 2)
  constructor <;> dsimp [centered] <;> linarith

theorem centered_add_int (x : ℝ) (z : ℤ) : centered (x + z) = centered x := by
  unfold centered
  rw [show x + (z : ℝ) + 1 / 2 = (x + 1 / 2) + z by ring,
    Int.floor_add_intCast, Int.cast_add]
  ring

theorem centered_int (z : ℤ) : centered (z : ℝ) = 0 := by
  have hz := centered_add_int 0 z
  norm_num [centered] at hz ⊢

noncomputable def xRep (q D : ℕ) (n : CyclicGroup q D) (i : Fin D) : ℝ :=
  Int.fract ((n.val : ℝ) / (q : ℝ) ^ (i.val + 1))

noncomputable def yRep (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D) : ℝ :=
  centered (((((dilation : CyclicGroup q D) * n).val : ℕ) : ℝ) /
    (q : ℝ) ^ (i.val + 1))

theorem xRep_mem (q D : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    0 ≤ xRep q D n i ∧ xRep q D n i < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem yRep_mem (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    -(1 / 2 : ℝ) ≤ yRep q D dilation n i ∧ yRep q D dilation n i < 1 / 2 :=
  centered_mem _

/-- Dividing congruent integers by any divisor of the modulus gives real
representatives differing by an integer. -/
theorem quotient_integer_difference {N m : ℕ} (hm : 0 < m) (hdiv : m ∣ N)
    {a b : ℤ} (hab : (a : ZMod N) = (b : ZMod N)) :
    ∃ z : ℤ, (a : ℝ) / m - (b : ℝ) / m = z := by
  have hz : ((a - b : ℤ) : ZMod N) = 0 := by
    push_cast
    exact sub_eq_zero.mpr hab
  have hdN : (N : ℤ) ∣ a - b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  have hdm : (m : ℤ) ∣ a - b := (Int.natCast_dvd_natCast.mpr hdiv).trans hdN
  obtain ⟨z, hz⟩ := hdm
  refine ⟨z, ?_⟩
  have hr : (a : ℝ) - b = (m : ℝ) * z := by exact_mod_cast hz
  have hmR : (m : ℝ) ≠ 0 := by positivity
  rw [← sub_div, hr, mul_div_cancel_left₀ _ hmR]

theorem xRep_integer_offset (q D : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, xRep q D n i - (n.val : ℝ) / (q : ℝ) ^ (i.val + 1) = z := by
  refine ⟨-⌊(n.val : ℝ) / (q : ℝ) ^ (i.val + 1)⌋, ?_⟩
  simp only [xRep, Int.fract, Int.cast_neg]
  ring

theorem yRep_integer_offset (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation n i -
      (((dilation : CyclicGroup q D) * n).val : ℝ) / (q : ℝ) ^ (i.val + 1) = z := by
  refine ⟨-⌊(((dilation : CyclicGroup q D) * n).val : ℝ) /
    (q : ℝ) ^ (i.val + 1) + 1 / 2⌋, ?_⟩
  simp only [yRep, centered, Int.cast_neg]
  ring

theorem val_add_integer_difference {q D : ℕ} (hq : 0 < q)
    (a b : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, ((a + b).val : ℝ) / (q : ℝ) ^ (i.val + 1) -
      ((a.val : ℝ) / (q : ℝ) ^ (i.val + 1) +
        (b.val : ℝ) / (q : ℝ) ^ (i.val + 1)) = z := by
  let : NeZero (q ^ D) := ⟨(pow_pos hq D).ne'⟩
  have hi : i.val + 1 ≤ D := i.isLt
  have hab : (((a + b).val : ℤ) : ZMod (q ^ D)) =
      (((a.val : ℤ) + b.val : ℤ) : ZMod (q ^ D)) := by
    simp
  obtain ⟨z, hz⟩ := quotient_integer_difference (pow_pos hq (i.val + 1))
    (pow_dvd_pow q hi) hab
  refine ⟨z, ?_⟩
  simpa only [Int.cast_natCast, Int.cast_add, Nat.cast_pow, add_div] using hz

theorem xRep_add_congr {q D : ℕ} (hq : 0 < q)
    (a b : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, xRep q D (a + b) i - (xRep q D a i + xRep q D b i) = z := by
  obtain ⟨z₁, h₁⟩ := xRep_integer_offset q D (a + b) i
  obtain ⟨z₂, h₂⟩ := xRep_integer_offset q D a i
  obtain ⟨z₃, h₃⟩ := xRep_integer_offset q D b i
  obtain ⟨z₄, h₄⟩ := val_add_integer_difference hq a b i
  refine ⟨z₁ - z₂ - z₃ + z₄, ?_⟩
  push_cast
  linarith

theorem yRep_add_congr {q D : ℕ} (hq : 0 < q) (dilation : ℕ)
    (a b : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation (a + b) i -
      (yRep q D dilation a i + yRep q D dilation b i) = z := by
  obtain ⟨z₁, h₁⟩ := yRep_integer_offset q D dilation (a + b) i
  obtain ⟨z₂, h₂⟩ := yRep_integer_offset q D dilation a i
  obtain ⟨z₃, h₃⟩ := yRep_integer_offset q D dilation b i
  obtain ⟨z₄, h₄⟩ := val_add_integer_difference hq
    ((dilation : CyclicGroup q D) * a) ((dilation : CyclicGroup q D) * b) i
  rw [mul_add] at h₁
  refine ⟨z₁ - z₂ - z₃ + z₄, ?_⟩
  push_cast
  linarith

theorem representative_ap_congr {A : Type uA} [AddMonoid A] (f : A → ℝ)
    (_hzero : f 0 = 0)
    (hadd : ∀ a b, ∃ z : ℤ, f (a + b) - (f a + f b) = z)
    (a d : A) (j : ℕ) :
    ∃ z : ℤ, f (a + j • d) - f a - (j : ℝ) * f d = z := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨z₁, h₁⟩ := ih
    obtain ⟨z₂, h₂⟩ := hadd (a + j • d) d
    refine ⟨z₁ + z₂, ?_⟩
    rw [succ_nsmul, ← add_assoc]
    push_cast
    linarith

theorem xRep_ap_congr {q D : ℕ} (hq : 0 < q)
    (a d : CyclicGroup q D) (j : ℕ) (i : Fin D) :
    ∃ z : ℤ, xRep q D (a + j • d) i - xRep q D a i -
      (j : ℝ) * xRep q D d i = z := by
  apply representative_ap_congr (fun n => xRep q D n i)
  · simp [xRep]
  · exact fun a b => xRep_add_congr hq a b i

theorem yRep_ap_congr {q D : ℕ} (hq : 0 < q) (dilation : ℕ)
    (a d : CyclicGroup q D) (j : ℕ) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation (a + j • d) i - yRep q D dilation a i -
      (j : ℝ) * yRep q D dilation d i = z := by
  apply representative_ap_congr (fun n => yRep q D dilation n i)
  · simpa [yRep] using centered_int 0
  · exact fun a b => yRep_add_congr hq dilation a b i

theorem yRep_dilation_congr {q D : ℕ} (hq : 0 < q) (dilation : ℕ)
    (n : CyclicGroup q D) (i : Fin D) :
    ∃ z : ℤ, yRep q D dilation n i - (dilation : ℝ) * xRep q D n i = z := by
  let : NeZero (q ^ D) := ⟨(pow_pos hq D).ne'⟩
  have hab : (((((dilation : CyclicGroup q D) * n).val : ℕ) : ℤ) :
      ZMod (q ^ D)) = (((dilation : ℤ) * n.val : ℤ) : ZMod (q ^ D)) := by simp
  obtain ⟨z₁, h₁⟩ := quotient_integer_difference (pow_pos hq (i.val + 1))
    (pow_dvd_pow q (show i.val + 1 ≤ D from i.isLt)) hab
  obtain ⟨z₂, h₂⟩ := yRep_integer_offset q D dilation n i
  obtain ⟨z₃, h₃⟩ := xRep_integer_offset q D n i
  refine ⟨z₁ + z₂ - dilation * z₃, ?_⟩
  simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_pow] at h₁
  rw [mul_div_assoc] at h₁
  push_cast
  nlinarith [h₁, h₂, h₃, congrArg (fun t : ℝ => (dilation : ℝ) * t) h₃]

/-- Every centered coordinate lies in the claimed discrete lattice. -/
theorem yRep_lattice (q D dilation : ℕ) (n : CyclicGroup q D) (i : Fin D)
    (hq : 0 < q) :
    ∃ z : ℤ, (q : ℝ) ^ (i.val + 1) * yRep q D dilation n i = z := by
  let a := ((dilation : CyclicGroup q D) * n).val
  let b : ℤ := ⌊(a : ℝ) / (q : ℝ) ^ (i.val + 1) + 1 / 2⌋
  refine ⟨(a : ℤ) - (q : ℤ) ^ (i.val + 1) * b, ?_⟩
  change (q : ℝ) ^ (i.val + 1) *
    ((a : ℝ) / (q : ℝ) ^ (i.val + 1) - (b : ℝ)) = _
  push_cast
  have hqR : (q : ℝ) ^ (i.val + 1) ≠ 0 := by positivity
  field_simp

theorem integer_eq_zero_of_abs_lt_one {z : ℤ} (h : |(z : ℝ)| < 1) : z = 0 := by
  have hh : -(1 : ℤ) < z ∧ z < 1 := by exact_mod_cast (abs_lt.mp h)
  omega

theorem lattice_separation {m : ℕ} (hm : 0 < m) {w : ℝ}
    (hw : ∃ z : ℤ, (m : ℝ) * w = z) (hne : w ≠ 0) : 1 / (m : ℝ) ≤ |w| := by
  obtain ⟨z, hz⟩ := hw
  have hzne : z ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hz
    exact hne ((mul_eq_zero.mp hz).resolve_left (by positivity))
  have hzabs : 1 ≤ |(z : ℝ)| := by
    by_contra h
    exact hzne (integer_eq_zero_of_abs_lt_one (lt_of_not_ge h))
  have hmR : 0 < (m : ℝ) := by positivity
  rw [← hz, abs_mul, abs_of_pos hmR] at hzabs
  exact (div_le_iff₀ hmR).mpr (by simpa [mul_comm] using hzabs)

/-- The representative at exponent zero is included as an auxiliary coordinate. -/
noncomputable def centeredDigit (q a j : ℕ) : ℝ := centered ((a : ℝ) / (q : ℝ) ^ j)

theorem centeredDigit_zero (q a : ℕ) : centeredDigit q a 0 = 0 := by
  simpa [centeredDigit] using centered_int (a : ℤ)

theorem centeredDigit_recurrence {q : ℕ} (hq : 0 < q) (a j : ℕ) :
    ∃ z : ℤ, (q : ℝ) * centeredDigit q a (j + 1) - centeredDigit q a j = z := by
  refine ⟨⌊(a : ℝ) / (q : ℝ) ^ j + 1 / 2⌋ -
    (q : ℤ) * ⌊(a : ℝ) / (q : ℝ) ^ (j + 1) + 1 / 2⌋, ?_⟩
  unfold centeredDigit centered
  push_cast
  have hqR : (q : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  ring

theorem centered_injective_on_unit_interval {x y : ℝ}
    (hx : 0 ≤ x ∧ x < 1) (hy : 0 ≤ y ∧ y < 1)
    (h : centered x = centered y) : x = y := by
  let z : ℤ := ⌊x + 1 / 2⌋ - ⌊y + 1 / 2⌋
  have hz : x - y = (z : ℝ) := by
    dsimp [centered] at h
    dsimp [z]
    push_cast
    linarith
  have hzabs : |(z : ℝ)| < 1 := by rw [← hz, abs_lt]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hz0 := integer_eq_zero_of_abs_lt_one hzabs
  rw [hz0, Int.cast_zero] at hz
  exact sub_eq_zero.mp hz

/-- The cyclic digit embedding separates distinct residues after multiplication
by `q`. This proof works for every positive base, not just primes. -/
theorem centeredDigit_separation {q D a b : ℕ} (hq : 0 < q)
    (ha : a < q ^ D) (hb : b < q ^ D) (hab : a ≠ b) :
    ∃ i : Fin D, 1 ≤ |(q : ℝ) *
      (centeredDigit q a (i.val + 1) - centeredDigit q b (i.val + 1))| := by
  by_contra! h
  have hdiff : ∀ j, j ≤ D → centeredDigit q a j - centeredDigit q b j = 0 := by
    intro j hj
    induction j with
    | zero => simp [centeredDigit_zero]
    | succ j ih =>
      have hp := ih (by omega)
      obtain ⟨za, hza⟩ := centeredDigit_recurrence hq a j
      obtain ⟨zb, hzb⟩ := centeredDigit_recurrence hq b j
      have hh : (q : ℝ) * (centeredDigit q a (j + 1) - centeredDigit q b (j + 1)) =
          ((za - zb : ℤ) : ℝ) := by push_cast; linarith
      have hz := integer_eq_zero_of_abs_lt_one
        (show |((za - zb : ℤ) : ℝ)| < 1 by rw [← hh]; exact h ⟨j, by omega⟩)
      rw [hz, Int.cast_zero] at hh
      exact (mul_eq_zero.mp hh).resolve_left (by positivity)
  have hN : 0 < (q : ℝ) ^ D := by positivity
  have habR : (a : ℝ) / (q : ℝ) ^ D = (b : ℝ) / (q : ℝ) ^ D := by
    apply centered_injective_on_unit_interval
    · constructor
      · positivity
      · apply (div_lt_one hN).mpr
        exact_mod_cast ha
    · constructor
      · positivity
      · apply (div_lt_one hN).mpr
        exact_mod_cast hb
    · exact sub_eq_zero.mp (hdiff D le_rfl)
  apply hab
  exact_mod_cast (div_left_inj' hN.ne').mp habR

theorem yRep_coordinate_separation {q D dilation : ℕ} (hq : 0 < q)
    (hunit : Nat.Coprime dilation (q ^ D))
    {a b : CyclicGroup q D} (hab : a ≠ b) :
    ∃ i : Fin D, 1 ≤ |(q : ℝ) * (yRep q D dilation a i - yRep q D dilation b i)| := by
  let : NeZero (q ^ D) := ⟨(pow_pos hq D).ne'⟩
  have hu : IsUnit (dilation : CyclicGroup q D) := (ZMod.isUnit_iff_coprime _ _).mpr hunit
  have hne : ((dilation : CyclicGroup q D) * a).val ≠
      ((dilation : CyclicGroup q D) * b).val := by
    intro h
    exact hab (hu.mul_left_cancel (ZMod.val_injective (q ^ D) h))
  exact centeredDigit_separation hq (ZMod.val_lt _) (ZMod.val_lt _) hne

theorem yRep_squared_separation {q D dilation : ℕ} (hq : 0 < q)
    (hunit : Nat.Coprime dilation (q ^ D))
    {a b : CyclicGroup q D} (hab : a ≠ b) :
    1 ≤ ∑ i : Fin D, ((q : ℝ) * yRep q D dilation a i -
      (q : ℝ) * yRep q D dilation b i) ^ 2 := by
  obtain ⟨i, hi⟩ := yRep_coordinate_separation hq hunit hab
  have hsq : 1 ≤ ((q : ℝ) * yRep q D dilation a i -
      (q : ℝ) * yRep q D dilation b i) ^ 2 := by
    rw [mul_sub] at hi
    nlinarith [sq_nonneg (|(q : ℝ) * yRep q D dilation a i -
      (q : ℝ) * yRep q D dilation b i| - 1),
      sq_abs ((q : ℝ) * yRep q D dilation a i - (q : ℝ) * yRep q D dilation b i)]
  exact hsq.trans (Finset.single_le_sum
    (fun j _ => sq_nonneg ((q : ℝ) * yRep q D dilation a j -
      (q : ℝ) * yRep q D dilation b j)) (Finset.mem_univ i))

theorem prime_power_step_ne {P e i j : ℕ} (hP : P.Prime)
    (hij : i < j) (hj : j < P) {d : ZMod (P ^ e)} (hd : d ≠ 0) :
    (i : ZMod (P ^ e)) * d ≠ (j : ZMod (P ^ e)) * d := by
  intro h
  have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
  have hlt : j - i < P := lt_of_le_of_lt (Nat.sub_le _ _) hj
  have hcop : Nat.Coprime (j - i) (P ^ e) :=
    (Nat.coprime_of_lt_prime (Nat.ne_of_gt hpos) hlt hP).symm.pow_right e
  have hu := (ZMod.isUnit_iff_coprime (j - i) (P ^ e)).mpr hcop
  have hz : ((j - i : ℕ) : ZMod (P ^ e)) * d = 0 := by
    rw [Nat.cast_sub hij.le, sub_mul, h, sub_self]
  exact hd (hu.mul_left_cancel (by simpa using hz))

theorem prime_power_ap_injective {P e k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (a d : ZMod (P ^ e)) (hd : d ≠ 0) :
    Function.Injective (fun j : Fin k => a + (j.val : ZMod (P ^ e)) * d) := by
  intro i j hij
  have hm := add_left_cancel hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact prime_power_step_ne hP hlt (lt_of_lt_of_le j.isLt hk) hd hm
  · exact prime_power_step_ne hP hlt (lt_of_lt_of_le i.isLt hk) hd hm.symm

theorem prime_power_ap_injective_pow {P e D k : ℕ} (hP : P.Prime) (hk : k ≤ P)
    (a d : CyclicGroup (P ^ e) D) (hd : d ≠ 0) :
    Function.Injective (fun j : Fin k => a + (j.val : CyclicGroup (P ^ e) D) * d) := by
  have hstep : ∀ i j : ℕ, i < j → j < P →
      (i : CyclicGroup (P ^ e) D) * d ≠ (j : CyclicGroup (P ^ e) D) * d := by
    intro i j hij hj heq
    have hpos : 0 < j - i := Nat.sub_pos_of_lt hij
    have hlt : j - i < P := lt_of_le_of_lt (Nat.sub_le _ _) hj
    have hcop : Nat.Coprime (j - i) ((P ^ e) ^ D) :=
      ((Nat.coprime_of_lt_prime (Nat.ne_of_gt hpos) hlt hP).symm.pow_right e).pow_right D
    have hu := (ZMod.isUnit_iff_coprime (j - i) ((P ^ e) ^ D)).mpr hcop
    have hz : ((j - i : ℕ) : CyclicGroup (P ^ e) D) * d = 0 := by
      rw [Nat.cast_sub hij.le, sub_mul, heq, sub_self]
    exact hd (hu.mul_left_cancel (by simpa using hz))
  intro i j hij
  have hm := add_left_cancel hij
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hstep i.val j.val hlt (lt_of_lt_of_le j.isLt hk) hm
  · exact hstep j.val i.val hlt (lt_of_lt_of_le i.isLt hk) hm.symm

end QuantitativeVanDerWaerden

end OAI
