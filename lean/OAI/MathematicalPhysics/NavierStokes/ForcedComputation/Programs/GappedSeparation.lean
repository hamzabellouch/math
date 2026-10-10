import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.GappedInstructions

namespace OAI

/-! Quantitative gaps for one- and two-symbol filled radix cylinders. -/

noncomputable section

namespace ForcedComputation.Radix

open Set

def Separated (δ : ℝ) (S T : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, δ ≤ |x - y|

theorem Separated.symm {δ : ℝ} {S T : Set ℝ} (h : Separated δ S T) :
    Separated δ T S := by
  intro x hx y hy
  simpa only [abs_sub_comm] using h y hy x hx

theorem cylinder_separated {B : ℝ} (hB : 0 < B) {a b : ℝ}
    (hab : 2 ≤ |a - b|) : Separated (1 / B) (cylinder B a) (cylinder B b) := by
  intro x hx y hy
  rcases le_total a b with h | h
  · have hg : a + 2 ≤ b := by rw [abs_of_nonpos (sub_nonpos.mpr h)] at hab; linarith
    calc
      1 / B ≤ y - x := cylinder_gap hB hg hx hy
      _ ≤ |y - x| := le_abs_self _
      _ = |x - y| := abs_sub_comm _ _
  · have hg : b + 2 ≤ a := by rw [abs_of_nonneg (sub_nonneg.mpr h)] at hab; linarith
    exact (cylinder_gap hB hg hy hx).trans (le_abs_self _)

theorem cylinder_subset_unit {B d : ℝ} (hB : 0 < B)
    (hd : 0 ≤ d ∧ d + 1 ≤ B) : cylinder B d ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  refine ⟨(div_nonneg hd.1 hB.le).trans hx.1, hx.2.trans ?_⟩
  exact (div_le_one hB).mpr hd.2

theorem nested_subset_cylinder {B a d : ℝ} (hB : 0 < B)
    (hd : 0 ≤ d ∧ d + 1 ≤ B) :
    push B a '' cylinder B d ⊆ cylinder B a := by
  rintro x ⟨y, hy, rfl⟩
  exact (push_mem_cylinder hB a).mpr (cylinder_subset_unit hB hd hy)

theorem nested_same_separated {B : ℝ} (hB : 0 < B) (a : ℝ) {d e : ℝ}
    (hde : 2 ≤ |d - e|) :
    Separated (1 / B ^ 2) (push B a '' cylinder B d) (push B a '' cylinder B e) := by
  rintro x ⟨u, hu, rfl⟩ y ⟨v, hv, rfl⟩
  have hg := cylinder_separated hB hde u hu v hv
  calc
    1 / B ^ 2 = (1 / B) / B := by ring
    _ ≤ |u - v| / B := (div_le_div_iff_of_pos_right hB).mpr hg
    _ = |push B a u - push B a v| := by
      rw [show push B a u - push B a v = (u - v) / B by dsimp [push]; ring,
        abs_div, abs_of_pos hB]

theorem nested_different_separated {B : ℝ} (hB : 1 ≤ B)
    {a b d e : ℝ} (hab : 2 ≤ |a - b|)
    (hd : 0 ≤ d ∧ d + 1 ≤ B) (he : 0 ≤ e ∧ e + 1 ≤ B) :
    Separated (1 / B ^ 2) (push B a '' cylinder B d) (push B b '' cylinder B e) := by
  have hp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBB : B ≤ B ^ 2 := by nlinarith
  have hrecip : 1 / B ^ 2 ≤ 1 / B := one_div_le_one_div_of_le hp hBB
  intro x hx y hy
  exact hrecip.trans (cylinder_separated hp hab x (nested_subset_cylinder hp hd hx)
    y (nested_subset_cylinder hp he hy))

def rationalBase (N : ℕ) : ℚ := 2 * N + 2

def rationalDigit {N : ℕ} (a : Fin N) : ℚ := 2 * a.val + 1

theorem rationalBase_ge_one (N : ℕ) : (1 : ℝ) ≤ (rationalBase N : ℝ) := by
  simp only [rationalBase, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat]
  nlinarith [show (0 : ℝ) ≤ N by positivity]

theorem rationalDigit_bounds {N : ℕ} (a : Fin N) :
    0 ≤ (rationalDigit a : ℝ) ∧ (rationalDigit a : ℝ) + 1 ≤ (rationalBase N : ℝ) := by
  have ha : (a.val : ℝ) < N := by exact_mod_cast a.isLt
  simp only [rationalDigit, rationalBase, Rat.cast_add, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
  constructor <;> nlinarith [show (0 : ℝ) ≤ a.val by positivity]

theorem rationalDigit_gap {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    2 ≤ |(rationalDigit a : ℝ) - (rationalDigit b : ℝ)| := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hh : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    rw [abs_of_nonpos]
    · simp only [rationalDigit, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_one, Rat.cast_ofNat]
      linarith
    · simp only [rationalDigit, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_one, Rat.cast_ofNat]
      linarith
  · have hh : (b.val : ℝ) + 1 ≤ a.val := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    rw [abs_of_nonneg]
    · simp only [rationalDigit, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_one, Rat.cast_ofNat]
      linarith
    · simp only [rationalDigit, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
        Rat.cast_one, Rat.cast_ofNat]
      linarith

/-- Distinct two-symbol words have a gap at least one inverse square base. -/
theorem twoSymbol_separated {N : ℕ} (a b d e : Fin N) (hne : (a, d) ≠ (b, e)) :
    Separated (1 / (rationalBase N : ℝ) ^ 2)
      (push (rationalBase N) (rationalDigit a) ''
        cylinder (rationalBase N) (rationalDigit d))
      (push (rationalBase N) (rationalDigit b) ''
        cylinder (rationalBase N) (rationalDigit e)) := by
  by_cases hab : a = b
  · subst b
    have hde : d ≠ e := by intro h; exact hne (by simp [h])
    exact nested_same_separated (lt_of_lt_of_le zero_lt_one (rationalBase_ge_one N)) _
      (rationalDigit_gap hde)
  · exact nested_different_separated (rationalBase_ge_one N) (rationalDigit_gap hab)
      (rationalDigit_bounds d) (rationalDigit_bounds e)

end ForcedComputation.Radix

end

end OAI
