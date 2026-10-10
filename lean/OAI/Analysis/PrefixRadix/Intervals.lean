import Mathlib
import OAI.Analysis.PrefixRadix.Codes

namespace OAI

/-! Closed prefix intervals and quantitative separation. -/

noncomputable section
open scoped ContDiff
namespace PrefixFlows
namespace Radix
namespace System
variable {A : Type*} (C : System A)
def finiteCode : List A → ℝ
  | [] => 0
  | a :: w => (C.digit a + finiteCode w) / C.base

def interval (w : List A) : Set ℝ :=
  Set.Icc (C.finiteCode w) (C.finiteCode w + C.rate ^ w.length)

 
theorem code_prepend (w : List A) (L : Interspersed.Stack A) :
    C.code (Interspersed.prepend w L) =
      C.finiteCode w + C.rate ^ w.length * C.code L := by
  induction w with
  | nil => simp [finiteCode]
  | cons a w ih =>
    simp only [Interspersed.prepend_cons, C.code_push, ih, finiteCode, List.length_cons, pow_succ]
    simp only [rate, div_eq_mul_inv]
    ring

 

theorem code_blank_tail (w : List A) (b : A) :
    C.code (Interspersed.prepend w (fun _ => b)) =
      C.finiteCode w + C.rate ^ w.length * (C.digit b / (C.base - 1)) := by
  rw [C.code_prepend, C.code_constant]

theorem code_mem_interval (w : List A) (L : Interspersed.Stack A) :
    C.code (Interspersed.prepend w L) ∈ C.interval w := by
  rw [C.code_prepend]
  have h := C.code_mem_unit L
  have hr := pow_nonneg C.rate_pos.le w.length
  exact ⟨le_add_of_nonneg_right (mul_nonneg hr h.1),
    add_le_add_right (by simpa using mul_le_mul_of_nonneg_left h.2 hr) _⟩

theorem finite_bounds (w : List A) :
    0 ≤ C.finiteCode w ∧ C.finiteCode w + C.rate ^ w.length ≤ 1 := by
  induction w with
  | nil => simp [finiteCode]
  | cons a w ih =>
    have hb := C.base_pos
    have hl : 0 ≤ (C.digit a + C.finiteCode w) / C.base :=
      div_nonneg (add_nonneg (C.digit_nonneg _) ih.1) hb.le
    refine ⟨hl, ?_⟩
    have hu : C.digit a + C.finiteCode w + C.rate ^ w.length ≤ C.base := by
      linarith [C.digit_le a, ih.2]
    have hre : C.finiteCode (a :: w) + C.rate ^ (a :: w).length =
        (C.digit a + C.finiteCode w + C.rate ^ w.length) / C.base := by
      simp only [finiteCode, List.length_cons, pow_succ, rate, div_eq_mul_inv]
      ring
    rw [hre]
    exact (div_le_iff₀ hb).2 (by simpa using hu)

theorem interval_subset_unit (w : List A) : C.interval w ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨(C.finite_bounds w).1.trans hx.1, hx.2.trans (C.finite_bounds w).2⟩

 

theorem mem_interval_cons (a : A) (w : List A) (x : ℝ) :
    x ∈ C.interval (a :: w) ↔ C.base * x - C.digit a ∈ C.interval w := by
  have hb := C.base_pos
  have hl : C.base * C.finiteCode (a :: w) = C.digit a + C.finiteCode w := by
    dsimp only [finiteCode]
    field_simp [ne_of_gt hb]
  have hu : C.base * (C.finiteCode (a :: w) + C.rate ^ (a :: w).length) =
      C.digit a + (C.finiteCode w + C.rate ^ w.length) := by
    simp only [finiteCode, List.length_cons, pow_succ, rate, div_eq_mul_inv]
    field_simp
    ring
  constructor
  · intro hx
    constructor
    · have h := mul_le_mul_of_nonneg_left hx.1 hb.le
      rw [hl] at h
      linarith
    · have h := mul_le_mul_of_nonneg_left hx.2 hb.le
      rw [hu] at h
      linarith
  · intro hx
    constructor
    · apply (mul_le_mul_iff_right₀ hb).mp
      rw [hl]
      linarith [hx.1]
    · apply (mul_le_mul_iff_right₀ hb).mp
      rw [hu]
      linarith [hx.2]

 

theorem incompatible_intervals_separated (v w : List A)
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ C.interval v, ∀ y ∈ C.interval w, ε ≤ |x - y| := by
  classical
  induction v generalizing w with
  | nil => exact (hvw List.nil_prefix).elim
  | cons a v ih =>
    cases w with
    | nil => exact (hwv List.nil_prefix).elim
    | cons b w =>
      by_cases hab : a = b
      · subst b
        have hvw' : ¬ v <+: w := by simpa only [List.prefix_cons_inj] using hvw
        have hwv' : ¬ w <+: v := by simpa only [List.prefix_cons_inj] using hwv
        rcases ih w hvw' hwv' with ⟨ε, hε, hgap⟩
        refine ⟨ε / C.base, div_pos hε C.base_pos, ?_⟩
        intro x hx y hy
        have hg := hgap _ ((C.mem_interval_cons a v x).1 hx)
          _ ((C.mem_interval_cons a w y).1 hy)
        have hid : |(C.base * x - C.digit a) - (C.base * y - C.digit a)| =
            C.base * |x - y| := by
          calc
            _ = |C.base * (x - y)| := by ring_nf
            _ = _ := by rw [abs_mul, abs_of_pos C.base_pos]
        rw [hid] at hg
        exact (div_le_iff₀ C.base_pos).2 (by linarith)
      · refine ⟨C.rate, C.rate_pos, ?_⟩
        intro x hx y hy
        have hx' := C.interval_subset_unit v ((C.mem_interval_cons a v x).1 hx)
        have hy' := C.interval_subset_unit w ((C.mem_interval_cons b w y).1 hy)
        have hg := C.first_letter_gap hab hx' hy'
        have hax : (C.digit a + (C.base * x - C.digit a)) / C.base = x := by
          field_simp [ne_of_gt C.base_pos]
          ring
        have hby : (C.digit b + (C.base * y - C.digit b)) / C.base = y := by
          field_simp [ne_of_gt C.base_pos]
          ring
        simpa only [hax, hby] using hg

theorem incompatible_intervals_disjoint (v w : List A)
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) : Disjoint (C.interval v) (C.interval w) := by
  rcases C.incompatible_intervals_separated v w hvw hwv with ⟨ε, hε, hgap⟩
  rw [Set.disjoint_left]
  intro x hx hy
  have h := hgap x hx x hy
  exact hε.not_ge (by simpa only [sub_self, abs_zero] using h)
end System
end Radix
end PrefixFlows
end

end OAI
