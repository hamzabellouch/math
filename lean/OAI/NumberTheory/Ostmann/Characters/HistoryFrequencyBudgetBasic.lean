import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabels

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HistoryFrequencyBudget

def exponent (a m : ℝ) (l : ℕ) : ℝ :=
  (2:ℝ)^l*a*m + 2*(4:ℝ)^l*Real.sqrt m

def bound (a m : ℝ) (l : ℕ) : ℕ := ⌊Real.exp (exponent a m l)⌋₊

def signedRange (V : ℕ) : Finset ℤ := (Finset.Icc (-(V:ℤ)) (V:ℤ)).erase 0

def ranges (a m : ℝ) (j : ℕ) (p : List Bool) : Finset ℤ :=
  signedRange (bound a m (j-p.length))

theorem mem_signedRange (V : ℕ) (s : ℤ) :
    s ∈ signedRange V ↔ s ≠ 0 ∧ s.natAbs ≤ V := by
  simp only [signedRange,Finset.mem_erase,Finset.mem_Icc]
  constructor
  · rintro ⟨hs,hl,hu⟩
    refine ⟨hs,?_⟩
    have ha := abs_le.mpr ⟨hl,hu⟩
    rw [Int.abs_eq_natAbs] at ha
    exact_mod_cast ha
  · rintro ⟨hs,ha⟩
    have ha' : |s| ≤ (V:ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ha
    exact ⟨hs,abs_le.mp ha'⟩

theorem signedRange_card (V : ℕ) : (signedRange V).card = 2*V := by
  have hz : (0:ℤ) ∈ Finset.Icc (-(V:ℤ)) (V:ℤ) := by simp
  simp only [signedRange,Finset.card_erase_of_mem hz,Int.card_Icc]
  omega

theorem exponent_nonneg {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (l : ℕ) :
    0 ≤ exponent a m l := by unfold exponent; positivity

theorem bound_pos {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) (l : ℕ) :
    1 ≤ bound a m l := by
  apply (Nat.le_floor_iff (Real.exp_pos _).le).mpr
  simpa using Real.one_le_exp (exponent_nonneg ha hm l)

theorem bound_le_exp (a m : ℝ) (l : ℕ) :
    (bound a m l:ℝ) ≤ Real.exp (exponent a m l) := Nat.floor_le (Real.exp_pos _).le

def linearEnvelope (a : ℝ) (j : ℕ) : ℝ := (2:ℝ)^j*a + 2*(4:ℝ)^j

theorem linearEnvelope_pos {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    0 < linearEnvelope a j := by unfold linearEnvelope; positivity

theorem exponent_le_linear {a m : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m)
    {l j : ℕ} (hl : l ≤ j) : exponent a m l ≤ linearEnvelope a j*m := by
  have h2 : (2:ℝ)^l ≤ 2^j := pow_le_pow_right₀ (by norm_num) hl
  have h4 : (4:ℝ)^l ≤ 4^j := pow_le_pow_right₀ (by norm_num) hl
  have hs : Real.sqrt m ≤ m := Real.sqrt_le_self_iff.mpr (Or.inr hm)
  unfold exponent linearEnvelope
  calc
    _ ≤ (2:ℝ)^j*a*m + 2*(4:ℝ)^j*m := by gcongr
    _ = _ := by ring

theorem budget_exp_bound (S : List Bool → Finset ℤ) (C : List Bool → ℝ)
    (N : ℕ) (L B : ℝ) (hC : ∀ p, 0 ≤ C p)
    (hnode : ∀ p, C p ≤ Real.exp B)
    (hleaf : ∀ p, p.length = N → ((S p).card:ℝ) ≤ Real.exp L)
    (k : ℕ) (p : List Bool) (hp : k+p.length=N) :
    FrequencyTreeSum.budget S C k p ≤
      Real.exp ((2:ℝ)^k*L+((2:ℝ)^k-1)*B) := by
  have hn (k : ℕ) (p : List Bool) : 0 ≤ FrequencyTreeSum.budget S C k p := by
    induction k generalizing p with
    | zero => exact Nat.cast_nonneg _
    | succ k ih => exact mul_nonneg (mul_nonneg (hC p) (ih _)) (ih _)
  induction k generalizing p with
  | zero => simpa only [FrequencyTreeSum.budget,pow_zero,one_mul,sub_self,zero_mul,add_zero]
      using hleaf p (by omega)
  | succ k ih =>
    have hl := ih (false::p) (by simp only [List.length_cons]; omega)
    have hr := ih (true::p) (by simp only [List.length_cons]; omega)
    calc
      _ ≤ Real.exp B * Real.exp ((2:ℝ)^k*L+((2:ℝ)^k-1)*B) *
          Real.exp ((2:ℝ)^k*L+((2:ℝ)^k-1)*B) :=
        mul_le_mul (mul_le_mul (hnode p) hl (hn _ _) (Real.exp_pos _).le)
          hr (hn _ _) (by positivity)
      _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; rw [pow_succ]; ring

end Ostmann.Characters.HistoryFrequencyBudget

end

end OAI
