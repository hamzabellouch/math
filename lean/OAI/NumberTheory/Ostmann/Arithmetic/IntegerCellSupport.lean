import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellCount

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.IntegerCell
open scoped BigOperators

def integerSupport (N M : ℕ) (a : ZMod M) (lo hi : ℝ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun n =>
    0 < n ∧ lo ≤ Real.log n ∧ Real.log n ≤ hi ∧ (n : ZMod M) = a

def openSupport (M : ℕ) (a : ZMod M) (lo hi : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp lo⌋₊ ⌊Real.exp hi⌋₊).filter fun n => (n : ZMod M) = a

theorem mem_integerSupport (N M : ℕ) (a : ZMod M) (lo hi : ℝ)
    (hN : ⌊Real.exp hi⌋₊ ≤ N) (n : ℕ) :
    n ∈ integerSupport N M a lo hi ↔
      Real.exp lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ Real.exp hi ∧ (n : ZMod M) = a := by
  simp only [integerSupport, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hn, hlo, hhi, ha⟩
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    exact ⟨(Real.le_log_iff_exp_le hnp).mp hlo, (Real.log_le_iff_le_exp hnp).mp hhi, ha⟩
  · rintro ⟨hlo, hhi, ha⟩
    have hnp : (0 : ℝ) < n := (Real.exp_pos lo).trans_le hlo
    have hn : n ≤ ⌊Real.exp hi⌋₊ := (Nat.le_floor_iff (Real.exp_pos hi).le).mpr hhi
    refine ⟨by omega, by exact_mod_cast hnp,
      (Real.le_log_iff_exp_le hnp).mpr hlo, (Real.log_le_iff_le_exp hnp).mpr hhi, ha⟩

theorem mem_openSupport (M : ℕ) (a : ZMod M) (lo hi : ℝ) (n : ℕ) :
    n ∈ openSupport M a lo hi ↔
      Real.exp lo < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp hi ∧ (n : ZMod M) = a := by
  simp only [openSupport, Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt (Real.exp_pos lo).le, Nat.le_floor_iff (Real.exp_pos hi).le, and_assoc]

theorem openSupport_subset (N M : ℕ) (a : ZMod M) (lo hi : ℝ)
    (hN : ⌊Real.exp hi⌋₊ ≤ N) :
    openSupport M a lo hi ⊆ integerSupport N M a lo hi := by
  intro n hn
  obtain ⟨hl, hh, ha⟩ := (mem_openSupport M a lo hi n).mp hn
  exact (mem_integerSupport N M a lo hi hN n).mpr ⟨hl.le, hh, ha⟩

theorem support_sdiff_subset (N M : ℕ) (a : ZMod M) (lo hi : ℝ)
    (hN : ⌊Real.exp hi⌋₊ ≤ N) :
    integerSupport N M a lo hi \ openSupport M a lo hi ⊆ {⌊Real.exp lo⌋₊} := by
  intro n hn
  obtain ⟨hc, ho⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨hl, hh, ha⟩ := (mem_integerSupport N M a lo hi hN n).mp hc
  have hlo : ⌊Real.exp lo⌋₊ ≤ n := by
    simpa only [Nat.floor_natCast] using Nat.floor_le_floor hl
  have hhi : n ≤ ⌊Real.exp lo⌋₊ := by
    by_contra h
    apply ho
    exact (mem_openSupport M a lo hi n).mpr
      ⟨(Nat.floor_lt (Real.exp_pos lo).le).mp (by omega), hh, ha⟩
  exact Finset.mem_singleton.mpr (le_antisymm hhi hlo)

theorem closed_endpoint_error (N M : ℕ) (a : ZMod M) (lo hi : ℝ)
    (hN : ⌊Real.exp hi⌋₊ ≤ N) (f : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n ∈ integerSupport N M a lo hi, |f n| ≤ B) :
    |(∑ n ∈ integerSupport N M a lo hi, f n) -
      (∑ n ∈ openSupport M a lo hi, f n)| ≤ B := by
  rw [← Finset.sum_sdiff_eq_sub (openSupport_subset N M a lo hi hN)]
  have hc : (integerSupport N M a lo hi \ openSupport M a lo hi).card ≤ 1 := by
    simpa only [Finset.card_singleton] using
      Finset.card_le_card (support_sdiff_subset N M a lo hi hN)
  calc
    _ ≤ ∑ n ∈ integerSupport N M a lo hi \ openSupport M a lo hi, |f n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ integerSupport N M a lo hi \ openSupport M a lo hi, B :=
      Finset.sum_le_sum (fun n hn => hf n (Finset.mem_sdiff.mp hn).1)
    _ = ((integerSupport N M a lo hi \ openSupport M a lo hi).card : ℝ)*B := by simp
    _ ≤ 1*B := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
    _ = _ := one_mul B

theorem openSupport_sum (M : ℕ) (a : ZMod M) (lo hi : ℝ) (f : ℝ → ℝ) :
    (∑ n ∈ Finset.Ioc ⌊Real.exp lo⌋₊ ⌊Real.exp hi⌋₊, f n*residueIndicator M a n) =
      ∑ n ∈ openSupport M a lo hi, f n := by
  simp only [openSupport, residueIndicator, mul_ite, mul_one, mul_zero, Finset.sum_filter]

def integerResidueMass (N M : ℕ) (a : ZMod M) (lo hi G : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∑ n ∈ integerSupport N M a lo hi, Real.exp (-G)*φ (Real.log n-G)

end Ostmann.Arithmetic.IntegerCell
end

end OAI
