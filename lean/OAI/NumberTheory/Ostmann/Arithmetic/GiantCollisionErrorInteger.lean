import OAI.NumberTheory.Ostmann.Arithmetic.GiantCollisionErrorBasic
import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellTests
import OAI.NumberTheory.Ostmann.Construction.DiagonalExternalMeasure

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.GiantCollisionError
open Construction

lemma exp_two_lt_eight : Real.exp 2 < 8 := by
  have h := Real.exp_one_lt_d9
  have hp := Real.exp_pos 1
  have he : Real.exp 2=Real.exp 1*Real.exp 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [he]
  nlinarith

theorem integerPivotCell_collision_card_le (G : ℝ) (q : ℕ) (hq : Nat.Prime q)
    (hlog : |Real.log q-G| ≤ 1) :
    ((integerPivotCell G).filter (fun n => ¬ Nat.Coprime n q)).card ≤ 8 := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
  have he : Real.exp (G+1) ≤ Real.exp 2*(q:ℝ) := by
    calc
      _ ≤ Real.exp (Real.log q+2) := Real.exp_le_exp.mpr (by
        have hh := (abs_le.mp hlog).1
        linarith)
      _ = _ := by rw [Real.exp_add,Real.exp_log hqR]; ring
  have hb : Real.exp (G+1) ≤ (8*q:ℕ) := by
    push_cast
    exact he.trans (mul_le_mul_of_nonneg_right exp_two_lt_eight.le hqR.le)
  have hc : ⌈Real.exp (G+1)⌉₊ ≤ 8*q := Nat.ceil_le.mpr hb
  have hcop (n : ℕ) : (¬ Nat.Coprime n q) ↔ q ∣ n := by
    rw [Nat.coprime_comm,hq.coprime_iff_not_dvd,not_not]
  simp only [integerPivotCell,hcop]
  rw [Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hc)

theorem externalPivotWeight_le (G : ℝ) (n : ℕ) :
    externalPivotWeight G n ≤ Real.exp (-G) := by
  exact (mul_le_mul_of_nonneg_left (Ostmann.smoothPartition_le_one _)
    (Real.exp_pos _).le).trans_eq (mul_one _)

theorem integerPivotCell_collision_mass_le (G : ℝ) (q : ℕ) (hq : Nat.Prime q)
    (hlog : |Real.log q-G| ≤ 1) :
    (∑ n ∈ integerPivotCell G,
      if ¬ Nat.Coprime n q then externalPivotWeight G n else 0) ≤ 8*Real.exp (-G) := by
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _n ∈ (integerPivotCell G).filter (fun n => ¬ Nat.Coprime n q), Real.exp (-G) :=
      Finset.sum_le_sum fun n _ => externalPivotWeight_le G n
    _ = (((integerPivotCell G).filter (fun n => ¬ Nat.Coprime n q)).card : ℝ)*
        Real.exp (-G) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast integerPivotCell_collision_card_le G q hq hlog) (Real.exp_pos _).le

theorem integerPivotCell_guard_error (G : ℝ) (q : ℕ) (hq : Nat.Prime q)
    (hlog : |Real.log q-G| ≤ 1) (f g : ℕ → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (heq : ∀ n ∈ integerPivotCell G, Nat.Coprime n q → f n=g n)
    (hbound : ∀ n ∈ integerPivotCell G, ¬ Nat.Coprime n q → ‖f n-g n‖ ≤ A) :
    ‖(∑ n ∈ integerPivotCell G,(externalPivotWeight G n:ℂ)*f n)-
      ∑ n ∈ integerPivotCell G,(externalPivotWeight G n:ℂ)*g n‖ ≤
      A*(8*Real.exp (-G)) := by
  exact (weighted_error_of_agree_off (integerPivotCell G) (externalPivotWeight G)
    (fun n => ¬ Nat.Coprime n q) f g A (fun n _ => externalPivotWeight_nonneg G n)
    (fun n hn hc => heq n hn (not_not.mp hc)) hbound).trans
      (mul_le_mul_of_nonneg_left (integerPivotCell_collision_mass_le G q hq hlog) hA)

theorem cellSupport_subset_integerPivotCell (N : ℕ) (lo hi G : ℝ) (hhi : hi ≤ G+1) :
    IntegerCell.cellSupport N lo hi ⊆ integerPivotCell G := by
  intro n hn
  have hh := (Finset.mem_filter.mp hn).2
  apply Finset.mem_Ioc.mpr
  refine ⟨hh.1,?_⟩
  have hnR : (0:ℝ)<n := by exact_mod_cast hh.1
  have hb : (n:ℝ) ≤ Real.exp (G+1) := by
    calc
      _ = Real.exp (Real.log n) := (Real.exp_log hnR).symm
      _ ≤ _ := Real.exp_le_exp.mpr (hh.2.2.trans hhi)
  exact_mod_cast hb.trans (Nat.le_ceil _)

theorem cellSupport_collision_card_le (N : ℕ) (lo hi G : ℝ) (hhi : hi ≤ G+1)
    (q : ℕ) (hq : Nat.Prime q) (hlog : |Real.log q-G| ≤ 1) :
    ((IntegerCell.cellSupport N lo hi).filter (fun n => ¬ Nat.Coprime n q)).card ≤ 8 :=
  (Finset.card_le_card (Finset.filter_subset_filter _
    (cellSupport_subset_integerPivotCell N lo hi G hhi))).trans
      (integerPivotCell_collision_card_le G q hq hlog)

theorem cellSupport_collision_mass_le (N : ℕ) (lo hi G : ℝ) (hhi : hi ≤ G+1)
    (q : ℕ) (hq : Nat.Prime q) (hlog : |Real.log q-G| ≤ 1) :
    (∑ n ∈ IntegerCell.cellSupport N lo hi,
      if ¬ Nat.Coprime n q then externalPivotWeight G n else 0) ≤ 8*Real.exp (-G) := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg
    (cellSupport_subset_integerPivotCell N lo hi G hhi) ?_).trans
      (integerPivotCell_collision_mass_le G q hq hlog)
  intro n _ _
  split_ifs <;> first | exact externalPivotWeight_nonneg G n | exact le_rfl

end Ostmann.Arithmetic.GiantCollisionError

end

end OAI
