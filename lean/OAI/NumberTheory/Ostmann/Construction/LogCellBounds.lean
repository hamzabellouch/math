import Mathlib
import OAI.NumberTheory.Ostmann.Construction.LogCellDefs

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem logCellWeight_nonneg (c : ℝ) (p : ℕ) : 0≤logCellWeight c p :=
  div_nonneg (Ostmann.smoothPartition_nonneg _) (Nat.cast_nonneg _)

theorem logCellWeight_le_exp (c : ℝ) (p : ℕ) : logCellWeight c p≤Real.exp (1-c) := by
  by_cases hp : p=0
  · simp only [hp, logCellWeight, Nat.cast_zero, div_zero]
    exact (Real.exp_pos _).le
  by_cases hφ : Ostmann.smoothPartition (Real.log p-c)=0
  · simp only [logCellWeight, hφ, zero_div]
    exact (Real.exp_pos _).le
  have hsupport := Ostmann.smoothPartition_support_subset hφ
  have hpos : (0:ℝ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp
  calc
    logCellWeight c p ≤ 1/(p:ℝ) :=
      div_le_div_of_nonneg_right (Ostmann.smoothPartition_le_one _) hpos.le
    _ = Real.exp (-(Real.log p)) := by rw [Real.exp_neg, Real.exp_log hpos, one_div]
    _ ≤ Real.exp (1-c) := Real.exp_le_exp.mpr (by linarith [hsupport.1])

theorem logCellWeight_log_sandwich (c : ℝ) (p : ℕ) :
    (c-1)*logCellWeight c p ≤ Real.log p*logCellWeight c p ∧
      Real.log p*logCellWeight c p ≤ (c+1)*logCellWeight c p := by
  by_cases hφ : Ostmann.smoothPartition (Real.log p-c)=0
  · simp only [logCellWeight, hφ, zero_div, mul_zero, le_refl, and_self]
  have hsupport := Ostmann.smoothPartition_support_subset hφ
  exact ⟨mul_le_mul_of_nonneg_right (by linarith [hsupport.1]) (logCellWeight_nonneg c p),
    mul_le_mul_of_nonneg_right (by linarith [hsupport.2]) (logCellWeight_nonneg c p)⟩

theorem logCellMass_nonneg (c : ℝ) (E : Finset ℕ) : 0≤logCellMass c E :=
  Finset.sum_nonneg (fun p _ => logCellWeight_nonneg c p)

theorem logCellLogMass_nonneg (c : ℝ) (E : Finset ℕ) : 0≤logCellLogMass c E :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (Real.log_natCast_nonneg p) (logCellWeight_nonneg c p))

theorem logCellMass_log_sandwich (c : ℝ) (E : Finset ℕ) :
    (c-1)*logCellMass c E ≤ logCellLogMass c E ∧
      logCellLogMass c E ≤ (c+1)*logCellMass c E := by
  constructor
  · simpa only [logCellMass, logCellLogMass, Finset.mul_sum] using
      Finset.sum_le_sum (s := logCellPrimes c \ E)
        (fun p _ => (logCellWeight_log_sandwich c p).1)
  · simpa only [logCellMass, logCellLogMass, Finset.mul_sum] using
      Finset.sum_le_sum (s := logCellPrimes c \ E)
        (fun p _ => (logCellWeight_log_sandwich c p).2)

theorem center_mul_logCellMass_sandwich {c : ℝ} (hc : 1<c) (E : Finset ℕ) :
    c/(c+1)*logCellLogMass c E ≤ c*logCellMass c E ∧
      c*logCellMass c E ≤ c/(c-1)*logCellLogMass c E := by
  obtain ⟨hlo,hhi⟩ := logCellMass_log_sandwich c E
  have hc0 : 0≤c := by linarith
  have hplus : 0<c+1 := by linarith
  have hminus : 0<c-1 := by linarith
  have h₁ : logCellLogMass c E/(c+1) ≤ logCellMass c E :=
    (div_le_iff₀ hplus).mpr (by simpa only [mul_comm] using hhi)
  have h₂ : logCellMass c E ≤ logCellLogMass c E/(c-1) :=
    (le_div_iff₀ hminus).mpr (by simpa only [mul_comm] using hlo)
  constructor
  · convert mul_le_mul_of_nonneg_left h₁ hc0 using 1; ring
  · convert mul_le_mul_of_nonneg_left h₂ hc0 using 1; ring

theorem finite_deletion_bound (s E : Finset ℕ) (f : ℕ → ℝ) {C : ℝ}
    (hC : 0≤C) (hf : ∀ p, 0≤f p) (hbound : ∀ p, f p≤C) :
    0≤(∑ p∈s, f p)-(∑ p∈s\E, f p) ∧
      (∑ p∈s, f p)-(∑ p∈s\E, f p)≤(E.card:ℝ)*C := by
  have heq := Finset.sum_sdiff (f := f) (Finset.inter_subset_left (s₁ := s) (s₂ := E))
  rw [Finset.sdiff_inter_self_left] at heq
  have hn : 0≤∑ p∈s∩E, f p := Finset.sum_nonneg (fun p _ => hf p)
  have hb : (∑ p∈s∩E, f p) ≤ (E.card:ℝ)*C := by
    calc
      _ ≤ ∑ _p∈s∩E, C := Finset.sum_le_sum (fun p _ => hbound p)
      _ = ((s∩E).card:ℝ)*C := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := E))) hC
  constructor <;> linarith

theorem logCellMass_delete_two (c : ℝ) (E : Finset ℕ) (hE : E.card≤2) :
    0≤logCellMass c ∅-logCellMass c E ∧
      logCellMass c ∅-logCellMass c E≤2*Real.exp (1-c) := by
  have h := finite_deletion_bound (logCellPrimes c) E (logCellWeight c)
    (Real.exp_pos (1-c)).le (logCellWeight_nonneg c) (logCellWeight_le_exp c)
  refine ⟨by simpa only [logCellMass, Finset.sdiff_empty] using h.1, ?_⟩
  calc
    _ ≤ (E.card:ℝ)*Real.exp (1-c) := by simpa only [logCellMass, Finset.sdiff_empty] using h.2
    _ ≤ 2*Real.exp (1-c) := mul_le_mul_of_nonneg_right (by exact_mod_cast hE) (Real.exp_pos _).le

theorem logCellLogMass_delete_two {c : ℝ} (hc : 0≤c) (E : Finset ℕ) (hE : E.card≤2) :
    0≤logCellLogMass c ∅-logCellLogMass c E ∧
      logCellLogMass c ∅-logCellLogMass c E≤2*(c+1)*Real.exp (1-c) := by
  have hp : 0≤c+1 := by linarith
  have hbound (p : ℕ) : Real.log p*logCellWeight c p≤(c+1)*Real.exp (1-c) :=
    (logCellWeight_log_sandwich c p).2.trans
      (mul_le_mul_of_nonneg_left (logCellWeight_le_exp c p) hp)
  have h := finite_deletion_bound (logCellPrimes c) E
    (fun p => Real.log p*logCellWeight c p) (mul_nonneg hp (Real.exp_pos _).le)
    (fun p => mul_nonneg (Real.log_natCast_nonneg p) (logCellWeight_nonneg c p)) hbound
  refine ⟨by simpa only [logCellLogMass, Finset.sdiff_empty] using h.1, ?_⟩
  calc
    _ ≤ (E.card:ℝ)*((c+1)*Real.exp (1-c)) := by
      simpa only [logCellLogMass, Finset.sdiff_empty] using h.2
    _ ≤ 2*((c+1)*Real.exp (1-c)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hE) (mul_nonneg hp (Real.exp_pos _).le)
    _ = _ := by ring

end Ostmann.Construction

end

end OAI
