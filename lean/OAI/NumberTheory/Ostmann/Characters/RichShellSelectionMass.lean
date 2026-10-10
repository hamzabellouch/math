import OAI.NumberTheory.Ostmann.Construction.LogLogPrimeBandSupport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Construction

def harmonicIntervalMass (E : Finset ℕ) (a b : ℝ) : ℝ :=
  harmonicPrimeMass (E.filter (fun p : ℕ => a < Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ b))

lemma harmonicIntervalMass_nonneg (E : Finset ℕ) (a b : ℝ) :
    0 ≤ harmonicIntervalMass E a b :=
  Finset.sum_nonneg (fun _p _ => div_nonneg zero_le_one (Nat.cast_nonneg _))

lemma harmonicIntervalMass_mono (E : Finset ℕ) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    harmonicIntervalMass E a b ≤ harmonicIntervalMass E c d := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp,lt_of_le_of_lt hca hlo,hhi.trans hbd⟩
  · intro p _ _
    exact div_nonneg zero_le_one (Nat.cast_nonneg _)

@[simp] lemma harmonicIntervalMass_self (E : Finset ℕ) (a : ℝ) : harmonicIntervalMass E a a = 0 := by
  unfold harmonicIntervalMass harmonicPrimeMass
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hp
  exact False.elim ((not_lt_of_ge hhi) hlo)

lemma harmonicIntervalMass_add (E : Finset ℕ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    harmonicIntervalMass E a b + harmonicIntervalMass E b c = harmonicIntervalMass E a c := by
  simp only [harmonicIntervalMass,harmonicPrimeMass,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp_all <;> linarith

lemma harmonicIntervalMass_grid (E : Finset ℕ) (a w : ℝ) (hw : 0 ≤ w) (N : ℕ) :
    (∑ i ∈ Finset.range N, harmonicIntervalMass E (a + i*w) (a + (i+1)*w)) =
      harmonicIntervalMass E a (a + N*w) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    convert harmonicIntervalMass_add E (by nlinarith [mul_nonneg (Nat.cast_nonneg N) hw] : a ≤ a+(N:ℝ)*w)
      (by nlinarith : a+(N:ℝ)*w ≤ a+((N:ℝ)+1)*w) using 1;
      simp only [Nat.cast_add,Nat.cast_one]

lemma harmonicIntervalMass_eq_of_support (E : Finset ℕ) (a b : ℝ)
    (hE : ∀ p ∈ E, a < Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ b) :
    harmonicIntervalMass E a b = harmonicPrimeMass E := by
  unfold harmonicIntervalMass
  rw [Finset.filter_eq_self.mpr hE]

theorem harmonicIntervalMass_mertens : ∃ C : ℝ, 0 < C ∧
    ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) → ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      harmonicIntervalMass E a b ≤ b-a+C := by
  obtain ⟨C,hC,hb⟩ := logLogPrimeBand_mass_error
  refine ⟨C,hC,?_⟩
  intro E hE a b ha hab
  have hs : E.filter (fun p : ℕ => a < Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ b) ⊆
      logLogPrimeBand a b := by
    intro p hp
    obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
    exact (logLogPrimeBand_mem_iff a b p).mpr ⟨hE p hp,hlo,hhi⟩
  have hm : harmonicIntervalMass E a b ≤ harmonicPrimeMass (logLogPrimeBand a b) :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
  have hh := (abs_le.mp (hb a b ha hab ∅ (by simp))).2
  simp only [Finset.sdiff_empty] at hh
  linarith

end Ostmann.Characters

end

end OAI
