import OAI.NumberTheory.TwoPoint.Fourier.MinorArcOriginGeometry

namespace OAI

/-! Exact finite cofactor intervals for discrete short-sum origins. -/

namespace TwoPointCorrelations

open Finset

/-- The upper cofactor cutoff is exclusive. -/
def minorArcWindowInterval (M A k H : ℕ) : Finset ℕ :=
  Ico (k / A + 1) (min M ((k + H) / A + 1))

lemma mem_minorArcWindowInterval (M A k H m : ℕ) (hA : 0 < A) :
    m ∈ minorArcWindowInterval M A k H ↔
      m < M ∧ k < A * m ∧ A * m ≤ k + H := by
  unfold minorArcWindowInterval
  rw [mem_Ico, lt_min_iff]
  have hlow : k / A < m ↔ k < A * m := by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hA : k / A < m ↔ k < m * A)
  have hhigh : m ≤ (k + H) / A ↔ A * m ≤ k + H := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hA : m ≤ (k + H) / A ↔ m * A ≤ k + H)
  omega

lemma minor_arc_interval_length (A k H a b : ℕ) (hA : 0 < A)
    (hwindow : ∀ m ∈ Ico a b, k < A * m ∧ A * m ≤ k + H) :
    ((b - a : ℕ) : ℝ) ≤ (H : ℝ) / A + 1 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  by_cases hab : a < b
  · have ha := (hwindow a (mem_Ico.mpr ⟨le_rfl, hab⟩)).1
    have hb := (hwindow (b - 1) (mem_Ico.mpr ⟨by omega, by omega⟩)).2
    have haR : (k : ℝ) < (A : ℝ) * a := by exact_mod_cast ha
    have hbR : (A : ℝ) * (b - 1 : ℕ) ≤ (k : ℝ) + H := by exact_mod_cast hb
    rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one] at hbR
    rw [Nat.cast_sub (by omega : a ≤ b)]
    rw [show (H : ℝ) / A + 1 = ((H : ℝ) + A) / A by field_simp [hA0.ne']]
    apply (le_div_iff₀ hA0).mpr
    nlinarith
  · rw [Nat.sub_eq_zero_of_le (by omega : b ≤ a), Nat.cast_zero]
    positivity

lemma minor_arc_geometric_mono {L V : ℝ} (h : L ≤ V) (α : ℝ) :
    minorArcGeometricBound L α ≤ minorArcGeometricBound V α := by
  unfold minorArcGeometricBound
  split_ifs
  · exact h
  · exact min_le_min h le_rfl

lemma minor_arc_geometric_window (A k H a b : ℕ) (hA : 0 < A)
    (hwindow : ∀ m ∈ Ico a b, k < A * m ∧ A * m ≤ k + H) (α : ℝ) :
    ‖∑ m ∈ Ico a b, additiveCharacter α m‖ ≤
      minorArcGeometricBound ((H : ℝ) / A + 1) α :=
  (minor_arc_geometric_bound α a b).trans
    (minor_arc_geometric_mono (minor_arc_interval_length A k H a b hA hwindow) α)

/-- The intersection of four origin windows is again one interval; its
length is controlled by the first prime, regardless of the other origins. -/
lemma minor_arc_four_window_kernel (M A B C D k l r s H : ℕ)
    (hA : 0 < A) (α : ℝ) :
    ‖∑ m ∈ (minorArcWindowInterval M A k H ∩ minorArcWindowInterval M B l H) ∩
        (minorArcWindowInterval M C r H ∩ minorArcWindowInterval M D s H),
      additiveCharacter α m‖ ≤ minorArcGeometricBound ((H : ℝ) / A + 1) α := by
  unfold minorArcWindowInterval
  rw [Ico_inter_Ico, Ico_inter_Ico, Ico_inter_Ico]
  apply minor_arc_geometric_window A k H _ _ hA
  intro m hm
  have hm' := mem_Ico.mp hm
  have hlow : k / A + 1 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm'.1
  have hhigh : m < (k + H) / A + 1 :=
    lt_of_lt_of_le hm'.2 (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hmlow : k < A * m := by
    have hh : k / A < m := by omega
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hA).mp hh
  have hmhigh : A * m ≤ k + H := by
    have hh : m ≤ (k + H) / A := by omega
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hA).mp hh
  exact ⟨hmlow, hmhigh⟩

end TwoPointCorrelations

end OAI
