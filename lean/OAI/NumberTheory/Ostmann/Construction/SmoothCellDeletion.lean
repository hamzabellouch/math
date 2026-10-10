import OAI.NumberTheory.Ostmann.Construction.SmoothGiantMassEstimate

namespace OAI

/-! # The nongiant smooth cell prior with the prescribed finite deletions -/

namespace Ostmann
open scoped Classical BigOperators

theorem smoothCell_atom_le (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, φ x ≤ 1) (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) :
    φ (Real.log p - G) / p ≤ Real.exp (1 - G) := by
  by_cases hp : p = 0
  · simp only [hp, Nat.cast_zero, div_zero]
    exact (Real.exp_pos _).le
  by_cases hz : φ (Real.log p - G) = 0
  · rw [hz, zero_div]
    exact (Real.exp_pos _).le
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
  have hs : |Real.log p - G| < 1 := by
    by_contra hn
    exact hz (hout _ (le_of_not_gt hn))
  have hlog : G - 1 ≤ Real.log p := by have := (abs_lt.mp hs).1; linarith
  have hexp : Real.exp (G - 1) ≤ (p : ℝ) := by
    simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr hlog
  calc
    _ ≤ 1 / (p : ℝ) := div_le_div_of_nonneg_right (hφ _) hp0.le
    _ ≤ (Real.exp (G - 1))⁻¹ := by simpa only [one_div] using inv_anti₀ (Real.exp_pos _) hexp
    _ = _ := by rw [← Real.exp_neg]; congr 1; ring

/-- Deleting a fixed finite set loses at most its cardinality times the
largest reciprocal prime in the cell, including boundary zero weights. -/
theorem smoothCell_deletion_loss (P E : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, φ x ≤ 1) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    smoothGiantMass P φ G - (E.card : ℝ) * Real.exp (1 - G) ≤
      smoothGiantMass (P \ E) φ G := by
  have he : (P \ E) ∪ (P ∩ E) = P := by ext p; simp; tauto
  have hd : Disjoint (P \ E) (P ∩ E) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_inter.mp hq).2
  have hsum := Finset.sum_union hd (f := fun p : ℕ => φ (Real.log p - G) / p)
  rw [he] at hsum
  have hbound : (∑ p ∈ P ∩ E, φ (Real.log p - G) / p) ≤
      (E.card : ℝ) * Real.exp (1 - G) := by
    calc
      _ ≤ ∑ _p ∈ P ∩ E, Real.exp (1 - G) :=
        Finset.sum_le_sum (fun p _ => smoothCell_atom_le φ G hφ hout p)
      _ = ((P ∩ E).card : ℝ) * Real.exp (1 - G) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
        (Finset.card_le_card Finset.inter_subset_right)) (Real.exp_nonneg _)
  unfold smoothGiantMass
  linarith

noncomputable def deletedSmoothCellPrior (P E : Finset ℕ) (φ : ℝ → ℝ)
    (G : ℝ) (p : P) : ℝ :=
  if (p : ℕ) ∈ E then 0 else
    Real.exp (smoothGiantLogNormalizer (P \ E) φ G) * φ (Real.log p - G) / p

theorem deletedSmoothCellPrior_nonneg (P E : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, 0 ≤ φ x) (p : P) : 0 ≤ deletedSmoothCellPrior P E φ G p := by
  unfold deletedSmoothCellPrior
  split_ifs
  · rfl
  · exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (hφ _)) (Nat.cast_nonneg _)

theorem deletedSmoothCellPrior_mass (P E : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hmass : 0 < smoothGiantMass (P \ E) φ G) :
    ∑ p : P, deletedSmoothCellPrior P E φ G p = 1 := by
  have hfilter : P.filter (fun p => p ∉ E) = P \ E := by ext p; simp
  have hs : (∑ p : P, if (p : ℕ) ∈ E then 0 else φ (Real.log p - G) / p) =
      smoothGiantMass (P \ E) φ G := by
    have he := Finset.sum_coe_sort P (fun p : ℕ => if p ∈ E then 0 else φ (Real.log p - G) / p)
    rw [he]
    rw [← hfilter, smoothGiantMass, Finset.sum_filter]
    simp only [ite_not]
  have hfactor (p : P) : deletedSmoothCellPrior P E φ G p =
      Real.exp (smoothGiantLogNormalizer (P \ E) φ G) *
        (if (p : ℕ) ∈ E then 0 else φ (Real.log p - G) / p) := by
    unfold deletedSmoothCellPrior
    split_ifs <;> ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum, hs, smoothGiantLogNormalizer, Real.exp_neg, Real.exp_log hmass]
  exact inv_mul_cancel₀ hmass.ne'

/-- The cancellation estimate needed for repeated internal samples applies
to the exact smooth cell law, not just the hard harmonic prior. -/
theorem prime_mul_deletedSmoothCellPrior_le (P E : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (φ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ x, φ x ≤ 1) (p : P) :
    (p : ℝ) * deletedSmoothCellPrior P E φ G p ≤
      Real.exp (smoothGiantLogNormalizer (P \ E) φ G) := by
  unfold deletedSmoothCellPrior
  split_ifs
  · simp only [mul_zero]
    exact (Real.exp_pos _).le
  · have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p p.property).ne_zero
    have he : (p : ℝ) *
        (Real.exp (smoothGiantLogNormalizer (P \ E) φ G) * φ (Real.log p - G) / p) =
        Real.exp (smoothGiantLogNormalizer (P \ E) φ G) * φ (Real.log p - G) := by
      field_simp
    rw [he]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) (hφ _)

theorem deletedSmoothCellPrior_support (P E : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (p : P) (hp : deletedSmoothCellPrior P E φ G p ≠ 0) :
    (p : ℕ) ∉ E ∧ φ (Real.log p - G) ≠ 0 := by
  constructor
  · intro he
    exact hp (by simp only [deletedSmoothCellPrior, he, ite_true])
  · intro hz
    apply hp
    unfold deletedSmoothCellPrior
    split_ifs <;> simp only [hz, mul_zero, zero_div]

theorem deletedSmoothCellPrior_log_lower (P E : Finset ℕ) (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : P)
    (hp : deletedSmoothCellPrior P E φ G p ≠ 0) : G - 1 ≤ Real.log p := by
  have hz := (deletedSmoothCellPrior_support P E φ G p hp).2
  have hs : |Real.log p - G| < 1 := by
    by_contra hn
    exact hz (hout _ (le_of_not_gt hn))
  have hh := (abs_lt.mp hs).1
  linarith

/-- The exact smooth law supplies the same small-atom scale required by
the repeated-prime and internal arithmetic bounds. -/
theorem deletedSmoothCellPrior_le_exp (P E : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (φ : ℝ → ℝ) (G H : ℝ)
    (hφ : ∀ x, φ x ≤ 1) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hH : smoothGiantLogNormalizer (P \ E) φ G ≤ H) (p : P) :
    deletedSmoothCellPrior P E φ G p ≤ Real.exp (H - (G - 1)) := by
  by_cases hz : deletedSmoothCellPrior P E φ G p = 0
  · rw [hz]
    exact (Real.exp_pos _).le
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (hP p p.property).pos
  have hlog := deletedSmoothCellPrior_log_lower P E φ G hout p hz
  have hsize : Real.exp (G - 1) ≤ (p : ℝ) := by
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr hlog
  have hinv : (p : ℝ)⁻¹ ≤ Real.exp (-(G - 1)) := by
    simpa only [Real.exp_neg] using inv_anti₀ (Real.exp_pos _) hsize
  calc
    _ ≤ Real.exp (smoothGiantLogNormalizer (P \ E) φ G) / (p : ℝ) := by
      apply (le_div_iff₀ hp).mpr
      simpa only [mul_comm] using prime_mul_deletedSmoothCellPrior_le P E hP φ G hφ p
    _ ≤ Real.exp H * Real.exp (-(G - 1)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (Real.exp_le_exp.mpr hH) hinv (inv_nonneg.mpr hp.le) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1

end Ostmann

end OAI
