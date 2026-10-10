import OAI.NumberTheory.Ostmann.Characters.CharacterWordBinSelection
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors
import OAI.NumberTheory.Ostmann.Construction.InitialWordCoordinates

namespace OAI

/-! # Supported top-first words retain their actual logarithmic bin -/
namespace Ostmann
open scoped Classical BigOperators

theorem top_first_word_log_bounds (m : ℕ) (ℓ : Fin (m + 1) → ℝ) (b τ : ℝ)
    (hbulk : ∀ i : Fin m, 0 ≤ ℓ i.succ ∧ ℓ i.succ ≤ b)
    (hsize : (m : ℝ) * b ≤ τ) (htop : τ ≤ ℓ 0 ∧ ℓ 0 ≤ 3 * τ) :
    τ ≤ ∑ i, ℓ i ∧ (∑ i, ℓ i) ≤ 4 * τ := by
  have h₀ : 0 ≤ ∑ i : Fin m, ℓ i.succ :=
    Finset.sum_nonneg (fun i _ => (hbulk i).1)
  have h₁ : (∑ i : Fin m, ℓ i.succ) ≤ (m : ℝ) * b := by
    calc
      _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum (fun i _ => (hbulk i).2)
      _ = _ := by simp
  rw [Fin.sum_univ_succ]
  constructor <;> linarith [htop.1, htop.2]

theorem binnedWordAverage_support {A B : Type*} [Fintype A] {n : ℕ}
    (μ : Fin n → A → ℝ) (F : Fin n → A → ℂ) (bin : (Fin n → A) → B) (b : B)
    (h : binnedWordAverage μ F bin b ≠ 0) :
    ∃ w, bin w = b ∧ productPrior μ w ≠ 0 := by
  by_contra! hnone
  apply h
  unfold binnedWordAverage
  apply Finset.sum_eq_zero
  intro w _
  by_cases hw : bin w = b
  · simp only [hw, ite_true, hnone w hw, Complex.ofReal_zero, zero_mul]
  · simp only [hw, ite_false]

theorem supported_character_word_bounds (m : ℕ) (P U T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hzero : Q 0 = T) (hsucc : ∀ i : Fin m, Q i.succ = U)
    (b τ : ℝ) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (w : Fin (m + 1) → P)
    (hw : productPrior (fun i => primeSubsetPrior P (Q i)) w ≠ 0) :
    τ ≤ ∑ i, Real.log (w i : ℝ) ∧ (∑ i, Real.log (w i : ℝ)) ≤ 4 * τ := by
  have hs (i : Fin (m + 1)) : (w i : ℕ) ∈ Q i := by
    apply primeSubsetPrior_support P (Q i) (w i)
    exact (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  apply top_first_word_log_bounds m _ b τ
  · intro i
    constructor
    · exact Real.log_nonneg (by exact_mod_cast (hP (w i.succ) (w i.succ).property).one_le)
    · apply hbulk
      simpa only [hsucc] using hs i.succ
  · exact hsize
  · apply htop
    simpa only [hzero] using hs 0

theorem supported_character_bin_bounds (m : ℕ) (P U T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hzero : Q 0 = T) (hsucc : ∀ i : Fin m, Q i.succ = U)
    (b τ : ℝ) (hτ : 2 ≤ τ) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (F : Fin (m + 1) → P → ℂ) (j : Fin (⌊4 * τ⌋₊ + 1))
    (hj : binnedWordAverage (fun i => primeSubsetPrior P (Q i)) F
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) j ≠ 0) :
    τ / 2 ≤ (j.val : ℝ) ∧ (j.val : ℝ) ≤ 4 * τ ∧ 0 < j.val := by
  obtain ⟨w, hwj, hw⟩ := binnedWordAverage_support _ _ _ _ hj
  have hs := supported_character_word_bounds m P U T Q hP hzero hsucc b τ hsize htop hbulk w hw
  have hjval : j.val = ⌊∑ i, Real.log (w i : ℝ)⌋₊ := by
    rw [← hwj]
    exact wordLogBin_val τ _ hs.2
  have hlo := Nat.lt_floor_add_one (∑ i, Real.log (w i : ℝ))
  have hhi := Nat.floor_le (show 0 ≤ ∑ i, Real.log (w i : ℝ) by linarith [hs.1])
  have hjlo : τ / 2 ≤ (j.val : ℝ) := by rw [hjval]; linarith [hs.1]
  refine ⟨hjlo, ?_, ?_⟩
  · rw [hjval]; exact hhi.trans hs.2
  · have : (0 : ℝ) < j.val := by linarith
    exact_mod_cast this

/-- Nonzero mass for the complete two-copy tuple forces nonzero mass for
both original word marginals. -/
theorem wordCopyPrior_word_support {A : Type*} (k nc : ℕ)
    (μ : Fin k → A → ℝ) (ν : Fin nc → A → ℝ)
    (y : Fin ((k + nc) + (k + nc)) → A)
    (hy : productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) y ≠ 0) :
    productPrior μ ((wordCopyEquiv A k nc).symm y).1.1 ≠ 0 ∧
      productPrior μ ((wordCopyEquiv A k nc).symm y).2.1 ≠ 0 := by
  have h := wordCopyPrior μ ν ((wordCopyEquiv A k nc).symm y)
  rw [Equiv.apply_symm_apply] at h
  rw [h] at hy
  change (productPrior μ _ * productPrior ν _) *
    (productPrior μ _ * productPrior ν _) ≠ 0 at hy
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).2).1⟩

theorem character_initial_word_support (m nc : ℕ) (P U T : Finset ℕ)
    (Q : Fin (m + 1) → Finset ℕ) (R : Fin nc → Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hzero : Q 0 = T)
    (hsucc : ∀ i : Fin m, Q i.succ = U)
    (b τ : ℝ) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (y : Fin (((m + 1) + nc) + ((m + 1) + nc)) → P)
    (hy : productPrior (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) y ≠ 0) :
    (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).1.1 i : ℝ)) ≤ 4 * τ ∧
    (∑ i, Real.log (((wordCopyEquiv P (m + 1) nc).symm y).2.1 i : ℝ)) ≤ 4 * τ := by
  have he : (fun i => primeSubsetPrior P
      (Fin.append (Fin.append Q R) (Fin.append Q R) i)) =
      Fin.append (Fin.append (fun i => primeSubsetPrior P (Q i))
        (fun i => primeSubsetPrior P (R i)))
        (Fin.append (fun i => primeSubsetPrior P (Q i)) (fun i => primeSubsetPrior P (R i))) := by
    change (primeSubsetPrior P ∘ Fin.append (Fin.append Q R) (Fin.append Q R)) = _
    rw [← map_fin_append, ← map_fin_append]
    rfl
  rw [he] at hy
  have hw := wordCopyPrior_word_support (m + 1) nc _ _ y hy
  exact ⟨(supported_character_word_bounds m P U T Q hP hzero hsucc b τ hsize htop hbulk _ hw.1).2,
    (supported_character_word_bounds m P U T Q hP hzero hsucc b τ hsize htop hbulk _ hw.2).2⟩

theorem character_select_supported_bin (m : ℕ) (L X A C δ b τ : ℝ)
    (hm : 1 ≤ m) (hLm : L ≤ m) (hX : 0 < X) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ : 2 ≤ τ)
    (P U T : Finset ℕ) (Q : Fin (m + 1) → Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hzero : Q 0 = T)
    (hsucc : ∀ i : Fin m, Q i.succ = U) (hsize : (m : ℝ) * b ≤ τ)
    (htop : ∀ p ∈ T, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ)
    (hbulk : ∀ p ∈ U, Real.log (p : ℝ) ≤ b)
    (E : Finset ℕ) (hE : Real.sqrt X * Real.exp (-A * m) ≤ E.card)
    (F : ℕ → Fin (m + 1) → P → ℂ)
    (hcount : (Fintype.card (Fin (⌊4 * τ⌋₊ + 1)) : ℝ) ≤ Real.exp (C * L))
    (hmean : ∀ x ∈ E, ∀ i, δ ≤ ‖∑ p : P, (primeSubsetPrior P (Q i) p : ℂ) * F x i p‖) :
    ∃ j : Fin (⌊4 * τ⌋₊ + 1), τ / 2 ≤ (j.val : ℝ) ∧
      (j.val : ℝ) ≤ 4 * τ ∧ 0 < j.val ∧
      ∃ S : Finset ℕ, S ⊆ E ∧ S.Nonempty ∧
        Real.sqrt X * Real.exp (-(A + C) * m) ≤ S.card ∧
        ∀ x ∈ S, Real.exp (-(C - 2 * Real.log δ) * m) ≤
          ‖binnedWordAverage (fun i => primeSubsetPrior P (Q i)) (F x)
            (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) j‖ := by
  obtain ⟨j, S, hSE, hSne, hScard, hword⟩ := character_word_bin_selection m L X A C δ
    hm hLm hX hC hδ hδ1 E hE (fun i => primeSubsetPrior P (Q i)) F
    (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) hcount hmean
  obtain ⟨x, hx⟩ := hSne
  have hn : binnedWordAverage (fun i => primeSubsetPrior P (Q i)) (F x)
      (fun w => wordLogBin τ (fun i => Real.log (w i : ℝ))) j ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos _).trans_le (hword x hx))
  obtain ⟨hjl, hju, hjpos⟩ := supported_character_bin_bounds m P U T Q hP hzero hsucc
    b τ hτ hsize htop hbulk (F x) j hn
  exact ⟨j, hjl, hju, hjpos, S, hSE, ⟨x, hx⟩, hScard, hword⟩

end Ostmann

end OAI
