import OAI.NumberTheory.TwoPoint.Bounds.CoprimeExceptionDensity
import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary

namespace OAI

/-! Extracting a fixed divisor from two ordinary multiplicative functions.
The failure of coprimality is counted explicitly, including its finite
interval boundary term. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def multiplicativeExtractionGap (f g : ℕ → ℂ) (u d n : ℕ) : ℂ :=
  f (u * n) * g (u * (n + d)) - f u * g u * f n * g (n + d)

lemma multiplicativeExtractionGap_eq_zero {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (u d n : ℕ) (hu : 0 < u) (hn : 0 < n)
    (hcop : u.Coprime (n * (n + d))) :
    multiplicativeExtractionGap f g u d n = 0 := by
  obtain ⟨h₁, h₂⟩ := Nat.coprime_mul_iff_right.mp hcop
  unfold multiplicativeExtractionGap
  rw [hfm u n hu hn h₁, hgm u (n + d) hu (by omega) h₂]
  ring

lemma norm_multiplicativeExtractionGap_le {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u d n : ℕ) (hu : 0 < u) (hn : 0 < n) :
    ‖multiplicativeExtractionGap f g u d n‖ ≤
      2 * (if ¬u.Coprime (n * (n + d)) then (1 : ℝ) else 0) := by
  by_cases hcop : u.Coprime (n * (n + d))
  · rw [multiplicativeExtractionGap_eq_zero hfm hgm u d n hu hn hcop]
    simp [hcop]
  · simp only [hcop, not_false_eq_true, ite_true, mul_one]
    have hn' : 0 < n + d := by omega
    have h₁ : ‖f (u * n) * g (u * (n + d))‖ ≤ 1 := by
      rw [norm_mul]
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul (hf _ (Nat.mul_pos hu hn))
          (hg _ (Nat.mul_pos hu hn')) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have h₂ : ‖f u * g u * f n * g (n + d)‖ ≤ 1 := by
      simp only [norm_mul]
      calc
        _ ≤ ((1 : ℝ) * 1) * 1 * 1 := by gcongr <;> first | exact hf _ hu | exact hg _ hu | exact hf _ hn | exact hg _ hn'
        _ = _ := by norm_num
    exact (norm_sub_le _ _).trans (by linarith)

theorem multiplicativeExtraction_sum_bound {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u d Y : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    ‖positivePrefix (multiplicativeExtractionGap f g u d) Y‖ ≤
      4 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card := by
  have hb : ‖positivePrefix (multiplicativeExtractionGap f g u d) Y‖ ≤
      2 * (coprimeExceptionCount u d Y : ℝ) := by
    unfold positivePrefix
    calc
      _ ≤ ∑ v ∈ range Y, ‖multiplicativeExtractionGap f g u d (v + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ range Y,
          2 * (if ¬u.Coprime ((v + 1) * (v + 1 + d)) then (1 : ℝ) else 0) := by
        apply sum_le_sum
        intro v _
        exact norm_multiplicativeExtractionGap_le hfm hgm hf hg u d (v + 1) hu (by omega)
      _ = _ := by simp [coprimeExceptionCount, mul_sum]
  have hc := coprimeExceptionCount_bound u d Y P hP hcover
  nlinarith only [hb, hc]

/-- Bounded cutoffs and progression indicators may be inserted before
the absolute value; their dependence on the integer is unrestricted. -/
theorem weightedMultiplicativeExtraction_sum_bound {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u d Y : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P)
    (q : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hq : ∀ n, 0 < n → ‖q n‖ ≤ K) :
    ‖positivePrefix (fun n => q n * multiplicativeExtractionGap f g u d n) Y‖ ≤
      K * (4 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card) := by
  have hb : ‖positivePrefix (fun n => q n * multiplicativeExtractionGap f g u d n) Y‖ ≤
      (K * 2) * (coprimeExceptionCount u d Y : ℝ) := by
    unfold positivePrefix
    calc
      _ ≤ ∑ v ∈ range Y, ‖q (v + 1) * multiplicativeExtractionGap f g u d (v + 1)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ v ∈ range Y,
          K * (2 * (if ¬u.Coprime ((v + 1) * (v + 1 + d)) then (1 : ℝ) else 0)) := by
        apply sum_le_sum
        intro v _
        rw [norm_mul]
        exact mul_le_mul (hq (v + 1) (by omega))
          (norm_multiplicativeExtractionGap_le hfm hgm hf hg u d (v + 1) hu (by omega))
          (norm_nonneg _) hK
      _ = _ := by simp [coprimeExceptionCount, mul_sum]
  have hc := mul_le_mul_of_nonneg_left (coprimeExceptionCount_bound u d Y P hP hcover) (by positivity : 0 ≤ K * 2)
  nlinarith only [hb, hc]

/-- Arbitrary finite shift families retain only their coefficient mass;
the exceptional-residue bound is uniform in the chosen shifts. -/
theorem finiteShift_extraction_sum_bound {ι : Type*} {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u Y : ℕ) (hu : 0 < u) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P)
    (S : Finset ι) (a : ι → ℂ) (d : ι → ℕ) (q : ι → ℕ → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (hq : ∀ i ∈ S, ∀ n, 0 < n → ‖q i n‖ ≤ K) :
    ‖∑ i ∈ S, a i * positivePrefix (fun n => q i n * multiplicativeExtractionGap f g u (d i) n) Y‖ ≤
      (∑ i ∈ S, ‖a i‖) *
        (K * (4 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card)) := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i * positivePrefix
        (fun n => q i n * multiplicativeExtractionGap f g u (d i) n) Y‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, ‖a i‖ *
        (K * (4 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card)) := by
      apply sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (weightedMultiplicativeExtraction_sum_bound hfm hgm hf hg u (d i) Y hu P hP hcover
          (q i) K hK (hq i hi)) (norm_nonneg _)
    _ = _ := (sum_mul _ _ _).symm

theorem multiplicativeExtraction_average_bound {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u d Y : ℕ) (hu : 0 < u) (hY : 0 < Y) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P) :
    ‖positivePrefix (multiplicativeExtractionGap f g u d) Y / (Y : ℂ)‖ ≤
      4 * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card / (Y : ℝ) := by
  have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hY').mpr
  calc
    _ ≤ 4 * (Y : ℝ) * (∑ p ∈ P, 1 / (p : ℝ)) + 4 * P.card :=
      multiplicativeExtraction_sum_bound hfm hgm hf hg u d Y hu P hP hcover
    _ = _ := by field_simp

lemma primeReciprocalSum_le_card_div (P : Finset ℕ) (P₀ : ℝ) (hP₀ : 0 < P₀)
    (hlarge : ∀ p ∈ P, P₀ ≤ (p : ℝ)) :
    (∑ p ∈ P, 1 / (p : ℝ)) ≤ P.card / P₀ := by
  calc
    _ ≤ ∑ _p ∈ P, 1 / P₀ := by
      apply sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hP₀ (hlarge p hp)
    _ = _ := by simp [div_eq_mul_inv]

theorem multiplicativeExtraction_rough_bound {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g)
    (u d Y : ℕ) (hu : 0 < u) (hY : 0 < Y) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcover : ∀ p, Nat.Prime p → p ∣ u → p ∈ P)
    (P₀ : ℝ) (hP₀ : 0 < P₀) (hlarge : ∀ p ∈ P, P₀ ≤ (p : ℝ)) :
    ‖positivePrefix (multiplicativeExtractionGap f g u d) Y / (Y : ℂ)‖ ≤
      4 * (P.card : ℝ) / P₀ + 4 * P.card / (Y : ℝ) := by
  have hb := multiplicativeExtraction_average_bound hfm hgm hf hg u d Y hu hY P hP hcover
  have hs := primeReciprocalSum_le_card_div P P₀ hP₀ hlarge
  calc
    _ ≤ 4 * ((P.card : ℝ) / P₀) + 4 * P.card / (Y : ℝ) :=
      hb.trans (add_le_add
        (mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 4 by norm_num))
        (le_refl (4 * P.card / (Y : ℝ))))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
