import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftConvolution
import OAI.NumberTheory.TwoPoint.Bounds.FourierRegionBound

namespace OAI

/-! Concrete Parseval and short-sum bounds for the two window polynomials. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical ComplexConjugate

lemma integral_fourierPolynomial_sq_injective {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (hinj : Set.InjOn frequency S) :
    (∫ θ, ‖fourierPolynomial S frequency coefficient θ‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ i ∈ S, ‖coefficient i‖ ^ 2 := by
  rw [integral_norm_fourierPolynomial_sq, sum_product]
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single i]
  · simp only [ite_true, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  · intro j hj hji
    have hf : frequency i ≠ frequency j := fun he => hji (hinj hi hj he).symm
    exact ite_eq_right hf
  · exact fun hnot => False.elim (hnot hi)

lemma integral_fourierPolynomial_sq_le_card {ι : Type*} (S : Finset ι)
    (frequency : ι → ℤ) (coefficient : ι → ℂ) (hinj : Set.InjOn frequency S)
    (hbound : ∀ i ∈ S, ‖coefficient i‖ ≤ 1) :
    (∫ θ, ‖fourierPolynomial S frequency coefficient θ‖ ^ 2
      ∂AddCircle.haarAddCircle) ≤ S.card := by
  rw [integral_fourierPolynomial_sq_injective S frequency coefficient hinj]
  calc
    _ ≤ ∑ _i ∈ S, (1 : ℝ) := by
      apply sum_le_sum
      intro i hi
      have hh := hbound i hi
      have hn := norm_nonneg (coefficient i)
      nlinarith
    _ = _ := by simp

lemma continuous_forwardWindowPolynomial (f : ℕ → ℂ) (D v : ℕ) :
    Continuous (forwardWindowPolynomial f D v) := continuous_fourierPolynomial _ _ _

lemma continuous_backwardWindowPolynomial (g : ℕ → ℂ) (Q v : ℕ) :
    Continuous (backwardWindowPolynomial g Q v) := continuous_fourierPolynomial _ _ _

lemma norm_forwardWindowPolynomial_le (f : ℕ → ℂ) (hf : OneBounded f) (D v : ℕ)
    (θ : AddCircle (1 : ℝ)) : ‖forwardWindowPolynomial f D v θ‖ ≤ D := by
  apply (norm_fourierPolynomial_le _ _ _ θ).trans
  calc
    _ ≤ ∑ _m ∈ Icc 1 D, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      have hm1 := (mem_Icc.mp hm).1
      exact hf _ (by omega)
    _ = _ := by simp

lemma norm_backwardWindowPolynomial_le (g : ℕ → ℂ) (hg : OneBounded g) (Q v : ℕ)
    (θ : AddCircle (1 : ℝ)) : ‖backwardWindowPolynomial g Q v θ‖ ≤ Q := by
  apply (norm_fourierPolynomial_le _ _ _ θ).trans
  calc
    _ ≤ ∑ _a ∈ Icc 1 Q, (1 : ℝ) := by
      apply sum_le_sum
      intro a ha
      have ha1 := (mem_Icc.mp ha).1
      exact hg _ (by omega)
    _ = _ := by simp

lemma integral_forwardWindowPolynomial_sq_le (f : ℕ → ℂ) (hf : OneBounded f)
    (D v : ℕ) :
    (∫ θ, ‖forwardWindowPolynomial f D v θ‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D := by
  have hi : Set.InjOn (fun m : ℕ => (m : ℤ)) (Icc 1 D) := by
    intro a _ b _ he
    change (a : ℤ) = (b : ℤ) at he
    exact_mod_cast he
  have hb : ∀ m ∈ Icc 1 D, ‖f (v + m)‖ ≤ 1 := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    exact hf _ (by omega)
  simpa only [forwardWindowPolynomial, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.cast_id] using integral_fourierPolynomial_sq_le_card (Icc 1 D)
      (fun m : ℕ => (m : ℤ)) (fun m => f (v + m)) hi hb

lemma integral_backwardWindowPolynomial_sq_le (g : ℕ → ℂ) (hg : OneBounded g)
    (Q v : ℕ) :
    (∫ θ, ‖backwardWindowPolynomial g Q v θ‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ Q := by
  have hi : Set.InjOn (fun a : ℕ => -(a : ℤ)) (Icc 1 Q) := by
    intro a _ b _ he
    exact_mod_cast neg_injective he
  have hb : ∀ a ∈ Icc 1 Q, ‖g (v + a)‖ ≤ 1 := by
    intro a ha
    have ha1 := (mem_Icc.mp ha).1
    exact hg _ (by omega)
  simpa only [backwardWindowPolynomial, Nat.card_Icc, Nat.add_sub_cancel,
    Nat.cast_id] using integral_fourierPolynomial_sq_le_card (Icc 1 Q)
      (fun a : ℕ => -(a : ℤ)) (fun a => g (v + a)) hi hb

lemma fourier_nat_at_real (m : ℕ) (θ : ℝ) :
    fourier (m : ℤ) (θ : AddCircle (1 : ℝ)) = additiveCharacter θ m := by
  rw [fourier_coe_apply]
  unfold additiveCharacter
  congr 1
  push_cast
  ring

lemma forwardWindowPolynomial_at_real (f : ℕ → ℂ) (D v : ℕ) (θ : ℝ) :
    forwardWindowPolynomial f D v (θ : AddCircle (1 : ℝ)) = shortWindowSum f D θ v := by
  unfold forwardWindowPolynomial fourierPolynomial
  simp_rw [fourier_nat_at_real]
  simpa only [Nat.zero_add, Nat.add_assoc, shortWindowSum] using
    (sum_Icc_shift (fun m => f (v + m) * additiveCharacter θ m) 0 D)

/-- Applying a progression mask to the original values preserves their unit bound. -/
noncomputable def progressionSequence (f : ℕ → ℂ) (l : ℕ) [NeZero l]
    (a : ZMod l) (n : ℕ) : ℂ := if (n : ZMod l) = a then f n else 0

lemma OneBounded.progressionSequence {f : ℕ → ℂ} (hf : OneBounded f)
    (l : ℕ) [NeZero l] (a : ZMod l) : OneBounded (progressionSequence f l a) := by
  intro n hn
  unfold TwoPointCorrelations.progressionSequence
  split_ifs
  · exact hf n hn
  · simp

/-- Every circle frequency is represented by a real frequency, and the
unimodular origin phase disappears before applying MRT. -/
theorem progression_window_sum_from_integral (f : ℕ → ℂ) (D Y l : ℕ)
    [NeZero l] (a : ZMod l) (K : ℝ)
    (hK : ∀ α, shortExponentialIntegral f (Y + 1) D α ≤ K)
    (θ : AddCircle (1 : ℝ)) :
    (∑ v ∈ range Y,
      ‖forwardWindowPolynomial (progressionSequence f l a) D (v + 1) θ‖) ≤ K := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective θ
  calc
    _ = ∑ v ∈ range Y, ‖∑ n ∈ Icc (v + 2) (v + 1 + D),
        if (n : ZMod l) = a then f n * additiveCharacter α n else 0‖ := by
      apply sum_congr rfl
      intro v _
      rw [forwardWindowPolynomial_at_real, ← norm_shortExponentialSum_eq_window,
        shortExponentialSum_at_nat]
      simp only [progressionSequence, ite_mul, zero_mul]
    _ ≤ K := progression_short_sum_from_integral f D Y l a α K hK

theorem MRTLiouvilleShortInput.progression_window_polynomials
    (hMRT : MRTLiouvilleShortInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y D l : ℕ), 10 ≤ D → D ≤ Y + 1 →
      ∀ [NeZero l] (a : ZMod l) (θ : AddCircle (1 : ℝ)),
        (∑ v ∈ range Y,
          ‖forwardWindowPolynomial (progressionSequence liouville l a) D (v + 1) θ‖) ≤
          C * (D : ℝ) * (Y + 1 : ℕ) * mrtShortError (Y + 1) D := by
  obtain ⟨C, hC, hbound⟩ := hMRT
  refine ⟨C, hC, ?_⟩
  intro Y D l hD hDY _ a θ
  exact progression_window_sum_from_integral liouville D Y l a _
    (fun α => hbound (Y + 1) D hD hDY α) θ

end TwoPointCorrelations

end OAI
