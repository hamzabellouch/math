import OAI.GroupTheory.PolycyclicRecognition.Analysis.QuantitativeInjectiveCover
import OAI.GroupTheory.PolycyclicRecognition.Analysis.InjectivePatchVolume

namespace OAI

/-! # Quantitative compact image volume away from the critical set -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_compact_image_volume_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∀ K : Set (Fin n → ℝ), IsCompact K →
      (∀ z ∈ K, ‖z‖ ≤ R ∧ η ≤ |(df z).det|) →
      let ρ := min 1 (η / (8 * (C * L ^ (n - 1)) * L))
      IsCompact (f '' K) ∧
        η * (volume K).toReal ≤ (2 * R / ρ + 2) ^ n * (volume (f '' K)).toReal := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_quantitative_injective_cover n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc K hK hgood
  obtain ⟨ρ, k, c, hρeq, hρ, hk, hcov, hinj⟩ := hcover f df R L η hR hL hη hf hdf hosc
  have hcont : ContinuousOn f K := fun z hz =>
    (hf z (by have := (hgood z hz).1; linarith)).continuousAt.continuousWithinAt
  have himage : IsCompact (f '' K) := hK.image_of_continuousOn hcont
  have hinjK (i : Fin n → Fin k) : Set.InjOn f (K ∩ closedBall (c i) ρ) := by
    intro z hz w hw he
    exact hinj i ⟨hgood z hz.1, hz.2⟩ ⟨hgood w hw.1, hw.2⟩ he
  have hb := volume_image_lower_of_finite_injective_cover volume f df hK.measurableSet
    (Finset.univ : Finset (Fin n → Fin k)) (fun i => closedBall (c i) ρ)
    (fun _ _ => measurableSet_closedBall) (fun z hz => by
      obtain ⟨i, hi⟩ := hcov z (hgood z hz).1
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_univ _, hi⟩)
    (fun z hz => hf z (by have := (hgood z hz).1; linarith))
    (fun i _ => hinjK i)
    (Real.toNNReal η) (fun z hz => by simpa [Real.coe_toNNReal η hη.le] using (hgood z hz).2)
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) himage.measure_ne_top) hb
  have hr : η * (volume K).toReal ≤ (k : ℝ) ^ n * (volume (f '' K)).toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal η hη.le,
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, Nat.cast_pow] using ht
  have hpow : (k : ℝ) ^ n ≤ (2 * R / ρ + 2) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg k) hk n
  subst ρ
  exact ⟨himage, hr.trans (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg)⟩

end PolycyclicRecognition

end

end OAI
