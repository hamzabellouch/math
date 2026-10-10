import OAI.NumberTheory.JointDickman.Amplification.IntegratedSampledError
import OAI.NumberTheory.JointDickman.Amplification.LogFrequencyBounds

namespace OAI

/-! # Integrability for exact finite-sum rearrangements of the histogram error -/

namespace JointDickman
open Finset MeasureTheory
open scoped SchwartzMap

theorem manuscriptFourier_frequency_continuous (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → ℝ → ℂ)
    (hF : ∀ x, Continuous (fun ξ => F ξ x)) (r : ZMod q) :
    Continuous (fun ξ => manuscriptFourier m B q J g (F ξ) r) := by
  classical
  unfold manuscriptFourier unitResidueFourier manuscriptCellSum
  apply continuous_finsetSum
  intro s _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro n _
  split_ifs
  · exact continuous_const.mul (hF _)
  · exact continuous_const

theorem sampledProjectedFourier_frequency_continuous (m B q : ℕ) [NeZero q]
    (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (F : ℝ → Fin (channelFineCount m B) → ℂ)
    (hF : ∀ i, Continuous (fun ξ => F ξ i)) (r : ZMod q) :
    Continuous (fun ξ => sampledProjectedFourier m B q J g (F ξ) r) := by
  simp_rw [sampledProjectedFourier_eq]
  apply continuous_const.mul
  unfold sampledProjectedValue
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (hF i)

theorem norm_le_sqrt_sum_sq {ι : Type*} [Fintype ι] (f : ι → ℂ) (i : ι)
    {C : ℝ} (hC : 0 ≤ C) (hs : ∑ j, ‖f j‖^2 ≤ C) : ‖f i‖ ≤ Real.sqrt C := by
  have hle : ‖f i‖^2 ≤ C :=
    (single_le_sum (fun j _ => sq_nonneg ‖f j‖) (mem_univ i)).trans hs
  nlinarith [Real.sq_sqrt hC,Real.sqrt_nonneg C,norm_nonneg (f i)]

theorem manuscriptFourier_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ∀ x ∈ Set.Icc (channelLower (channelFineCount m B) i)
      (channelUpper (channelFineCount m B) i), ‖F x‖ ≤ M) (r : ZMod q) :
    ‖manuscriptFourier m B q J g F r‖ ≤ Real.sqrt (manuscriptAmplitudeEnergy m B q J*M^2) := by
  apply norm_le_sqrt_sum_sq _ r (mul_nonneg (manuscriptAmplitudeEnergy_nonneg hm hB J) (sq_nonneg M))
  exact (manuscript_amplitude_fourier_bounds hm hB J g hg F hM hF).1.trans_eq
    (by unfold manuscriptAmplitudeEnergy; ring)

theorem sampledProjectedFourier_norm_le {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g : (auxiliaryPrimes B → Bool) → ℝ) (hg : ∀ x, |g x| ≤ 1)
    (F : Fin (channelFineCount m B) → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ i ∈ J, ‖F i‖ ≤ M) (r : ZMod q) :
    ‖sampledProjectedFourier m B q J g F r‖ ≤ Real.sqrt (manuscriptAmplitudeEnergy m B q J*M^2) :=
  norm_le_sqrt_sum_sq _ r (mul_nonneg (manuscriptAmplitudeEnergy_nonneg hm hB J) (sq_nonneg M))
    (sampledProjectedFourier_square_le hm hB J g hg F hM hF)

theorem schwartz_bounded_product_integrable (w : 𝓢(ℝ,ℝ)) (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) {M N : ℝ}
    (hM : ∀ ξ, ‖F ξ‖ ≤ M) (hN : ∀ ξ, ‖G ξ‖ ≤ N) (hMN : 0 ≤ M) :
    Integrable (fun ξ => testFourierTransform w ξ*(F ξ*G ξ)) :=
  (schwartz_testFourier_integrable w).mul_bdd (hF.mul hG).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul]
      exact mul_le_mul (hM ξ) (hN ξ) (norm_nonneg _) hMN))

theorem logOscillatoryTest_continuous_frequency (w : ℝ → ℝ) (B N β x : ℝ) :
    Continuous (fun ξ => logOscillatoryTest w B N (β*ξ) x) := by
  unfold logOscillatoryTest oscillatoryTest
  exact continuous_const.mul (continuous_additivePhase.comp
    ((continuous_const.mul continuous_id).mul continuous_const))

theorem logarithmic_histogram_integrals {m B q : ℕ} [NeZero q]
    (hm : 0 < m) (hB : 0 < B) (J : Finset (Fin (channelFineCount m B)))
    (g h : (auxiliaryPrimes B → Bool) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (w₁ w₂ : ℝ → ℝ) {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂)
    (N β : ℝ) (w : 𝓢(ℝ,ℝ)) (r : ZMod q) :
    let F := fun ξ => logOscillatoryTest w₁ B N (β*ξ)
    let G := fun ξ => logOscillatoryTest w₂ B N (-β*ξ)
    Integrable (fun ξ => testFourierTransform w ξ*
      (manuscriptFourier m B q J g (F ξ) r*manuscriptFourier m B q J h (G ξ) (-r))) ∧
    Integrable (fun ξ => testFourierTransform w ξ*
      (sampledProjectedFourier m B q J g (fun i => F ξ (channelLower (channelFineCount m B) i)) r*
        sampledProjectedFourier m B q J h (fun i => G ξ (channelLower (channelFineCount m B) i)) (-r))) := by
  dsimp only
  have hF (ξ x : ℝ) : ‖logOscillatoryTest w₁ B N (β*ξ) x‖ ≤ M₁ := by
    rw [logOscillatoryTest_norm]
    exact hw₁ _
  have hG (ξ x : ℝ) : ‖logOscillatoryTest w₂ B N (-β*ξ) x‖ ≤ M₂ := by
    rw [logOscillatoryTest_norm]
    exact hw₂ _
  constructor
  · refine schwartz_bounded_product_integrable
      (w := w) (M := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₁^2))
      (N := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₂^2)) _ _ ?_ ?_ ?_ ?_ ?_
    · exact manuscriptFourier_frequency_continuous m B q J g _
        (fun x => logOscillatoryTest_continuous_frequency _ _ _ _ x) _
    · exact manuscriptFourier_frequency_continuous m B q J h _
        (fun x => logOscillatoryTest_continuous_frequency _ _ _ _ x) _
    · intro ξ
      exact manuscriptFourier_norm_le hm hB J g hg _ hM₁ (fun _ _ x _ => hF ξ x) r
    · intro ξ
      exact manuscriptFourier_norm_le hm hB J h hh _ hM₂ (fun _ _ x _ => hG ξ x) (-r)
    · positivity
  · refine schwartz_bounded_product_integrable
      (w := w) (M := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₁^2))
      (N := Real.sqrt (manuscriptAmplitudeEnergy m B q J*M₂^2)) _ _ ?_ ?_ ?_ ?_ ?_
    · exact sampledProjectedFourier_frequency_continuous m B q J g _
        (fun i => logOscillatoryTest_continuous_frequency _ _ _ _ _) _
    · exact sampledProjectedFourier_frequency_continuous m B q J h _
        (fun i => logOscillatoryTest_continuous_frequency _ _ _ _ _) _
    · intro ξ
      exact sampledProjectedFourier_norm_le hm hB J g hg _ hM₁ (fun i _ => hF ξ _) r
    · intro ξ
      exact sampledProjectedFourier_norm_le hm hB J h hh _ hM₂ (fun i _ => hG ξ _) (-r)
    · positivity

end JointDickman

end OAI
