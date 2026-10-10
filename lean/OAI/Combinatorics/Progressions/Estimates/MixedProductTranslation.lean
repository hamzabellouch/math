import OAI.Combinatorics.Progressions.Probability.SpatialProductDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem scalarDensityConvolution_translation_l1 (f g : ℝ → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hf : Integrable f) (hg : Integrable g)
    (hg0 : ∀ x, 0 ≤ g x) (hgmass : (∫ x, g x) = 1) (D : ℝ)
    (hmove : ∀ a b, (∫ x, |f (x + a) - f (x + b)|) ≤ D * |a - b|) (a b : ℝ) :
    (∫ x, |scalarDensityConvolution f g (x + a) - scalarDensityConvolution f g (x + b)|) ≤
      D * |a - b| := by
  have hj (c : ℝ) : Integrable (Function.uncurry (fun t x => f (x + c - t) * g t))
      (volume.prod volume) := by
    have h := (scalarDensityConvolution_joint_integrable (fun x => f (x + c)) g
      (hfm.comp (measurable_id.add_const c)) hgm (hf.comp_add_right c) hg).swap
    change Integrable (fun p : ℝ × ℝ => f (p.2 - p.1 + c) * g p.1) (volume.prod volume) at h
    simp only [sub_add_eq_add_sub] at h
    exact h
  have h := densityMixture_l1_le volume volume _ _ (hj a) (hj b)
  simp only [Real.norm_eq_abs] at h
  apply h.trans
  have hd : Integrable (Function.uncurry
      (fun t x => f (x + a - t) * g t - f (x + b - t) * g t)) (volume.prod volume) :=
    (hj a).sub (hj b)
  have hp (t : ℝ) : (∫ x, ‖f (x + a - t) * g t - f (x + b - t) * g t‖) ≤
      g t * (D * |a - b|) := by
    simp only [← sub_mul, norm_mul, Real.norm_of_nonneg (hg0 t), Real.norm_eq_abs,
      integral_mul_const]
    have hm := hmove (a - t) (b - t)
    simp only [show a - t - (b - t) = a - b by ring] at hm
    simp only [← add_sub_assoc] at hm
    exact (mul_le_mul_of_nonneg_right hm (hg0 t)).trans_eq (mul_comm _ _)
  have hmono := integral_mono_ae hd.integral_norm_prod_left (hg.mul_const (D * |a - b|))
    (Filter.Eventually.of_forall hp)
  rw [integral_mul_const, hgmass, one_mul] at hmono
  exact hmono

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

theorem fourDensity_translation_l1 {A B C D : SlicedProductBlock ι}
    (hA : A.Admissible) (hB : B.Admissible) (hC : C.Admissible) (hD : D.Admissible)
    (a b : ℝ) :
    (∫ x, |fourDensity A B C D (x + a) - fourDensity A B C D (x + b)|) ≤
      2 * pairCap A B * |a - b| :=
  scalarDensityConvolution_translation_l1 _ _ (pairDensity_measurable A B)
    (pairDensity_measurable C D) (pairDensity_probability_density hA hB).2.1
    (pairDensity_probability_density hC hD).2.1 (pairDensity_probability_density hC hD).1
    (pairDensity_probability_density hC hD).2.2 _ (pairDensity_translation_l1 hA hB) a b

theorem mixedFourDensity_translation_l1 {P : Type*} [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ] (B : P → Fin 4 → SlicedProductBlock ι)
    (hm : ∀ j, MeasurableFamily (fun p => B p j)) {r : ℝ} (hr : 0 < r)
    (hgood : ∀ᵐ p ∂μ, (∀ j, (B p j).Admissible) ∧ (∀ j, r ≤ (B p j).volumeScale))
    (a b : ℝ) :
    (∫ x, |mixedFourDensity μ B (x + a) - mixedFourDensity μ B (x + b)|) ≤
      2 * (uniformCap ι r hr : ℝ) * |a - b| := by
  let F : P → ℝ → ℝ := fun p => fourDensity (B p 0) (B p 1) (B p 2) (B p 3)
  have hmeas := fourDensity_measurable_family (hm 0) (hm 1) (hm 2) (hm 3)
  have hprob := hgood.mono (fun p hp => fourDensity_probability_density
      (hp.1 0) (hp.1 1) (hp.1 2) (hp.1 3))
  have hmove : ∀ᵐ p ∂μ, ∀ a b, (∫ x, |F p (x + a) - F p (x + b)|) ≤
      2 * (uniformCap ι r hr : ℝ) * |a - b| := by
    filter_upwards [hgood] with p hp a b
    exact (fourDensity_translation_l1 (hp.1 0) (hp.1 1) (hp.1 2) (hp.1 3) a b).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pairCap_le_of_scale_lower hr (hp.2 0) (hp.2 1))
          (by norm_num)) (abs_nonneg _))
  exact densityMixture_translation_l1 μ F hmeas hprob _ hmove a b

variable {I : Type*} [Fintype I] [DecidableEq I] {P J : I → Type*}
  [∀ i, MeasurableSpace (P i)] [∀ i, Fintype (J i)]

theorem jointMixedDensity_translation_l1 (μ : ∀ i, Measure (P i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B : ∀ i, P i → Fin 4 → SlicedProductBlock (J i))
    (hm : ∀ i j, MeasurableFamily (fun p => B i p j)) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (hgood : ∀ i, ∀ᵐ p ∂μ i, (∀ j, (B i p j).Admissible) ∧ (∀ j, r i ≤ (B i p j).volumeScale))
    (a b : I → ℝ) :
    (∫ x, |jointMixedDensity μ B (x + a) - jointMixedDensity μ B (x + b)|) ≤
      (∑ i, 2 * (uniformCap (J i) (r i) (hr i) : ℝ)) * dist a b := by
  have hs (i) := mixedFourDensity_spec (μ i) (B i) (hm i) (hr i) (hgood i)
  exact independentCoordinateDensity_translation_l1 _ (fun i => (hs i).2.2.1)
    (fun i x => ((hs i).1 x).1) (fun i => (hs i).2.2.2)
    (fun i => 2 * uniformCap (J i) (r i) (hr i))
    (fun i => mixedFourDensity_translation_l1 (μ i) (B i) (hm i) (hr i) (hgood i)) a b

theorem jointMixedDensity_imageTranslationBound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Ω → (I → ℝ)) (hU : Measurable U)
    (μ : ∀ i, Measure (P i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B : ∀ i, P i → Fin 4 → SlicedProductBlock (J i))
    (hm : ∀ i j, MeasurableFamily (fun p => B i p j)) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (hgood : ∀ i, ∀ᵐ p ∂μ i, (∀ j, (B i p j).Admissible) ∧ (∀ j, r i ≤ (B i p j).volumeScale))
    (hmap : Measure.map U ν = realDensityMeasure volume (jointMixedDensity μ B)) :
    ImageTranslationBound ν U (∑ i, 2 * uniformCap (J i) (r i) (hr i)) := by
  have hs := jointMixedDensity_spec μ B hm r hr hgood
  apply imageTranslationBound_of_density ν U hU _ hs.2.1.continuous.measurable
    hs.2.2.1 (fun x => (hs.1 x).1) hmap
  intro z
  have h := jointMixedDensity_translation_l1 μ B hm r hr hgood (-z) 0
  simp only [← sub_eq_add_neg, add_zero, dist_eq_norm, sub_zero, norm_neg] at h
  simp only [dist_eq_norm, sub_zero, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_ofNat]
  exact h

end Erdos3.SlicedProductBlock

end

end OAI
