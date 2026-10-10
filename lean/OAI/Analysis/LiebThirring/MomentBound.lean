import OAI.Analysis.LiebThirring.ComplexFamilies

namespace OAI


noncomputable section
namespace SharpLiebThirring
open MeasureTheory Set
open SobolevProof SobolevProof.C1L2 SpectralProof ConstantProof

lemma Admissible.locallyIntegrable {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) : LocallyIntegrable W volume := by
  apply hW.2.locallyIntegrable
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

lemma Admissible.integrable_rpow {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) :
    Integrable (fun x ↦ W x^(γ+1/2)) := by
  have hp : 0 < γ+1/2 := by linarith
  have hh := hW.2.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at hh
  apply hh.congr
  filter_upwards [hW.1] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg hx]

lemma Admissible.mass_eq_ofReal {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) :
    potentialMass γ W = ENNReal.ofReal (∫ x, W x^(γ+1/2)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hW.integrable_rpow hγ)]
  · apply lintegral_congr_ae
    filter_upwards [hW.1] with x hx
    exact ENNReal.ofReal_rpow_of_nonneg hx (by linarith)
  · filter_upwards [hW.1] with x hx
    exact Real.rpow_nonneg hx _

lemma Admissible.mass_ne_top {γ : ℝ} {W : ℝ → ℝ}
    (hW : Admissible γ W) (hγ : 1/2 < γ) : potentialMass γ W ≠ ⊤ := by
  rw [hW.mass_eq_ofReal hγ]
  exact ENNReal.ofReal_ne_top

lemma sharpConstant_pos {γ : ℝ} (hγ : 1/2 < γ) : 0 < sharpConstant γ := by
  have hσ : 0 < γ-1/2 := by linarith
  have he := action_constant_eq_sharp hσ
  rw [sub_add_cancel] at he
  rw [← he]
  apply div_pos _ (betaAction_pos hσ)
  unfold actionYoungConstant
  positivity

lemma finite_complex_eigenfamily_bound {N : ℕ} {γ : ℝ}
    (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) {W : ℝ → ℝ}
    (hW : Admissible γ W) (u : Fin N → H1) (k : Fin N → ℝ)
    (ho : IsOrthonormalFamily u) (he : ∀ i, IsNegativeEigenfunction W (k i) (u i)) :
    (∑ i, k i^(2*γ)) ≤ sharpConstant γ*∫ x, W x^(γ+1/2) := by
  have hWl := hW.locallyIntegrable hγ₀
  choose a ha har using (fun i ↦ eigen_C1_representative hWl (he i) Complex.reCLM)
  choose b hb hbi using (fun i ↦ eigen_C1_representative hWl (he i) Complex.imCLM)
  have hr (i j : Fin N) : inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0 := by
    have hh := congrArg Complex.re (ho i j)
    rw [re_l2Pairing (har i) (hbi i) (har j) (hbi j)] at hh
    simpa only [apply_ite,Complex.one_re,Complex.zero_re] using hh
  have hi (i j : Fin N) : inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0 := by
    have hh := congrArg Complex.im (ho i j)
    rw [im_l2Pairing (har i) (hbi i) (har j) (hbi j)] at hh
    simpa only [apply_ite,Complex.one_im,Complex.zero_im,ite_self] using hh
  obtain ⟨J,hJ,v,l,hvo,hve,hl,hs⟩ := realify_finite_family hWl k (fun i ↦ (he i).1) a b ha hb hr hi (2*γ)
  let := hJ
  exact hs.trans (real_family_bound hγ₀ hγ₁ hWl hW.1 (hW.integrable_rpow hγ₀) v l hvo hve hl)

/-- The full (unlimited-family-size) negative spectral moment estimate. -/
lemma negativeMoment_bound {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2)
    {W : ℝ → ℝ} (hW : Admissible γ W) :
    negativeMoment γ W ≤ ENNReal.ofReal (sharpConstant γ)*potentialMass γ W := by
  unfold negativeMoment
  refine iSup_le (fun N ↦ iSup_le (fun u ↦ iSup_le (fun k ↦ iSup_le (fun ho ↦ iSup_le (fun he ↦ ?_)))))
  have hh := ENNReal.ofReal_le_ofReal (finite_complex_eigenfamily_bound hγ₀ hγ₁ hW u k ho he)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ Real.rpow_nonneg (he i).1.le _),
    ENNReal.ofReal_mul (sharpConstant_pos hγ₀).le,← hW.mass_eq_ofReal hγ₀] at hh
  simpa only [ENNReal.ofReal_rpow_of_nonneg (he _).1.le (show 0 ≤ 2*γ by linarith)] using hh

end SharpLiebThirring

end

end OAI
