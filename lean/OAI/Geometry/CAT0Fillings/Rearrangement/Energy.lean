import Mathlib
import OAI.Geometry.CAT0Fillings.Rearrangement.Distribution
import OAI.Geometry.CAT0Fillings.Rearrangement.Substitution

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma map_antitone_derivative_measure {h : ℝ → ℝ} {K : ℝ≥0}
    (hh : LipschitzWith K h) {a b : ℝ} (hab : a ≤ b)
    (ha : AntitoneOn h (Icc a b)) :
    ((volume.restrict (Icc a b)).withDensity (fun r => ENNReal.ofReal (-deriv h r))).map h =
      volume.restrict (Icc (h b) (h a)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hh.continuous.measurable]
  have hd : Measurable (fun r : ℝ => ENNReal.ofReal (-deriv h r)) :=
    (measurable_deriv h).neg.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul (volume.restrict (Icc a b)) hd
    (show Measurable (fun r => g (h r)) from hg.comp hh.continuous.measurable)]
  exact (lintegral_antitone_interval hh hab ha g).symm

lemma inverse_energy_identity {R : ℝ → ℝ} {U c : ℝ}
    (hU : 0 < U) (hc : 0 < c) (hR : Antitone R)
    (hpos : ∀ t ∈ Ico 0 U, 0 < R t)
    (hD : ∀ s t : ℝ, 0 < s → s < t → t < U → c*(t-s) ≤ R s-R t)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    ∫⁻ r in Icc 0 (R 0), w r * (ENNReal.ofReal (-deriv (radialInverse R U) r))^2 =
      ∫⁻ t in Icc 0 U, w (R t) / ENNReal.ofReal (-deriv R t) := by
  let h := radialInverse R U
  let v := fun r => ENNReal.ofReal (-deriv h r)
  let ν := (volume.restrict (Icc 0 (R 0))).withDensity v
  have hh : LipschitzWith (c⁻¹).toNNReal h :=
    radialInverse_lipschitz hU.le hc (hR.antitoneOn _) hD
  have hvm : Measurable v := (measurable_deriv h).neg.ennreal_ofReal
  have hB : 0 ≤ R 0 := (hpos 0 ⟨le_rfl,hU⟩).le
  have h0 : h 0 = U := radialInverse_at_zero hU hpos
  have hB0 : h (R 0) = 0 := radialInverse_zero_outside hU.le (hR.antitoneOn _) le_rfl
  have hmap : ν.map h = volume.restrict (Icc 0 U) := by
    have he := map_antitone_derivative_measure hh hB
      ((radialInverse_antitone R U).antitoneOn _)
    rwa [h0,hB0] at he
  have hgood : ∀ᵐ t ∂volume.restrict (Icc 0 U),
      t ∈ Ioo 0 U ∧ HasDerivAt R (deriv R t) t ∧
      HasDerivAt h (deriv R t)⁻¹ (R t) ∧ deriv R t ≠ 0 := by
    have he : volume.restrict (Icc 0 U) = volume.restrict (Ioo 0 U) :=
      Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
    rw [he]
    filter_upwards [ae_inverse_derivative hU.le hc hR hD,
      ae_restrict_mem measurableSet_Ioo] with t ht hm
    exact ⟨hm,ht⟩
  have hpull : ∀ᵐ r ∂ν,
      h r ∈ Ioo 0 U ∧ HasDerivAt R (deriv R (h r)) (h r) ∧
      HasDerivAt h (deriv R (h r))⁻¹ (R (h r)) ∧ deriv R (h r) ≠ 0 := by
    have hg' := hgood
    rw [←hmap] at hg'
    exact ae_of_ae_map hh.continuous.measurable.aemeasurable hg'
  let g := fun t => w (R t) / ENNReal.ofReal (-deriv R t)
  have hgm : Measurable g := (hw.comp hR.measurable).div (measurable_deriv R).neg.ennreal_ofReal
  have heq : (fun r => w r*v r) =ᵐ[ν] (fun r => g (h r)) := by
    filter_upwards [hpull] with r hr
    have hfiber : r = R (h r) := radialInverse_fiber (hR.antitoneOn _)
      hr.1.1 hr.1.2 hr.2.1.continuousAt rfl
    have hd : deriv h r = (deriv R (h r))⁻¹ := by
      calc
        deriv h r = deriv h (R (h r)) := congrArg (deriv h) hfiber
        _ = _ := hr.2.2.1.deriv
    have hdneg : 0 < -deriv R (h r) :=
      neg_pos.mpr (lt_of_le_of_ne hR.deriv_nonpos hr.2.2.2)
    dsimp [g,v]
    rw [hd,←inv_neg,ENNReal.ofReal_inv_of_pos hdneg,div_eq_mul_inv]
    exact congrArg (fun z => w z * (ENNReal.ofReal (-deriv R (h r)))⁻¹) hfiber
  calc
    _ = ∫⁻ r, w r*v r ∂ν := by
      change _ = ∫⁻ r, w r*v r ∂(volume.restrict (Icc 0 (R 0))).withDensity v
      rw [lintegral_withDensity_eq_lintegral_mul _ hvm (show Measurable (fun r => w r*v r) from hw.mul hvm)]
      apply lintegral_congr
      intro r
      dsimp [v]
      ring
    _ = ∫⁻ r, g (h r) ∂ν := lintegral_congr_ae heq
    _ = ∫⁻ t, g t ∂ν.map h := (lintegral_map hgm hh.continuous.measurable).symm
    _ = _ := by rw [hmap]

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma coarea_ratio_bound {A d P l z β : ℝ}
    (hA : 0 < A) (hd : 0 < d) (hβ : 0 < β)
    (hP : β*A ≤ P) (hQ : P^2 ≤ l*z) (hlam : A*d = l) :
    A/d ≤ (β⁻¹)^2*z := by
  have hAP : (β*A)^2 ≤ P^2 := sq_le_sq₀ (mul_pos hβ hA).le
    ((mul_pos hβ hA).le.trans hP) |>.mpr hP
  have h2 : β^2*A ≤ d*z := by
    apply (mul_le_mul_iff_left₀ hA).mp
    rw [←hlam] at hQ
    nlinarith only [hAP,hQ]
  have hratio : A/d ≤ z/(β^2) := (div_le_div_iff₀ hd (sq_pos_of_pos hβ)).mpr
    (by nlinarith only [h2])
  convert hratio using 1
  field_simp

theorem rearranged_profile_energy_bound (μ ζ : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ζ] {ω : ℝ} {n : ℕ} (hω : 0 < ω) (hn : 0 < n)
    {U K η : ℝ} (hU : 0 < U) (hK : 0 < K) (hη : η < 1)
    {P : ℝ → ℝ}
    (hpos : ∀ t ∈ Ico 0 U, 0 < μ.real (Ioi t))
    (hco : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((n:ℝ)*ω*(radiusDistribution μ ω n t)^(n-1)) ≤ P t ∧
      P t ≤ K*(μ.rnDeriv volume t).toReal ∧
      P t^2 ≤ (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal) :
    let R := radiusDistribution μ ω n
    let h := radialInverse R U
    ∫⁻ r in Icc 0 (R 0), ENNReal.ofReal ((n:ℝ)*ω*r^(n-1)) *
      (ENNReal.ofReal (-deriv h r))^2 ≤
      ENNReal.ofReal (((1-η)⁻¹)^2)*ζ univ := by
  dsimp only
  let R := radiusDistribution μ ω n
  have hc : 0 < (1-η)/K := div_pos (sub_pos.mpr hη) hK
  have hD := radius_secant_from_coarea μ hω hn hK
    (fun t ht => hpos t ⟨ht.1.le,ht.2⟩) (hco.mono fun _ h => ⟨h.1,h.2.1⟩)
  have hRpos : ∀ t ∈ Ico 0 U, 0 < R t := fun t ht => radius_pos μ hω (hpos t ht)
  have he := inverse_energy_identity hU hc (radius_antitone μ hω.le)
    hRpos hD (fun r => ENNReal.ofReal ((n:ℝ)*ω*r^(n-1))) (by fun_prop)
  rw [he]
  have hpt : ∀ᵐ t ∂volume.restrict (Icc 0 U),
      ENNReal.ofReal ((n:ℝ)*ω*R t^(n-1)) / ENNReal.ofReal (-deriv R t) ≤
        ENNReal.ofReal (((1-η)⁻¹)^2)*ζ.rnDeriv volume t := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hco,ae_restrict_of_ae (ae_radius_derivative μ hω hn),
      ae_inverse_derivative hU.le hc (radius_antitone μ hω.le) hD,
      ae_restrict_mem measurableSet_Ioo] with t hp hd hi ht
    have hA : 0 < (n:ℝ)*ω*R t^(n-1) :=
      mul_pos (mul_pos (by exact_mod_cast hn) hω) (pow_pos (hRpos t ⟨ht.1.le,ht.2⟩) _)
    have hdpos : 0 < -deriv R t := neg_pos.mpr
      (lt_of_le_of_ne (radius_antitone μ hω.le).deriv_nonpos hi.2.2)
    have hlam : ((n:ℝ)*ω*R t^(n-1))*(-deriv R t) = (μ.rnDeriv volume t).toReal := by
      have hc := hd.2
      change (n:ℝ)*ω*R t^(n-1)*deriv R t = _ at hc
      linarith
    have hr := coarea_ratio_bound hA hdpos (sub_pos.mpr hη) hp.1 hp.2.2 hlam
    calc
      _ = ENNReal.ofReal (((n:ℝ)*ω*R t^(n-1))/(-deriv R t)) :=
        (ENNReal.ofReal_div_of_pos hdpos).symm
      _ ≤ ENNReal.ofReal ((((1-η)⁻¹)^2)*(ζ.rnDeriv volume t).toReal) :=
        ENNReal.ofReal_le_ofReal hr
      _ = ENNReal.ofReal (((1-η)⁻¹)^2)*ENNReal.ofReal (ζ.rnDeriv volume t).toReal :=
        ENNReal.ofReal_mul (sq_nonneg _)
      _ ≤ _ := by gcongr; exact ENNReal.ofReal_toReal_le
  calc
    _ ≤ ∫⁻ t in Icc 0 U, ENNReal.ofReal (((1-η)⁻¹)^2)*ζ.rnDeriv volume t :=
      lintegral_mono_ae hpt
    _ = ENNReal.ofReal (((1-η)⁻¹)^2)*∫⁻ t in Icc 0 U, ζ.rnDeriv volume t := by
      rw [lintegral_const_mul _ (ζ.measurable_rnDeriv volume)]
    _ ≤ _ := by
      gcongr
      exact (Measure.setLIntegral_rnDeriv_le (μ := ζ) (ν := volume) (Icc 0 U)).trans (measure_mono (subset_univ _))

end CAT0Fillings.Rearrangement
end

end OAI
