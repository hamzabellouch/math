import OAI.Geometry.LatticeCovering.GaussianRates

namespace OAI


namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

noncomputable def localScale (C : ℝ) (n : ℕ) : ℕ := ⌈sectionRadius C n⌉₊+2

lemma sectionRadius_le_localScale (C : ℝ) (n : ℕ) :
    sectionRadius C n ≤ (localScale C n : ℝ) := by
  have H := Nat.le_ceil (sectionRadius C n)
  dsimp [localScale]
  push_cast
  linarith

lemma dimension_le_localScale {C : ℝ} (hC : 0 < C) {n D : ℕ}
    (hD : (D:ℝ) ≤ C*((firstSize n:ℝ)+1)) : D ≤ localScale C n := by
  have _ := hC
  have hc := sectionRadius_le_localScale C n
  have hh : (D:ℝ) ≤ (localScale C n:ℝ) := by
    dsimp [sectionRadius] at hc
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity]
  exact_mod_cast hh

lemma localScale_tendsto {C : ℝ} (hC : 0 < C) : Tendsto (localScale C) atTop atTop := by
  apply tendsto_atTop_mono _ firstSize_tendsto
  intro n
  have H := sectionRadius_le_localScale C n
  dsimp [sectionRadius] at H
  exact_mod_cast (show (firstSize n:ℝ) ≤ (localScale C n:ℝ) by
    nlinarith [show (0:ℝ) ≤ (firstSize n:ℝ) by positivity])

lemma eventually_localScale_root {C : ℝ} (hC : 0 < C) : ∀ᶠ n : ℕ in atTop,
    Real.exp ((localScale C n:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ)) := by
  let H : ℝ := 3*(C+2)
  have hH : 0 < H := by dsimp [H]; positivity
  have hsmall : (fun n : ℕ => (Real.log (Real.log (n:ℝ)))^60) =o[atTop]
      (fun n => Real.log (n:ℝ)) := by
    simpa only [Function.comp_def,Real.rpow_natCast,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop ((60:ℕ):ℝ) (by norm_num : (0:ℝ) < 1)).comp_tendsto log_nat_atTop
  filter_upwards [hsmall.bound (by positivity : 0 < 1/(4*H^30)),
    loglog_nat_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℕ)] with n hbound hs hn
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ Real.log (Real.log (n:ℝ)) := le_trans zero_le_one hs
  have hs2 : 1 ≤ (Real.log (Real.log (n:ℝ)))^2 := one_le_pow₀ hs
  have hceil := Nat.ceil_lt_add_one (sq_nonneg (Real.log (Real.log (n:ℝ))))
  change (firstSize n:ℝ) < (Real.log (Real.log (n:ℝ)))^2+1 at hceil
  have hlceil := Nat.ceil_lt_add_one (sectionRadius_pos hC n).le
  have hl : (localScale C n:ℝ) ≤ H*(Real.log (Real.log (n:ℝ)))^2 := by
    dsimp [localScale,sectionRadius]
    push_cast
    dsimp [sectionRadius] at hlceil
    have hh := mul_le_mul_of_nonneg_left hceil.le (show 0 ≤ C+1 by linarith)
    dsimp [H]
    nlinarith [mul_nonneg (show 0 ≤ 2*C+5 by linarith) (sub_nonneg.mpr hs2)]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hs0 _),
    abs_of_nonneg (Real.log_natCast_nonneg n)] at hbound
  have hpow : (localScale C n:ℝ)^30 ≤ H^30*(Real.log (Real.log (n:ℝ)))^60 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (localScale C n)) hl 30
    simpa only [mul_pow,←pow_mul] using hh
  have hexp : 4*(localScale C n:ℝ)^30 ≤ Real.log (n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 4*H^30)
    have he : (4*H^30)*(1/(4*H^30)*Real.log (n:ℝ))=Real.log (n:ℝ) := by field_simp
    rw [he] at hh
    nlinarith
  have hlog : Real.log (Real.sqrt (Real.sqrt (n:ℝ)))=Real.log (n:ℝ)/4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg _),Real.log_sqrt hnp.le]
    ring
  rw [←Real.exp_log (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hnp))]
  apply Real.exp_le_exp.mpr
  rw [hlog]
  linarith


end SingleLatticeCovering.FinalRates



namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory MeasureTheory.Measure Set Filter Topology GaussianDensity CanonicalDensity Sections
open scoped ENNReal

lemma normalizer_half (D : ℕ) : normalizer D (1/2)=(Real.sqrt (2*Real.pi))^D := by
  unfold normalizer
  rw [show Real.pi/(1/2)=2*Real.pi by ring,Real.sqrt_eq_rpow,
    ←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 2*Real.pi)]
  congr 1
  ring

lemma density_half_gaussian {D : ℕ} (y : E D) :
    GaussianDensity.density (1/2) y=Sections.gaussian (E D) y := by
  unfold GaussianDensity.density Sections.gaussian
  rw [normalizer_half,finrank_euclideanSpace_fin,zpow_neg,zpow_natCast]
  congr 1
  congr 1
  ring


theorem eventually_local_coordinate_position : ∀ᶠ l : ℕ in atTop,
    ∀ m D : ℕ, D ≤ l → 0 < m+D →
      Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
      ∀ K : Set (Fin (m+D) → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
        ∃ e : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ),
          ∀ y : Fin D → ℝ, ‖WithLp.toLp 2 y‖ ≤ 6*(l:ℝ)^2 →
            (volume (e '' K)).toReal*Folded.gamma y/2 ≤
              (volume (coordinateFiber (e '' K) y)).toReal := by
  filter_upwards [eventually_local_position] with l hl
  intro m D hD hn hroot K hK hc hi
  let A : (Fin (m+D) → ℝ) ≃ₗ[ℝ] E (m+D) := (WithLp.linearEquiv 2 ℝ (Fin (m+D) → ℝ)).symm
  have hAK : IsCompact (A '' K) := hK.image A.toContinuousLinearEquiv.continuous
  have hAc : Convex ℝ (A '' K) := hc.linear_image A.toLinearMap
  have hAi : (interior (A '' K)).Nonempty := by
    change (interior (A.toContinuousLinearEquiv.toHomeomorph '' K)).Nonempty
    rw [←A.toContinuousLinearEquiv.toHomeomorph.image_interior]
    exact hi.image _
  obtain ⟨g,hg⟩ := hl m D hD hn hroot (A '' K) hAK hAc hAi
  let J := g '' (A '' K)
  have hJ : IsCompact J := hAK.image g.toAffineMap.continuous_of_finiteDimensional
  let G : E (m+D) ≃ₜ ((Fin m → ℝ) × E D) :=
    { toEquiv := g.toEquiv
      continuous_toFun := g.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := g.symm.toAffineMap.continuous_of_finiteDimensional }
  have hJi : (interior J).Nonempty := by
    change (interior (G '' (A '' K))).Nonempty
    rw [←G.image_interior]
    exact hAi.image G
  have hJ0 : 0 < (volume J).toReal := by
    apply ENNReal.toReal_pos (ne_of_gt ?_) hJ.measure_ne_top
    exact (isOpen_interior.measure_pos volume hJi).trans_le (measure_mono interior_subset)
  let e := A.toAffineEquiv.trans (g.trans (flatten m D).toAffineEquiv)
  have he : e '' K=flatten m D '' J := by
    dsimp [e,J]
    rw [Set.image_image,Set.image_image]
    rfl
  refine ⟨e,fun y hy => ?_⟩
  rw [he,flatten_volume m D hJ]
  have hf : coordinateFiber (flatten m D '' J) y=Sections.fiber J (WithLp.toLp 2 y) := by
    have H := flatten_fiber (flatten m D '' J) (WithLp.toLp 2 y)
    have hc : (flatten m D).symm '' ((flatten m D) '' J)=J := by
      simp only [Set.image_image,LinearEquiv.symm_apply_apply,Set.image_id']
    rw [hc] at H
    exact H.symm
  rw [hf]
  have H := hg (WithLp.toLp 2 y) hy
  rw [density_half_gaussian,gaussian_toLp] at H
  change Folded.gamma y/2 ≤ canonical J (WithLp.toLp 2 y) at H
  rw [canonical,ENNReal.toReal_inv] at H
  have HH := mul_le_mul_of_nonneg_left H hJ0.le
  rw [←mul_assoc,mul_inv_cancel₀ hJ0.ne',one_mul] at HH
  simpa only [mul_div_assoc] using HH


end SingleLatticeCovering.GaussianNumerics




noncomputable section

end

end OAI
