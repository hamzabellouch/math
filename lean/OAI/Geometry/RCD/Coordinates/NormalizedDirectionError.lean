import OAI.Geometry.RCD.Coordinates.DyadicMeanControl
import OAI.Geometry.RCD.Harmonic.GramDirectionalError

namespace OAI

/-! # Directional Gram errors after changing the exact normalizing frame -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] in
/-- Shifting the constant in an L1 error costs the measure times the shift. -/
theorem integral_abs_sub_const_le {f : X → ℝ} {s : Set X}
    (hf : IntegrableOn f s μ) (hs : μ s ≠ ∞) (a b : ℝ) :
    (∫ x in s, |f x - b| ∂μ) ≤
      (∫ x in s, |f x - a| ∂μ) + μ.real s * |a - b| := by
  have hc (c : ℝ) : IntegrableOn (fun _ : X => c) s μ := integrableOn_const hs
  have hb := integral_mono_ae (hf.sub (hc b)).abs
    ((hf.sub (hc a)).abs.add (hc |a - b|))
    (Filter.Eventually.of_forall fun x => abs_sub_le (f x) a b)
  have he := integral_add (hf.sub (hc a)).abs (hc |a - b|)
  simp only [Pi.sub_apply] at he
  simp only [Pi.add_apply, Pi.sub_apply] at hb
  rw [he] at hb
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul] using hb

/-- Express the length in the local exact frame using the working-frame mean. -/
theorem changed_frame_norm_sq {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (p : X) (r : ℝ)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (A : Euclidean n →L[ℝ] Euclidean n)
    (hexact : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
      (ball p r) measurableSet_ball S) (v : Euclidean n) :
    ‖S.symm (A v)‖ ^ 2 =
      ⟪v, sobolevMeanGram μ hQ ((sobolevColumnMap μ hQ u).comp A)
        (ball p r) measurableSet_ball v⟫_ℝ := by
  rw [sobolevMeanGram_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply]
  exact exact_mean_inverse_norm_sq μ hQ (sobolevColumnMap μ hQ u)
    (ball p r) measurableSet_ball S hexact (A v)

/-- The first-order splitting estimate expressed in arbitrary coordinates. -/
theorem changed_frame_local_error {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (p : X) (r : ℝ)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (A : Euclidean n →L[ℝ] Euclidean n)
    {ε : ℝ} {w : X → Euclidean n} (hε : 0 ≤ ε)
    (hfirst : FirstOrderSplittingOn μ hQ p r ε (transformedColumn μ hQ u S) w)
    (hvolume : 0 < μ.real (ball p r)) (hfinite : μ (ball p r) ≠ ∞)
    (v : Euclidean n) :
    (∫ x in ball p r, |localGamma μ hQ (sobolevColumnMap μ hQ u (A v))
      (sobolevColumnMap μ hQ u (A v)) x - ‖S.symm (A v)‖ ^ 2| ∂μ) ≤
      (n : ℝ) ^ 2 * (ε * μ.real (ball p r)) * ‖S.symm (A v)‖ ^ 2 := by
  have herror : ∀ i j : Fin n, ∫ x in ball p r,
      |localGamma μ hQ (transformedColumn μ hQ u S i) (transformedColumn μ hQ u S j) x -
        (if i = j then 1 else 0)| ∂μ ≤ ε * μ.real (ball p r) := by
    intro i j
    apply (div_le_iff₀ hvolume).mp
    simpa only [div_eq_inv_mul] using hfirst.gram i j
  have herr := directional_gram_error_le μ hQ (transformedColumn μ hQ u S)
    (ball p r) hfinite (mul_nonneg hε hvolume.le) herror (S.symm (A v))
  rw [sobolevColumnMap_transformed] at herr
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using herr

/-- An exact frame on the current ball and an operator estimate for the
working frame give the L1 directional error needed in a Gaussian shell. -/
theorem changed_frame_directional_error {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (p : X) (r : ℝ)
    (S : Euclidean n ≃L[ℝ] Euclidean n) (A : Euclidean n →L[ℝ] Euclidean n)
    {ε δ : ℝ} {w : X → Euclidean n} (hε : 0 ≤ ε)
    (hfirst : FirstOrderSplittingOn μ hQ p r ε (transformedColumn μ hQ u S) w)
    (hexact : IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
      (ball p r) measurableSet_ball S)
    (hvolume : 0 < μ.real (ball p r)) (hfinite : μ (ball p r) ≠ ∞)
    (hnorm : ‖sobolevMeanGram μ hQ ((sobolevColumnMap μ hQ u).comp A)
      (ball p r) measurableSet_ball - ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤ δ)
    (v : Euclidean n) :
    (∫ x in ball p r, |localGamma μ hQ (sobolevColumnMap μ hQ u (A v))
      (sobolevColumnMap μ hQ u (A v)) x - ‖v‖ ^ 2| ∂μ) ≤
      (((n : ℝ) ^ 2 * ε) * (1 + δ) + δ) * μ.real (ball p r) * ‖v‖ ^ 2 := by
  let U := sobolevColumnMap μ hQ u
  let z := S.symm (A v)
  have herr := changed_frame_local_error μ hQ u p r S A hε hfirst hvolume hfinite v
  have hz := changed_frame_norm_sq μ hQ u p r S A hexact v
  have hupper : ‖z‖ ^ 2 ≤ (1 + δ) * ‖v‖ ^ 2 := by
    rw [hz]
    exact inner_upper_of_sub_id_norm _ hnorm v
  have hdelta : |‖z‖ ^ 2 - ‖v‖ ^ 2| ≤ δ * ‖v‖ ^ 2 := by
    have hl := inner_lower_of_sub_id_norm _ hnorm v
    have hu := inner_upper_of_sub_id_norm _ hnorm v
    rw [← hz] at hl hu
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have htri := integral_abs_sub_const_le μ
    (localGamma_memL1 μ hQ (U (A v)) (U (A v))).integrableOn hfinite (‖z‖ ^ 2) (‖v‖ ^ 2)
  have hnormterm := mul_le_mul_of_nonneg_left hupper
    (mul_nonneg (sq_nonneg (n : ℝ)) (mul_nonneg hε hvolume.le))
  have hconstant := mul_le_mul_of_nonneg_left hdelta hvolume.le
  change (∫ x in ball p r, |localGamma μ hQ (U (A v)) (U (A v)) x - ‖v‖ ^ 2| ∂μ) ≤ _
  nlinarith

end RegularPointCoordinates

end

end OAI
