import OAI.Probability.InvariantIsing.Fields.FieldSpinTransition
import OAI.Probability.IsingPerceptron.FiniteGaussianVariation

namespace OAI

/-! Continuity of the scalar Gaussian step at zero variance. The payoff
has a uniform linear envelope; the physical-spin observable is bounded.
This is the dominated-convergence input for closed height cones. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

lemma field_shift_linear_envelope {E : Type*} [TopologicalSpace E]
    {U : E → ℝ → ℝ} {s x : E → ℝ} (hs : Continuous s) (hx : Continuous x)
    {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (t₀ : E) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ᶠ t in 𝓝 t₀, ∀ u, |U t (x t + Real.sqrt (s t) * u)| ≤ A + B * ‖u‖ := by
  let X := |x t₀| + 1
  let R := |Real.sqrt (s t₀)| + 1
  have hX0 : |x t₀| < X := by dsimp only [X]; linarith
  have hR0 : |Real.sqrt (s t₀)| < R := by dsimp only [R]; linarith
  have hxB : ∀ᶠ t in 𝓝 t₀, |x t| < X :=
    (isOpen_lt hx.abs continuous_const).mem_nhds hX0
  have hsB : ∀ᶠ t in 𝓝 t₀, |Real.sqrt (s t)| < R :=
    (isOpen_lt (Real.continuous_sqrt.comp hs).abs continuous_const).mem_nhds
      hR0
  refine ⟨C + L * X, L * R, by dsimp only [X]; positivity,
    by dsimp only [R]; positivity, ?_⟩
  filter_upwards [hxB, hsB] with t ht hs'
  intro u
  have harg : |x t + Real.sqrt (s t) * u| ≤ X + R * |u| :=
    (abs_add_le _ _).trans (by rw [abs_mul]; gcongr)
  calc
    _ ≤ C + L * (X + R * |u|) := (hB t _).trans (by gcongr)
    _ = C + L * X + L * R * ‖u‖ := by rw [Real.norm_eq_abs]; ring

lemma continuous_field_gaussian_integral {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2)) (hs : Continuous s)
    (hx : Continuous x) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) :
    Continuous (fun t => ∫ u, U t (x t + Real.sqrt (s t) * u) ∂gaussianReal 0 1) := by
  let A := fun t u => U t (x t + Real.sqrt (s t) * u)
  have hA : Continuous (fun p : E × ℝ => A p.1 p.2) :=
    hU.comp (continuous_fst.prodMk ((hx.comp continuous_fst).add
      (((Real.continuous_sqrt.comp hs).comp continuous_fst).mul continuous_snd)))
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨D, B, hD, hBB, hb⟩ := field_shift_linear_envelope hs hx hC hL hB t₀
  apply tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => D + B * ‖u‖)
  · exact Eventually.of_forall (fun t =>
      (hA.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
  · filter_upwards [hb] with t ht
    exact ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using ht u)
  · exact gaussian_linearGrowth_integrable (by fun_prop)
      ⟨D, B, hD, hBB, fun u => by rw [abs_of_nonneg (by positivity)]⟩ _ _
  · exact ae_of_all _ (fun u =>
      (hA.comp (continuous_id.prodMk continuous_const)).continuousAt)

lemma continuous_field_gaussian_weighted {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2))
    (hA : Continuous (fun p : E × ℝ => A p.1 p.2))
    (hs : Continuous s) (hx : Continuous x) {C L M : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (_hM : 0 ≤ M)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (haB : ∀ t y, |A t y| ≤ M) (ζ : ℝ) :
    Continuous (fun t => ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u)) *
      A t (x t + Real.sqrt (s t) * u) ∂gaussianReal 0 1) := by
  let q := fun p : E × ℝ => (p.1, x p.1 + Real.sqrt (s p.1) * p.2)
  have hq : Continuous q := continuous_fst.prodMk ((hx.comp continuous_fst).add
    (((Real.continuous_sqrt.comp hs).comp continuous_fst).mul continuous_snd))
  have hF : Continuous (fun p : E × ℝ =>
      Real.exp (ζ * U p.1 (x p.1 + Real.sqrt (s p.1) * p.2)) *
        A p.1 (x p.1 + Real.sqrt (s p.1) * p.2)) :=
    (Real.continuous_exp.comp ((hU.comp hq).const_mul ζ)).mul (hA.comp hq)
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨D, B, _hD, _hBB, hb⟩ := field_shift_linear_envelope hs hx hC hL hB t₀
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (|ζ| * D) * Real.exp ((|ζ| * B) * ‖u‖) * M)
  · exact Eventually.of_forall (fun t =>
      (hF.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
  · filter_upwards [hb] with t ht
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have harg : ζ * U t (x t + Real.sqrt (s t) * u) ≤
        |ζ| * D + (|ζ| * B) * ‖u‖ := by
      calc
        _ ≤ |ζ * U t (x t + Real.sqrt (s t) * u)| := le_abs_self _
        _ = |ζ| * |U t (x t + Real.sqrt (s t) * u)| := abs_mul _ _
        _ ≤ |ζ| * (D + B * ‖u‖) := mul_le_mul_of_nonneg_left (ht u) (abs_nonneg _)
        _ = _ := by ring
    rw [← Real.exp_add]
    exact mul_le_mul (Real.exp_le_exp.mpr harg) (haB t _)
      (abs_nonneg _) (Real.exp_pos _).le
  · exact (((gaussianReal_exponentialNormMoments 0 1) (|ζ| * B)).const_mul
      (Real.exp (|ζ| * D))).mul_const M
  · exact ae_of_all _ (fun u =>
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt)

lemma continuous_field_gaussian_transform {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2)) (hs : Continuous s)
    (hx : Continuous x) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (ζ : ℝ) :
    Continuous (fun t => gaussianTransform (s t) ζ (U t) (x t)) := by
  by_cases hζ : ζ = 0
  · subst ζ
    simpa only [gaussianTransform, ite_true] using
      continuous_field_gaussian_integral hU hs hx hC hL hB
  · have hZ := continuous_field_gaussian_weighted (A := fun _ _ => 1) hU
      (show Continuous (fun _ : E × ℝ => (1 : ℝ)) from continuous_const)
      hs hx hC hL zero_le_one hB (fun _ _ => by norm_num) ζ
    simp only [mul_one] at hZ
    have hp (t : E) : 0 < ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u))
        ∂gaussianReal 0 1 := by
      apply IsingPerceptron.integral_exp_pos
      have hm : Measurable (U t) :=
        (hU.comp (continuous_const.prodMk continuous_id)).measurable
      have hg : HasLinearGrowth (U t) :=
        ⟨C, L, hC, hL, by simpa only [Real.norm_eq_abs] using hB t⟩
      exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
        (hm.comp (by fun_prop)) ((hg.add_left (x t)).scale_argument (Real.sqrt (s t))) ζ
    simpa only [gaussianTransform, hζ, ite_false] using
      (hZ.log (fun t => (hp t).ne')).div_const ζ

lemma continuous_field_gaussian_tilt_average {E : Type*} [TopologicalSpace E]
    [FirstCountableTopology E] {U A : E → ℝ → ℝ} {s x : E → ℝ}
    (hU : Continuous (fun p : E × ℝ => U p.1 p.2))
    (hA : Continuous (fun p : E × ℝ => A p.1 p.2))
    (hs : Continuous s) (hx : Continuous x) {C L M : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hB : ∀ t y, |U t y| ≤ C + L * |y|) (haB : ∀ t y, |A t y| ≤ M) (ζ : ℝ) :
    Continuous (fun t => gaussianTiltAverage (s t) ζ (U t) (A t) (x t)) := by
  have hn := continuous_field_gaussian_weighted hU hA hs hx hC hL hM hB haB ζ
  have hd := continuous_field_gaussian_weighted (A := fun _ _ => 1) hU
    (show Continuous (fun _ : E × ℝ => (1 : ℝ)) from continuous_const)
    hs hx hC hL zero_le_one hB (fun _ _ => by norm_num) ζ
  simp only [mul_one] at hd
  have hp (t : E) : 0 < ∫ u, Real.exp (ζ * U t (x t + Real.sqrt (s t) * u))
      ∂gaussianReal 0 1 := by
    apply IsingPerceptron.integral_exp_pos
    have hm : Measurable (U t) :=
      (hU.comp (continuous_const.prodMk continuous_id)).measurable
    have hg : HasLinearGrowth (U t) :=
      ⟨C, L, hC, hL, by simpa only [Real.norm_eq_abs] using hB t⟩
    exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
      (hm.comp (by fun_prop)) ((hg.add_left (x t)).scale_argument (Real.sqrt (s t))) ζ
  simp only [gaussianTiltAverage_eq_div]
  convert hn.div hd (fun t => (hp t).ne') using 1

end InvariantIsing

end

end OAI
