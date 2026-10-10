import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem preBrownian_increment_indep_past {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    IndepFun (fun ω => B t ω - B s ω)
      (fun ω (u : Set.Iic s) => B u ω) P := by
  have h : IndepFun (fun ω => B (s + (t - s)) ω - B s ω)
      (fun ω (u : Set.Iic s) => B u ω) P :=
    (hB.indepFun_shift s).comp (measurable_pi_apply (t - s)) measurable_id
  simpa [Function.comp_def, add_tsub_cancel_of_le hst] using h

theorem preBrownian_martingale_natural {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) :
    Martingale B (Filtration.natural B hm) P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨Filtration.stronglyAdapted_natural hm, ?_⟩
  intro s t hst
  have hind := preBrownian_increment_indep_past hB hst
  have hn := Filtration.natural_eq_comap B hm s
  have hcond : P[(fun ω => B t ω - B s ω) | Filtration.natural B hm s] =ᵐ[P]
      fun _ => ∫ ω, B t ω - B s ω ∂P := by
    rw [hn]
    exact condExp_indep_eq (hm t |>.measurable.sub (hm s).measurable).comap_le
      (hn ▸ (Filtration.natural B hm).le s) (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hind
  have hzero : (∫ ω, B t ω - B s ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval, hB.integral_eval, sub_self]
  have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s)
    (Filtration.natural B hm s)
  have hself := condExp_of_stronglyMeasurable (Filtration.natural B hm |>.le s)
    (Filtration.stronglyAdapted_natural hm s) (hB.integrable_eval s)
  filter_upwards [hcond, hsub] with ω hc hs
  rw [hzero] at hc
  rw [hself] at hs
  simp only [Pi.sub_apply] at hs
  change P[B t - B s | Filtration.natural B hm s] ω = 0 at hc
  rw [hc] at hs
  linarith

theorem preBrownian_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) : (∫ ω, (B t ω)^2 ∂P) = (t : ℝ) := by
  have h := hB.covariance_eval t t
  simpa [covariance, hB.integral_eval, pow_two] using h

theorem preBrownian_increment_sq_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[(fun ω => (B t ω - B s ω)^2) | Filtration.natural B hm s] =ᵐ[P]
      fun _ => ((t : ℝ) - (s : ℝ)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hind : IndepFun (fun ω => (B t ω - B s ω)^2)
      (fun ω (u : Set.Iic s) => B u ω) P :=
    (preBrownian_increment_indep_past hB hst).comp (measurable_id.pow_const 2) measurable_id
  have hn := Filtration.natural_eq_comap B hm s
  have hcond : P[(fun ω => (B t ω - B s ω)^2) | Filtration.natural B hm s] =ᵐ[P]
      fun _ => ∫ ω, (B t ω - B s ω)^2 ∂P := by
    rw [hn]
    exact condExp_indep_eq ((hm t).measurable.sub (hm s).measurable |>.pow_const 2).comap_le
      (hn ▸ (Filtration.natural B hm).le s)
      (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hind
  have hint : (∫ ω, (B t ω - B s ω)^2 ∂P) = (t : ℝ) - (s : ℝ) := by
    have h := preBrownian_integral_sq (hB.shift s) (t - s)
    simpa [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using h
  simpa only [hint] using hcond

theorem preBrownian_increment_condExp_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[(fun ω => B t ω - B s ω) | Filtration.natural B hm s] =ᵐ[P] fun _ => 0 := by
  have hM := preBrownian_martingale_natural hB hm
  have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s)
    (Filtration.natural B hm s)
  filter_upwards [hsub, hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω h1 h2 h3
  simpa only [Pi.sub_def, h2, h3, sub_self] using h1

theorem preBrownian_square_sub_time_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) :
    Martingale (fun t ω => (B t ω)^2 - (t : ℝ)) (Filtration.natural B hm) P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hM := preBrownian_martingale_natural hB hm
  have hL2 (t) := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  refine ⟨fun t => (hM.stronglyAdapted t).pow 2 |>.sub stronglyMeasurable_const, ?_⟩
  intro s t hst
  let F := Filtration.natural B hm s
  let X : Ω → ℝ := B t - B s
  have hXL2 : MemLp X 2 P := (hL2 t).sub (hL2 s)
  have hXint : Integrable X P := (hB.integrable_eval t).sub (hB.integrable_eval s)
  have hXzero : P[X | F] =ᵐ[P] fun _ => 0 := by
    have hsub := condExp_sub (hB.integrable_eval t) (hB.integrable_eval s) F
    filter_upwards [hsub, hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω h1 h2 h3
    dsimp [X, F] at *
    simp only [h2, h3, sub_self] at h1
    exact h1
  have hprodInt : Integrable (B s * X) P := (hL2 s).integrable_mul hXL2
  have hprodZero : P[B s * X | F] =ᵐ[P] fun _ => 0 := by
    have hp := condExp_mul_of_stronglyMeasurable_left (hM.stronglyAdapted s) hprodInt hXint
    filter_upwards [hp, hXzero] with ω hp hz
    change P[B s * X | F] ω = B s ω * P[X | F] ω at hp
    rw [hz, mul_zero] at hp
    exact hp
  have htwoZero : P[(fun ω => 2 * (B s ω * X ω)) | F] =ᵐ[P] fun _ => 0 := by
    have hp := condExp_smul (μ := P) (2 : ℝ) (B s * X) F
    filter_upwards [hp, hprodZero] with ω hp hz
    change P[(fun ω => 2 * (B s ω * X ω)) | F] ω = 2 * P[B s * X | F] ω at hp
    rw [hz, mul_zero] at hp
    exact hp
  have hXSq := preBrownian_increment_sq_condExp (mΩ := mΩ) hB hm hst
  have hBSq : P[(fun ω => (B s ω)^2) | F] = (fun ω => (B s ω)^2) :=
    condExp_of_stronglyMeasurable (Filtration.natural B hm |>.le s)
      ((hM.stronglyAdapted s).pow 2) (hL2 s).integrable_sq
  have hfun : (fun ω => (B t ω)^2) =
      (fun ω => (X ω)^2 + 2 * (B s ω * X ω)) + (fun ω => (B s ω)^2) := by
    funext ω
    dsimp [X]
    ring
  have hsum1 := condExp_add hXL2.integrable_sq (hprodInt.const_mul 2) F
  have hsum2 := condExp_add (hXL2.integrable_sq.add (hprodInt.const_mul 2))
    (hL2 s).integrable_sq F
  have hBtSq : P[(fun ω => (B t ω)^2) | F] =ᵐ[P]
      fun ω => ((t : ℝ) - (s : ℝ)) + (B s ω)^2 := by
    rw [hfun]
    filter_upwards [hsum2, hsum1, htwoZero, hXSq] with ω h2 h1 hz hsq
    change P[(fun ω => (X ω)^2) | F] ω = (t : ℝ) - (s : ℝ) at hsq
    simp only [Pi.add_def, Pi.mul_def] at h2 h1
    rw [hBSq] at h2
    rw [h1, hz, hsq] at h2
    simpa only [Pi.add_def, add_zero] using h2
  have hsub := condExp_sub (hL2 t).integrable_sq (integrable_const (t : ℝ)) F
  have hc : P[(fun _ : Ω => (t : ℝ)) | F] = (fun _ => (t : ℝ)) :=
    condExp_const (Filtration.natural B hm |>.le s) (t : ℝ)
  filter_upwards [hsub, hBtSq] with ω hs hsq
  rw [hc] at hs
  simp only [Pi.sub_apply] at hs
  rw [hsq] at hs
  simp only [Pi.sub_def] at hs
  exact hs.trans (by ring)

noncomputable def brownianExponential {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := Real.exp (a * B t ω - a^2 * (t : ℝ) / 2)

theorem preBrownian_integrable_exp_mul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (a : ℝ) : Integrable (fun ω => Real.exp (a * B t ω)) P := by
  have hi : Integrable (fun x : ℝ => Real.exp (a * x)) (P.map (B t)) := by
    rw [(hB.hasLaw_eval t).map_eq]
    exact integrable_exp_mul_gaussianReal a
  exact (integrable_map_measure (by fun_prop) (hB.aemeasurable t)).mp hi

theorem preBrownian_exponential_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (a : ℝ) : Integrable (brownianExponential B a t) P := by
  have hi := (preBrownian_integrable_exp_mul hB t a).mul_const
    (Real.exp (-(a^2 * (t : ℝ) / 2)))
  convert hi using 1
  funext ω
  simp only [brownianExponential, ← Real.exp_add]
  congr 1

theorem preBrownian_exponential_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (a : ℝ) : (∫ ω, brownianExponential B a t ω ∂P) = 1 := by
  have heq : brownianExponential B a t =
      fun ω => Real.exp (-(a^2 * (t : ℝ) / 2)) * Real.exp (a * B t ω) := by
    funext ω
    simp only [brownianExponential, ← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul]
  change Real.exp (-(a^2 * (t : ℝ) / 2)) * mgf (B t) P a = 1
  rw [mgf_gaussianReal (hB.hasLaw_eval t)]
  rw [← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem preBrownian_exponential_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) (a : ℝ) :
    Martingale (brownianExponential B a) (Filtration.natural B hm) P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have had : StronglyAdapted (Filtration.natural B hm) (brownianExponential B a) := by
    intro t
    exact Real.continuous_exp.comp_stronglyMeasurable
      ((stronglyMeasurable_const.mul (Filtration.stronglyAdapted_natural hm t)).sub
        stronglyMeasurable_const)
  refine ⟨had, ?_⟩
  intro s t hst
  let D : Ω → ℝ := fun ω => Real.exp
    (a * (B t ω - B s ω) - a^2 * ((t : ℝ) - (s : ℝ)) / 2)
  have hD : D = brownianExponential (fun u ω => B (s + u) ω - B s ω) a (t - s) := by
    funext ω
    simp [D, brownianExponential, add_tsub_cancel_of_le hst, NNReal.coe_sub hst]
  have hDint : Integrable D P := by
    rw [hD]
    exact preBrownian_exponential_integrable (hB.shift s) (t - s) a
  have hDone : (∫ ω, D ω ∂P) = 1 := by
    rw [hD]
    exact preBrownian_exponential_integral (hB.shift s) (t - s) a
  have hind : IndepFun D (fun ω (u : Set.Iic s) => B u ω) P :=
    (preBrownian_increment_indep_past hB hst).comp
      (show Measurable (fun x : ℝ => Real.exp (a * x - a^2 * ((t : ℝ) - (s : ℝ)) / 2)) from by fun_prop)
      measurable_id
  have hn := Filtration.natural_eq_comap B hm s
  have hDC : P[D | Filtration.natural B hm s] =ᵐ[P] fun _ => 1 := by
    have hc : P[D | Filtration.natural B hm s] =ᵐ[P] fun _ => ∫ ω, D ω ∂P := by
      rw [hn]
      exact condExp_indep_eq (show Measurable D from by dsimp [D]; fun_prop).comap_le
        (hn ▸ (Filtration.natural B hm).le s)
        (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable hind
    simpa only [hDone] using hc
  have hfactor : brownianExponential B a t = brownianExponential B a s * D := by
    funext ω
    simp only [brownianExponential, Pi.mul_apply, D, ← Real.exp_add]
    congr 1
    ring
  have hprodInt : Integrable (brownianExponential B a s * D) P := by
    rw [← hfactor]
    exact preBrownian_exponential_integrable hB t a
  rw [hfactor]
  have hp := condExp_mul_of_stronglyMeasurable_left (had s) hprodInt hDint
  filter_upwards [hp, hDC] with ω hp hc
  simpa only [Pi.mul_apply, hc, mul_one] using hp

end Problem367

end OAI
