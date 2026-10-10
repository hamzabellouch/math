import OAI.Geometry.RCD.Transport.RenyiSobolevDensity

namespace OAI

/-! # Exponential heat-energy control without compact initial support -/

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heat_exponential_energy_lintegral (f : Lp ℝ 2 μ) (p : X)
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hfi : Integrable (fun x => Real.exp (a*dist p x)*(f x)^2) μ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (a*dist p x)*(heatAt μ hQ t f x)^2) ∂μ) ≤
      ENNReal.ofReal (Real.exp (a^2/2*t)*(∫ x, Real.exp (a*dist p x)*(f x)^2 ∂μ)) := by
  let u := heatAt μ hQ t f
  let F := fun (i : ℕ) x => ENNReal.ofReal (radialWeight p a i x*(u x)^2)
  have hm (i : ℕ) : AEMeasurable (F i) μ :=
    ((radialWeight_lipschitz p ha i).continuous.measurable.aemeasurable.mul
      ((Lp.aestronglyMeasurable u).aemeasurable.pow_const 2)).ennreal_ofReal
  have hmono : ∀ᵐ x ∂μ, Monotone (fun i => F i x) := .of_forall fun x i j hij => by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (min_le_min_left _ (Nat.cast_le.mpr hij)) ha)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (a*dist p x)*(u x)^2))) := .of_forall fun x => by
    have he : ∀ᶠ i : ℕ in atTop, dist p x ≤ (i:ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (dist p x))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with i hi
    simp only [F,radialWeight,min_eq_left hi]
  have hb (i : ℕ) : (∫⁻ x, F i x ∂μ) ≤
      ENNReal.ofReal (Real.exp (a^2/2*t)*(∫ x, Real.exp (a*dist p x)*(f x)^2 ∂μ)) := by
    obtain ⟨hi,hb⟩ := heatAt_radialWeight_integral μ hQ f p ha (i:ℝ) ht
    have hi0 := (heatAt_radialWeight_integral μ hQ f p ha (i:ℝ) (t:=0) le_rfl).1
    simp only [heatAt_zero,one_apply_eq_self] at hi0
    have hinit : (∫ x, radialWeight p a i x*(f x)^2 ∂μ) ≤
        ∫ x, Real.exp (a*dist p x)*(f x)^2 ∂μ := by
      apply integral_mono_ae hi0 hfi
      exact .of_forall fun x => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)) (sq_nonneg _)
    rw [←ofReal_integral_eq_lintegral_ofReal hi
      (.of_forall fun x => mul_nonneg (radialWeight_nonneg p a i x) (sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hb.trans (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le))
  exact le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone hm hmono hlim) (.of_forall hb)

 theorem heat_exponential_energy (f : Lp ℝ 2 μ) (p : X)
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hfi : Integrable (fun x => Real.exp (a*dist p x)*(f x)^2) μ) :
    Integrable (fun x => Real.exp (a*dist p x)*(heatAt μ hQ t f x)^2) μ ∧
    (∫ x, Real.exp (a*dist p x)*(heatAt μ hQ t f x)^2 ∂μ) ≤
      Real.exp (a^2/2*t)*(∫ x, Real.exp (a*dist p x)*(f x)^2 ∂μ) := by
  have hb := heat_exponential_energy_lintegral μ hQ f p ha ht hfi
  have hn : ∀ᵐ x ∂μ, 0 ≤ Real.exp (a*dist p x)*(heatAt μ hQ t f x)^2 :=
    .of_forall fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hi : Integrable (fun x => Real.exp (a*dist p x)*(heatAt μ hQ t f x)^2) μ := by
    refine ⟨((by fun_prop : Measurable (fun x : X => Real.exp (a*dist p x))).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable _).pow 2)),?_⟩
    rw [hasFiniteIntegral_iff_ofReal hn]
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  refine ⟨hi,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hi hn] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le
    (integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))).mp hb

end RegularPointCoordinates

end

end OAI
