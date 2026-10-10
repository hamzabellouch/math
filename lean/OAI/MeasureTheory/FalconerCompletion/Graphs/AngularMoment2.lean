import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.AngularMoment
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ENNReal ComplexConjugate
variable {V : Type*} [MeasurableSpace V]

noncomputable def sourceAngularMomentND (μ : Measure V) (U : ℝ × V → ℂ) (r : ℝ) : ℝ :=
  ∫ w, ‖U (r,w)‖^2 ∂μ

noncomputable def sourceAngularHND (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) : ℝ :=
  (2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ∫ r, Ψ (r/(2:ℝ)^v)*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r

noncomputable def sourceAngularHFND (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) : ℝ :=
  (2:ℝ)^((d:ℝ)*(v-a))*((2:ℝ)^v)⁻¹*
    ∫ r, Ψ (r/(2:ℝ)^v)*‖∫ w, ψ w*U (r,w)*conj (W (r,w)) ∂μ‖^2

lemma graph_radial_normalizationND {Ω : ℝ} (hΩ : 0 < Ω) (Ψ f : ℝ → ℝ) :
    Ω⁻¹*(∫ r, Ψ (r/Ω)*f r) = ∫ u, Ψ u*f (Ω*u) := by
  have h := Measure.integral_comp_mul_left (fun r => Ψ (r/Ω)*f r) Ω
  simp only [abs_of_pos (inv_pos.mpr hΩ),smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with u
  rw [mul_div_cancel_left₀ u hΩ.ne']

lemma sourceAngularHND_normalized (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (U W : ℝ × V → ℂ) :
    sourceAngularHND d μ a v Ψ U W = (2:ℝ)^((d:ℝ)*(v-a))*
      ∫ u, Ψ u*sourceAngularMomentND μ U ((2:ℝ)^v*u)*sourceAngularMomentND μ W ((2:ℝ)^v*u) := by
  dsimp [sourceAngularHND]
  rw [mul_assoc]
  congr 1
  simpa only [mul_assoc] using graph_radial_normalizationND (by positivity : (0:ℝ)<(2:ℝ)^v)
    Ψ (fun r => sourceAngularMomentND μ U r*sourceAngularMomentND μ W r)

lemma sourceAngularHFND_normalized (d : ℕ) (μ : Measure V) (a v : ℝ)
    (Ψ : ℝ → ℝ) (ψ : V → ℂ) (U W : ℝ × V → ℂ) :
    sourceAngularHFND d μ a v Ψ ψ U W = (2:ℝ)^((d:ℝ)*(v-a))*
      ∫ u, Ψ u*‖∫ w, ψ w*U ((2:ℝ)^v*u,w)*conj (W ((2:ℝ)^v*u,w)) ∂μ‖^2 := by
  dsimp [sourceAngularHFND]
  rw [mul_assoc,graph_radial_normalizationND (by positivity : (0:ℝ)<(2:ℝ)^v)]

lemma sourceAngularMomentND_measurable (μ : Measure V) [SFinite μ]
    {U : ℝ × V → ℂ} (hU : Measurable U) : Measurable (sourceAngularMomentND μ U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

lemma sourceAngularMomentND_nonneg (μ : Measure V) (U : ℝ × V → ℂ) (r : ℝ) :
    0 ≤ sourceAngularMomentND μ U r := integral_nonneg (fun _ => sq_nonneg _)

lemma sourceAngularMomentND_bound (μ : Measure V) [IsFiniteMeasure μ]
    (U : ℝ × V → ℂ) {C : ℝ} (r : ℝ) (hb : ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ C) :
    sourceAngularMomentND μ U r ≤ C^2*μ.real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hb] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

lemma angular_square_integrableND (μ : Measure V) [IsFiniteMeasure μ]
    {f : V → ℂ} (hf : Measurable f) {C : ℝ} (hb : ∀ᵐ w ∂μ, ‖f w‖ ≤ C) :
    Integrable (fun w => ‖f w‖^2) μ := by
  apply Integrable.of_bound (hf.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards [hb] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hw 2

lemma graph_weighted_moments_integrableND (μ : Measure V) [IsFiniteMeasure μ]
    {U W : ℝ × V → ℂ} (hU : Measurable U) (hW : Measurable W)
    {C D : ℝ} (hUbound : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖ ≤ C)
    (hWbound : ∀ r, ∀ᵐ w ∂μ, ‖W (r,w)‖ ≤ D)
    {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ) :
    Integrable (fun r => Ψ r*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r) := by
  apply (hΨ.norm.mul_const ((C^2*μ.real univ)*(D^2*μ.real univ))).mono'
    ((hΨ.aestronglyMeasurable.mul (sourceAngularMomentND_measurable μ hU).aestronglyMeasurable).mul
      (sourceAngularMomentND_measurable μ hW).aestronglyMeasurable)
  filter_upwards with r
  change ‖Ψ r*sourceAngularMomentND μ U r*sourceAngularMomentND μ W r‖ ≤ _
  rw [norm_mul,norm_mul,Real.norm_eq_abs (sourceAngularMomentND μ U r),
    Real.norm_eq_abs (sourceAngularMomentND μ W r),
    abs_of_nonneg (sourceAngularMomentND_nonneg μ U r),
    abs_of_nonneg (sourceAngularMomentND_nonneg μ W r),mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (sourceAngularMomentND_bound μ U r (hUbound r))
    (sourceAngularMomentND_bound μ W r (hWbound r)) (sourceAngularMomentND_nonneg μ W r)
      (by positivity)) (norm_nonneg _)

lemma sourceAngularMomentND_pair (μ : Measure V) [SFinite μ]
    (U W : ℝ × V → ℂ) (r : ℝ) :
    (∫ w : V × V, ‖U (r,w.1)*W (r,w.2)‖^2 ∂μ.prod μ) =
      sourceAngularMomentND μ U r*sourceAngularMomentND μ W r := by
  simp_rw [norm_mul,mul_pow]
  exact integral_prod_mul (fun w => ‖U (r,w)‖^2) (fun w => ‖W (r,w)‖^2)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
