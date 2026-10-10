import OAI.MathematicalPhysics.Boltzmann.Compactness.PairRepresentative

namespace OAI

/-! # Removal of compact velocity cutoffs under uniform Gaussian moments -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X]

private theorem gaussian_integrable (μ : Measure (X × (Velocity × Velocity)))
    {M : ℝ} (hM : 0 ≤ M)
    (hm : (∫⁻ p, ENNReal.ofReal (weight p.2.1*weight p.2.2) ∂μ) ≤ ENNReal.ofReal M) :
    Integrable (fun p => weight p.2.1*weight p.2.2) μ ∧
      (∫ p, weight p.2.1*weight p.2.2 ∂μ) ≤ M := by
  have hn : ∀ᵐ p ∂μ, 0 ≤ weight p.2.1*weight p.2.2 :=
    ae_of_all _ (fun _ => mul_nonneg (weight_pos _).le (weight_pos _).le)
  have hi : Integrable (fun p => weight p.2.1*weight p.2.2) μ := by
    refine ⟨by unfold weight; fun_prop,?_⟩
    exact (hasFiniteIntegral_iff_ofReal hn).mpr (hm.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hi,(ENNReal.ofReal_le_ofReal_iff hM).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi hn]
  exact hm

private theorem weighted_gaussian_integrable (μ : Measure (X × (Velocity × Velocity)))
    (hi : Integrable (fun p => weight p.2.1*weight p.2.2) μ)
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    {f : Velocity × Velocity → ℝ} (hf : Measurable f)
    {C : ℝ} (hb : ∀ p, |f p| ≤ C*(weight p.1*weight p.2)) :
    Integrable (fun p => θ p.1*f p.2) μ := by
  apply (hi.const_mul (|B| *C)).mono'
    ((hθ.comp measurable_fst).mul (hf.comp measurable_snd)).aestronglyMeasurable
  exact ae_of_all _ (fun p => by
    change ‖θ p.1*f p.2‖ ≤ (|B| *C)*(weight p.2.1*weight p.2.2)
    rw [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ |B| *(C*(weight p.2.1*weight p.2.2)) :=
        mul_le_mul ((hB _).trans (le_abs_self B)) (hb _) (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring)

theorem weighted_gaussian_error (μ : Measure (X × (Velocity × Velocity)))
    {M : ℝ} (hM : 0 ≤ M)
    (hm : (∫⁻ p, ENNReal.ofReal (weight p.2.1*weight p.2.2) ∂μ) ≤ ENNReal.ofReal M)
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    {f g : Velocity × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {C δ : ℝ} (hδ : 0 ≤ δ)
    (hf : ∀ p, |f p| ≤ C*(weight p.1*weight p.2))
    (he : ∀ p, |g p-f p| ≤ δ*(weight p.1*weight p.2)) :
    |(∫ p, θ p.1*g p.2 ∂μ)-(∫ p, θ p.1*f p.2 ∂μ)| ≤ |B| *δ*M := by
  obtain ⟨hi,hbound⟩ := gaussian_integrable μ hM hm
  have hg (p) : |g p| ≤ (δ+C)*(weight p.1*weight p.2) := by
    have ht := abs_add_le (g p-f p) (f p)
    rw [sub_add_cancel] at ht
    have hb := add_le_add (he p) (hf p)
    nlinarith
  rw [← integral_sub (weighted_gaussian_integrable μ hi hθ hB hgm hg)
    (weighted_gaussian_integrable μ hi hθ hB hfm hf),← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le (hi.const_mul (|B| *δ)) ?_).trans
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (abs_nonneg _) hδ)
  · exact ae_of_all _ (fun p => by
      rw [← mul_sub,Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ |B| *(δ*(weight p.2.1*weight p.2.2)) :=
          mul_le_mul ((hB _).trans (le_abs_self B)) (he _) (abs_nonneg _) (abs_nonneg _)
        _ = _ := by ring)

theorem gaussian_weighted_integral_tendsto
    {μ : ℕ → Measure (X × (Velocity × Velocity))} {ν : Measure (X × (Velocity × Velocity))}
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hμ : ∀ᶠ n in atTop,
      (∫⁻ p, ENNReal.ofReal (weight p.2.1*weight p.2.2) ∂μ n) ≤ ENNReal.ofReal C)
    (hν : (∫⁻ p, ENNReal.ofReal (weight p.2.1*weight p.2.2) ∂ν) ≤ ENNReal.ofReal D)
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    (hcompact : ∀ g : C(Velocity × Velocity, ℝ), HasCompactSupport g →
      Tendsto (fun n => ∫ p, θ p.1*g p.2 ∂μ n) atTop (𝓝 (∫ p, θ p.1*g p.2 ∂ν)))
    (f : C(Velocity × Velocity, ℝ)) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ p, |f p| ≤ L*(1+‖p.1‖+‖p.2‖)) :
    Tendsto (fun n => ∫ p, θ p.1*f p.2 ∂μ n) atTop (𝓝 (∫ p, θ p.1*f p.2 ∂ν)) := by
  have hfg (p) : |f p| ≤ (3*L)*(weight p.1*weight p.2) :=
    (hf p).trans ((mul_le_mul_of_nonneg_left (pair_weight_le p.1 p.2) hL).trans_eq (by ring))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(3*(|B| *(C+D)+1))
  have hden : 0 < 3*(|B| *(C+D)+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ*(3*(|B| *(C+D)+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨g,hg,hfgerr⟩ := CollisionCompactness.exists_compact_gaussian_approximation f hL hf hδ
  have hgconv := Metric.tendsto_nhds.mp (hcompact g hg) (ε/3) (by positivity)
  filter_upwards [hμ,hgconv] with n hn hng
  rw [Real.dist_eq] at hng ⊢
  have hnerr := weighted_gaussian_error (μ n) hC hn hθ hB f.continuous.measurable g.continuous.measurable hδ.le hfg hfgerr
  have hνerr := weighted_gaussian_error ν hD hν hθ hB f.continuous.measurable g.continuous.measurable hδ.le hfg hfgerr
  have ht₁ := abs_sub_le (∫ p, θ p.1*f p.2 ∂μ n) (∫ p, θ p.1*g p.2 ∂μ n)
    (∫ p, θ p.1*f p.2 ∂ν)
  have ht₂ := abs_sub_le (∫ p, θ p.1*g p.2 ∂μ n) (∫ p, θ p.1*g p.2 ∂ν)
    (∫ p, θ p.1*f p.2 ∂ν)
  rw [abs_sub_comm] at hnerr
  nlinarith

end BoltzmannNonuniqueness.Compactness

end

end OAI
