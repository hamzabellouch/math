import OAI.Probability.SLE.ChartMeasurability
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

/-! The inverse-Loewner derivative is measurable in the original stopped
past. Difference quotients stay inside the upper half-plane. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def halfPlaneRealShift (z : upperHalfPlane) (a : ℝ) : upperHalfPlane :=
  ⟨(z:ℂ)+(a:ℂ),by simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,
    Complex.ofReal_im,add_zero] using z.property⟩

lemma halfPlaneRealShift_continuous (a : ℝ) : Continuous (fun z => halfPlaneRealShift z a) :=
  (continuous_subtype_val.add continuous_const).subtype_mk _

theorem measurable_halfPlane_derivative
    {Ω : Type*} [MeasurableSpace Ω] (J : Ω → ℂ → ℂ)
    (hJ : Measurable (fun p : Ω × upperHalfPlane => J p.1 p.2))
    (hd : ∀ ω (z : upperHalfPlane), DifferentiableAt ℂ (J ω) z) :
    Measurable (fun p : Ω × upperHalfPlane => deriv (J p.1) p.2) := by
  let a : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  let Q : ℕ → Ω × upperHalfPlane → ℂ := fun n p =>
    (a n:ℂ)⁻¹*(J p.1 (halfPlaneRealShift p.2 (a n))-J p.1 p.2)
  have hQ (n : ℕ) : Measurable (Q n) := by
    exact measurable_const.mul ((hJ.comp (measurable_fst.prodMk
      ((halfPlaneRealShift_continuous (a n)).measurable.comp measurable_snd))).sub hJ)
  apply measurable_of_tendsto_metrizable hQ
  apply tendsto_pi_nhds.mpr
  intro p
  have ha : Tendsto (fun n => (a n:ℂ)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [a,Complex.ofReal_zero,Function.comp_def] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · exact Eventually.of_forall (fun n => by
        simp only [mem_compl_iff,mem_singleton_iff,Complex.ofReal_eq_zero]
        dsimp only [a]
        positivity)
  have hh := (hd p.1 p.2).hasDerivAt.tendsto_slope_zero.comp ha
  simpa only [Q,halfPlaneRealShift,smul_eq_mul,Function.comp_def] using hh

theorem source_stopped_inverse_derivative_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace.prod inferInstance]
      (fun p : Ω × upperHalfPlane =>
        deriv (F p.1 (τ p.1)) ((p.2:ℂ)+(Real.sqrt κ*B (τ p.1) p.1:ℝ))) := by
  let J : Ω → ℂ → ℂ := fun ω z => F ω (τ ω) (z+(Real.sqrt κ*B (τ ω) ω:ℝ))
  have hmJ : Measurable[hτ.measurableSpace.prod inferInstance]
      (fun p : Ω × upperHalfPlane => J p.1 p.2) :=
    continuous_eval.measurable.comp
      ((source_stopped_inversePath_measurable B hm hc κ γ G F hw τ hτ).comp
        measurable_fst |>.prodMk measurable_snd)
  have hd (ω : Ω) (z : upperHalfPlane) :
      HasDerivAt (J ω) (deriv (F ω (τ ω)) ((z:ℂ)+(Real.sqrt κ*B (τ ω) ω:ℝ))) z := by
    have hz : (z:ℂ)+(Real.sqrt κ*B (τ ω) ω:ℝ) ∈ upperHalfPlane := by
      simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
        using z.property
    simpa only [J,Function.comp_def,id_eq,mul_one] using
      (((hw ω).2.2.2.2.1 (τ ω)).differentiableAt
        (isOpen_upperHalfPlane.mem_nhds hz)).hasDerivAt.comp (z:ℂ)
        ((hasDerivAt_id (z:ℂ)).add_const ((Real.sqrt κ*B (τ ω) ω:ℝ):ℂ))
  have he (p : Ω × upperHalfPlane) := (hd p.1 p.2).deriv
  simpa only [he] using @measurable_halfPlane_derivative Ω hτ.measurableSpace J hmJ
    (fun ω z => (hd ω z).differentiableAt)

end SLEExactGauge

end

end OAI
