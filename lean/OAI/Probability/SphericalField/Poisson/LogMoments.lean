import Mathlib
import OAI.Probability.SphericalField.Poisson.StableMoments

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

attribute [fun_prop] stablePoissonTotal_measurable
lemma stablePoisson_palm_laplace' {b r t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hr : b < r) (ht : 0 < t) :
    (∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))
      ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      ENNReal.ofReal (b*t^(b-r)*Real.Gamma (r-b)*Real.exp (-Real.Gamma (1-b)*t^b)) := by
  have hh := stablePoisson_palm_laplace hb hb1 hr ht
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top] at hh
  exact hh

lemma stablePoisson_palm_mellin_mul {a b r : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) (hr : b < r) :
    (∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (r-a)) =
      ENNReal.ofReal (Real.Gamma (r-b)*Real.Gamma (1-a/b)*
        (Real.Gamma (1-b))^(a/b-1)) := by
  let P := poissonRandomMeasureLaw (stableLogIntensity b)
  let c := Real.Gamma (1-b)
  have hc : 0 < c := Real.Gamma_pos_of_pos (by linarith)
  have hra : 0 < r-a := by linarith
  let K := fun (η : Measure ℝ) (t : ℝ) => stableJumpMomentE r η*
    ENNReal.ofReal (t^(r-a-1)*Real.exp (-t*stablePoissonTotal η))
  have hm : Measurable (Function.uncurry K) := by dsimp [K]; fun_prop
  have hgamma : ∀ᵐ η ∂P,
      stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))*ENNReal.ofReal (Real.Gamma (r-a)) =
        ∫⁻ t : ℝ in Ioi 0, K η t := by
    filter_upwards [stablePoissonTotal_pos hb hb1] with η hη
    dsimp [K]
    rw [lintegral_const_mul _ (by fun_prop),gamma_lintegral_positive_scale hra hη,
      show -(r-a) = a-r by ring,ENNReal.ofReal_mul (Real.rpow_nonneg hη.le _),mul_assoc]
  have hinner (t : ℝ) (ht : 0 < t) : (∫⁻ η, K η t ∂P) =
      ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-a-1)*Real.exp (-c*t^b)) := by
    have hfac (η : Measure ℝ) : K η t = ENNReal.ofReal (t^(r-a-1))*
        (stableJumpMomentE r η*ENNReal.ofReal (Real.exp (-t*stablePoissonTotal η))) := by
      dsimp [K]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
      ring
    simp_rw [hfac]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,stablePoisson_palm_laplace' hb hb1 hr ht,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]
    congr 1
    have hp : t^(r-a-1)*t^(b-r) = t^(b-a-1) := by rw [← Real.rpow_add ht]; congr 1; ring
    calc
      _ = b*Real.Gamma (r-b)*(t^(r-a-1)*t^(b-r))*Real.exp (-c*t^b) := by dsimp [c]; ring
      _ = _ := by rw [hp]; ring
  calc
    _ = ∫⁻ η, stableJumpMomentE r η*ENNReal.ofReal (stablePoissonTotal η^(a-r))*
        ENNReal.ofReal (Real.Gamma (r-a)) ∂P :=
      (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ η, (∫⁻ t : ℝ in Ioi 0, K η t) ∂P := lintegral_congr_ae hgamma
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ η, K η t ∂P := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (b*Real.Gamma (r-b))*ENNReal.ofReal (t^(b-a-1)*Real.exp (-c*t^b)) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hinner t ht
    _ = ENNReal.ofReal (b*Real.Gamma (r-b))*
        ENNReal.ofReal (c^(-((b-a-1)+1)/b)*(1/b)*Real.Gamma (((b-a-1)+1)/b)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,gamma_lintegral_rpow_scale (by linarith) hb hc]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (mul_nonneg hb.le (Real.Gamma_pos_of_pos (sub_pos.mpr hr)).le)]
      congr 1
      rw [show -((b-a-1)+1)/b = a/b-1 by field_simp; ring,
        show ((b-a-1)+1)/b = 1-a/b by field_simp; ring]
      dsimp [c]
      field_simp

lemma stablePoissonTotal_rpow_lintegral_mul {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) :
    (∫⁻ η, ENNReal.ofReal (stablePoissonTotal η^a)
      ∂poissonRandomMeasureLaw (stableLogIntensity b))*ENNReal.ofReal (Real.Gamma (1-a)) =
      ENNReal.ofReal (Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)) := by
  have he := stablePoisson_palm_mellin_mul hb hb1 ha hb1
  have hrew : (fun η => stableJumpMomentE 1 η*ENNReal.ofReal (stablePoissonTotal η^(a-1))) =ᵐ[
      poissonRandomMeasureLaw (stableLogIntensity b)] (fun η => ENNReal.ofReal (stablePoissonTotal η^a)) := by
    filter_upwards [stablePoisson_total_finite hb hb1,stablePoissonTotal_pos hb hb1] with η hη hpos
    have hJ : stableJumpMomentE 1 η = ENNReal.ofReal (stablePoissonTotal η) := by
      simp only [stableJumpMomentE,one_mul,stablePoissonTotal]
      exact (ENNReal.ofReal_toReal hη).symm
    rw [hJ,← ENNReal.ofReal_mul hpos.le]
    congr 1
    calc
      _ = stablePoissonTotal η^((1:ℝ)+(a-1)) := by rw [Real.rpow_add hpos,Real.rpow_one]
      _ = _ := by congr 1; ring
  rw [lintegral_congr_ae hrew] at he
  rw [he]
  congr 1
  have hc : 0 < Real.Gamma (1-b) := Real.Gamma_pos_of_pos (by linarith)
  calc
    _ = Real.Gamma (1-a/b)*((Real.Gamma (1-b))^((1:ℝ)+(a/b-1))) := by
      rw [Real.rpow_add hc,Real.rpow_one]; ring
    _ = _ := by congr 2; ring

lemma stablePoissonTotal_rpow_integral {a b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (ha : a < b) :
    (∫ η, stablePoissonTotal η^a ∂poissonRandomMeasureLaw (stableLogIntensity b)) =
      Real.Gamma (1-a/b)*(Real.Gamma (1-b))^(a/b)/Real.Gamma (1-a) := by
  have hga : 0 < Real.Gamma (1-a) := Real.Gamma_pos_of_pos (by linarith)
  have hgab : 0 < Real.Gamma (1-a/b) := Real.Gamma_pos_of_pos (by
    have : a/b < 1 := (div_lt_one hb).mpr ha
    linarith)
  have hi := stablePoissonTotal_rpow_integrable hb hb1 ha
  have hn : ∀ η : Measure ℝ, 0 ≤ stablePoissonTotal η^a := fun η =>
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have he := stablePoissonTotal_rpow_lintegral_mul hb hb1 ha
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)] at he
  have her := congrArg ENNReal.toReal he
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal hga.le,ENNReal.toReal_ofReal
      (mul_nonneg hgab.le (Real.rpow_nonneg (Real.Gamma_pos_of_pos (by linarith : 0 < 1-b)).le _))] at her
  exact (eq_div_iff hga.ne').mpr her

def stableMassKernel : Kernel (Measure ℝ) ℝ where
  toFun η := normalizedMeasure (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)))
  measurable' := normalizedMeasure_measurable.comp (measurable_measure_withDensity_fixed (by fun_prop))

instance stableMassKernel_finite : IsFiniteKernel stableMassKernel := by
  refine ⟨1, by simp, ?_⟩
  intro η
  change (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ)⁻¹ *
    (η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ) ≤ 1
  exact ENNReal.inv_mul_le_one _

def stableCountKernel : Kernel (Measure ℝ) ℝ :=
  stableMassKernel.withDensity (fun η x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x)))

instance stableCountKernel_sFinite : IsSFiniteKernel stableCountKernel :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

lemma stableCountKernel_eq (η : Measure ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) :
    stableCountKernel η = η := by
  rw [stableCountKernel,Kernel.withDensity_apply _ (by fun_prop : Measurable
    (Function.uncurry (fun η x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x)))))]
  change (((η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ)⁻¹) •
    η.withDensity (fun x => ENNReal.ofReal (Real.exp x))).withDensity
      (fun x => ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) = η
  have hmass : η.withDensity (fun x => ENNReal.ofReal (Real.exp x)) univ =
      ENNReal.ofReal (stablePoissonTotal η) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ENNReal.ofReal_toReal (by simpa [stableJumpMomentE] using hf)).symm
  rw [hmass,withDensity_smul_measure,← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have hd : (fun x => ENNReal.ofReal (Real.exp x)*
      ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) =
      (fun _ : ℝ => ENNReal.ofReal (stablePoissonTotal η)) := by
    funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [Real.exp_neg]
    field_simp
  change (ENNReal.ofReal (stablePoissonTotal η))⁻¹ • η.withDensity
    (fun x => ENNReal.ofReal (Real.exp x)*ENNReal.ofReal (stablePoissonTotal η*Real.exp (-x))) = η
  rw [hd,withDensity_const,smul_smul,ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,one_smul]

lemma stableJumpMomentE_one_add_dirac (x : ℝ) (η : Measure ℝ) :
    stableJumpMomentE 1 (Measure.dirac x+η) = ENNReal.ofReal (Real.exp x)+stableJumpMomentE 1 η := by
  simp [stableJumpMomentE,lintegral_add_measure]

lemma stableCountKernel_add_dirac (η : Measure ℝ) (x : ℝ)
    (hf : stableJumpMomentE 1 η ≠ ⊤) (hp : 0 < stablePoissonTotal η) :
    stableCountKernel (Measure.dirac x+η) = Measure.dirac x+η := by
  apply stableCountKernel_eq
  · rw [stableJumpMomentE_one_add_dirac]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hf⟩
  · rw [stablePoissonTotal_add_dirac x η (by simpa [stableJumpMomentE] using hf)]
    positivity

end SphericalPerceptron
end
end
end

end OAI
