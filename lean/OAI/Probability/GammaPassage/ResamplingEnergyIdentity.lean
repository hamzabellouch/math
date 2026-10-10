import OAI.Probability.LatticePassage.ResamplingSymmetry

namespace OAI

namespace GammaFPP.EnergyIdentity
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma exponential_square_difference (a b t : ℝ) :
    (exp (t*b/2)-exp (t*a/2))^2 = exp (t*a)*(exp (t*(b-a)/2)-1)^2 := by
  have h₁ : exp (t*b/2) = exp (t*a/2)*exp (t*(b-a)/2) := by
    rw [← exp_add]
    congr 1
    ring
  have h₂ : exp (t*a) = exp (t*a/2)^2 := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  rw [h₁, h₂]
  ring

lemma exponential_square_difference_split (a b t : ℝ) :
    (exp (t*b/2)-exp (t*a/2))^2 =
      exp (t*a)*(exp (t*max (b-a) 0/2)-1)^2 +
      exp (t*b)*(exp (t*max (a-b) 0/2)-1)^2 := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    simp only [mul_zero, zero_div, exp_zero, sub_self, zero_pow (by omega : 2 ≠ 0),
      mul_zero, add_zero]
    exact exponential_square_difference a b t
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    simp only [mul_zero, zero_div, exp_zero, sub_self, zero_pow (by omega : 2 ≠ 0),
      mul_zero, zero_add]
    rw [sub_sq_comm]
    exact exponential_square_difference b a t

/-- Exchanging a coordinate identifies the backward exponential energy with
the forward one. The weighting belongs to the old environment in each term. -/
theorem exponential_resampling_energy_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (i : ι) (a : ℝ) :
    (∫⁻ z : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      ((exp (a*f (Function.update z.1 i (z.2 i))/2)-exp (a*f z.1/2))^2)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) =
    2 * (∫⁻ z : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      (exp (a*f z.1)*(exp (a*max (f (Function.update z.1 i (z.2 i))-f z.1) 0/2)-1)^2)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  let P := (Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))
  let H := fun z : (ι → ℝ) × (ι → ℝ) => ENNReal.ofReal
    (exp (a*f z.1)*(exp (a*max (f (Function.update z.1 i (z.2 i))-f z.1) 0/2)-1)^2)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hswap := lintegral_map (μ := P) hH (CompanionFPP.exchangeCoordinate_preserving μ i).measurable
  rw [(CompanionFPP.exchangeCoordinate_preserving μ i).map_eq] at hswap
  have he (x y : ℝ) : ENNReal.ofReal ((exp (a*y/2)-exp (a*x/2))^2) =
      ENNReal.ofReal (exp (a*x)*(exp (a*max (y-x) 0/2)-1)^2) +
      ENNReal.ofReal (exp (a*y)*(exp (a*max (x-y) 0/2)-1)^2) := by
    rw [exponential_square_difference_split, ENNReal.ofReal_add (by positivity) (by positivity)]
  simp_rw [he]
  rw [lintegral_add_left (by fun_prop)]
  have hb : (∫⁻ z, ENNReal.ofReal
      (exp (a*f (Function.update z.1 i (z.2 i)))*
        (exp (a*max (f z.1-f (Function.update z.1 i (z.2 i))) 0/2)-1)^2) ∂P) =
      ∫⁻ z, H z ∂P := by
    rw [hswap]
    apply lintegral_congr
    intro z
    dsimp [H]
    rw [CompanionFPP.exchangeCoordinate_resample, CompanionFPP.exchangeCoordinate_first]
  change (∫⁻ z, H z ∂P) + _ = 2*(∫⁻ z, H z ∂P)
  rw [hb, two_mul]

end GammaFPP.EnergyIdentity

end OAI
