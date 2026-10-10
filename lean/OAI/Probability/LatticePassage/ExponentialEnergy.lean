import OAI.Probability.LatticePassage.ResamplingTransform

namespace OAI

namespace CompanionFPP
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
  have hswap := lintegral_map (μ := P) hH (exchangeCoordinate_preserving μ i).measurable
  rw [(exchangeCoordinate_preserving μ i).map_eq] at hswap
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
    rw [exchangeCoordinate_resample, exchangeCoordinate_first]
  change (∫⁻ z, H z ∂P) + _ = 2*(∫⁻ z, H z ∂P)
  rw [hb, two_mul]

theorem finite_exponential_forward_energy (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e : ↥(localEdges x R), ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
      ENNReal.ofReal (exp (a*finitePassageTime x y R z.1) *
        (exp (a*max (finitePassageTime x y R (Function.update z.1 e (z.2 e))-
          finitePassageTime x y R z.1) 0/2)-1)^2)
      ∂(Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)).prod
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))) ≤
    (ENNReal.ofReal (2*a^2)*R) *
      ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime x y R v))
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1) := by
  classical
  let P := Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)
  let F := finitePassageTime x y R
  let K := fun v e u => ENNReal.ofReal ((exp (a*max (F (Function.update v e u)-F v) 0/2)-1)^2)
  have he : ∀ e : ↥(localEdges x R),
      (∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
        ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) =
      ∫⁻ v, ENNReal.ofReal (exp (a*F v))*(∫⁻ u, K v e u ∂expMeasure 1) ∂P := by
    intro e
    rw [lintegral_prod _ (by dsimp [K,F]; fun_prop)]
    apply lintegral_congr
    intro v
    dsimp only
    rw [lintegral_const_mul _ (show Measurable (fun w : LocalCoordinates x R => K v e (w e)) from by dsimp [K,F]; fun_prop)]
    congr 1
    have h := lintegral_map (μ := P) (show Measurable (K v e) from by dsimp [K,F]; fun_prop)
      (measurable_pi_apply e)
    rw [(measurePreserving_eval (fun _ : ↥(localEdges x R) => expMeasure 1) e).map_eq] at h
    exact h.symm
  simp_rw [ENNReal.ofReal_mul (exp_pos _).le]
  change (∑ e, ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
    ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) ≤ _
  simp_rw [he]
  rw [← lintegral_finsetSum _ (fun e _ => by dsimp [K,F]; fun_prop)]
  simp_rw [← mul_sum]
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal (exp (a*F v))*(ENNReal.ofReal (2*a^2)*R) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [finite_coordinates_nonnegative x R] with v hv
      gcongr
      exact finite_upward_exponential_sum x y R hR v hv a ha
    _ = _ := by
      simp_rw [mul_comm _ (ENNReal.ofReal (2*a^2)*R)]
      exact lintegral_const_mul _ (by dsimp [F]; fun_prop)

theorem finite_exponential_resampling_energy (x y : Vertex) (R : ℕ)
    (hR : latticeDistance x y < R) (a : ℝ) (ha : |a| ≤ 1/2) :
    (∑ e : ↥(localEdges x R), ∫⁻ z : LocalCoordinates x R × LocalCoordinates x R,
      ENNReal.ofReal ((exp (a*finitePassageTime x y R (Function.update z.1 e (z.2 e))/2) -
        exp (a*finitePassageTime x y R z.1/2))^2)
      ∂(Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)).prod
        (Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1))) ≤
    (ENNReal.ofReal (4*a^2)*R) *
      ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime x y R v))
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1) := by
  classical
  simp_rw [exponential_resampling_energy_split (expMeasure 1) (finitePassageTime x y R)
    (measurable_finitePassageTime x y R), ← mul_sum]
  have h := finite_exponential_forward_energy x y R hR a ha
  calc
    _ ≤ 2*((ENNReal.ofReal (2*a^2)*R)*
      ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime x y R v))
        ∂Measure.pi (fun _ : ↥(localEdges x R) => expMeasure 1)) := by
      gcongr
    _ = _ := by
      have he : (2 : ℝ≥0∞)*ENNReal.ofReal (2*a^2) = ENNReal.ofReal (4*a^2) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      simp only [← mul_assoc, he]

end CompanionFPP

end OAI
