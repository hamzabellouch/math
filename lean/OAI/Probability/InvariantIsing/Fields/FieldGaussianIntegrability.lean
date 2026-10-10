import OAI.Probability.InvariantIsing.Fields.FieldGaussianTransformLaw
import OAI.Probability.IsingPerceptron.GaussianIntegration

namespace OAI

/-! The weighted integrability needed for covariance differentiation of
the linearly growing scalar Ising recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma field_exp_mul_linear_integrable (v : ℝ≥0) (z ζ : ℝ) {F G : ℝ → ℝ}
    (hF : Measurable F) (hFg : HasLinearGrowth F)
    (hG : Measurable G) (hGg : HasLinearGrowth G) :
    Integrable (fun u => Real.exp (ζ * F u) * G u) (gaussianReal z v) := by
  obtain ⟨CF, LF, _hCF, _hLF, hFb⟩ := hFg
  obtain ⟨CG, LG, hCG, hLG, hGb⟩ := hGg
  have hi := ((gaussianReal_exponentialNormMoments z v) (|ζ| * LF + 1)).const_mul
    ((CG + LG) * Real.exp (|ζ| * CF))
  apply hi.mono' ((hF.const_mul ζ).exp.mul hG).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  have he1 : 1 ≤ Real.exp ‖u‖ := Real.one_le_exp (norm_nonneg u)
  have hen : ‖u‖ ≤ Real.exp ‖u‖ := by linarith [Real.add_one_le_exp ‖u‖]
  have hGbound : |G u| ≤ (CG + LG) * Real.exp ‖u‖ := calc
    _ ≤ CG + LG * ‖u‖ := hGb u
    _ ≤ CG * Real.exp ‖u‖ + LG * Real.exp ‖u‖ :=
      add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he1 hCG)
        (mul_le_mul_of_nonneg_left hen hLG)
    _ = _ := by ring
  have hFbound : ζ * F u ≤ |ζ| * (CF + LF * ‖u‖) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb u) (abs_nonneg ζ))
  change ‖Real.exp (ζ * F u) * G u‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (|ζ| * (CF + LF * ‖u‖)) * ((CG + LG) * Real.exp ‖u‖) :=
      mul_le_mul (Real.exp_le_exp.mpr hFbound) hGbound (abs_nonneg _) (Real.exp_pos _).le
    _ = ((CG + LG) * Real.exp (|ζ| * CF)) * Real.exp ((|ζ| * LF + 1) * ‖u‖) := by
      rw [show |ζ| * (CF + LF * ‖u‖) = |ζ| * CF + (|ζ| * LF) * ‖u‖ by ring,
        Real.exp_add, show (|ζ| * LF + 1) * ‖u‖ = (|ζ| * LF) * ‖u‖ + ‖u‖ by ring,
        Real.exp_add]
      ring

lemma field_gaussian_tilted_ibp {F D DD : ℝ → ℝ}
    (hF : Measurable F) (hFg : HasLinearGrowth F)
    (hD : Measurable D) (hDD : Measurable DD)
    {K C : ℝ} (hDb : ∀ u, |D u| ≤ K) (hDDb : ∀ u, |DD u| ≤ C)
    (hd : ∀ u, HasDerivAt F (D u) u) (hdd : ∀ u, HasDerivAt D (DD u) u)
    (r ζ z : ℝ) :
    (∫ u, u * D (z + r * u)
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) =
      r * (∫ u, DD (z + r * u) + ζ * (D (z + r * u)) ^ 2
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  let U := fun u => F (z + r * u)
  let A := fun u => Real.exp (ζ * U u) * D (z + r * u)
  let DA := fun u => r * (Real.exp (ζ * U u) *
    (DD (z + r * u) + ζ * (D (z + r * u)) ^ 2))
  have hUm : Measurable U := hF.comp (measurable_const.add (measurable_id.const_mul r))
  have hUg : HasLinearGrowth U := (hFg.add_left z).scale_argument r
  have hw := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hUm hUg ζ
  have hA : Integrable A (gaussianReal 0 1) := by
    exact hw.mul_bdd (hD.comp (measurable_const.add (measurable_id.const_mul r))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using hDb (z + r * u)))
  have hDA : Integrable DA (gaussianReal 0 1) := by
    apply Integrable.const_mul
    exact hw.mul_bdd
      ((hDD.comp (measurable_const.add (measurable_id.const_mul r))).add
        (((hD.comp (measurable_const.add (measurable_id.const_mul r))).pow_const 2).const_mul ζ)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => by
        simpa only [Real.norm_eq_abs] using bounded_generator hDb hDDb ζ (z + r * u)))
  have hAD (u : ℝ) : HasDerivAt A (DA u) u := by
    have harg : HasDerivAt (fun y => z + r * y) r u := by
      convert ((hasDerivAt_id u).const_mul r).const_add z using 1 <;>
        first | rfl | simp only [mul_one]
    have h1 : HasDerivAt (fun y => F (z + r * y)) (D (z + r * u) * r) u :=
      (hd (z + r * u)).comp u harg
    have h2 : HasDerivAt (fun y => D (z + r * y)) (DD (z + r * u) * r) u :=
      (hdd (z + r * u)).comp u harg
    convert ((h1.const_mul ζ).exp).mul h2 using 1
    dsimp only [A, DA, U]
    ring
  have hGm : Measurable (fun u => u * D (z + r * u)) :=
    measurable_id.mul (hD.comp (measurable_const.add (measurable_id.const_mul r)))
  have hGg : HasLinearGrowth (fun u => u * D (z + r * u)) := by
    refine ⟨0, |K|, le_rfl, abs_nonneg K, fun u => ?_⟩
    rw [abs_mul, Real.norm_eq_abs, zero_add]
    calc
      |u| * |D (z + r * u)| ≤ |u| * |K| :=
        mul_le_mul_of_nonneg_left ((hDb _).trans (le_abs_self K)) (abs_nonneg u)
      _ = _ := mul_comm _ _
  have hXA : Integrable (fun u => u * A u) (gaussianReal 0 1) := by
    convert field_exp_mul_linear_integrable 1 0 ζ hUm hUg hGm hGg using 1
    funext u
    dsimp only [A]
    ring
  have hibp := gaussian_integration_by_parts hAD hA hDA hXA
  simp only [integral_tilted_eq_div]
  have hnum : (∫ u, Real.exp (ζ * F (z + r * u)) * (u * D (z + r * u)) ∂gaussianReal 0 1) =
      r * ∫ u, Real.exp (ζ * F (z + r * u)) *
        (DD (z + r * u) + ζ * (D (z + r * u)) ^ 2) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]
    convert hibp using 1
    congr 1
    funext u
    dsimp only [A, DA, U]
    ring
  rw [hnum]
  ring

end InvariantIsing

end

end OAI
