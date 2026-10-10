import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationEndpoint
import OAI.Probability.InvariantIsing.Fields.FieldGaussianIntegrability

namespace OAI

/-! Gaussian integration by parts for the bounded continuation test,
with the actual linearly growing scalar field as tilted potential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma magnetic_gaussian_tilted_test_ibp {F M A B : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (hM : Measurable M) (hA : Measurable A) (hB : Measurable B)
    {K C D : ℝ} (bM : ∀ x, |M x| ≤ K) (bA : ∀ x, |A x| ≤ C)
    (bB : ∀ x, |B x| ≤ D) (dF : ∀ x, HasDerivAt F (M x) x)
    (dA : ∀ x, HasDerivAt A (B x) x) (r ζ z : ℝ) :
    (∫ u, u * A (z + r * u)
      ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) =
      r * (∫ u, B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F (z + r * u))) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (bA 0)
  let U := fun u => F (z + r * u)
  let V := fun u => Real.exp (ζ * U u) * A (z + r * u)
  let DV := fun u => r * (Real.exp (ζ * U u) *
    (B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)))
  have hUm : Measurable U := hF.comp (by fun_prop)
  have hUg : HasLinearGrowth U := (hG.add_left z).scale_argument r
  have hw := integrable_exp_of_linearGrowth (gaussianReal 0 1)
    (gaussianReal_exponentialNormMoments 0 1) hUm hUg ζ
  have bgen (x : ℝ) : |B x + ζ * A x * M x| ≤ D + |ζ| * C * K := by
    refine (abs_add_le _ _).trans (add_le_add (bB x) ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (bA x) (abs_nonneg ζ))
      (bM x) (abs_nonneg _) (mul_nonneg (abs_nonneg ζ) hC)
  have hV : Integrable V (gaussianReal 0 1) :=
    hw.mul_bdd (hA.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        simpa only [Real.norm_eq_abs] using bA (z + r * u))
  have hDV : Integrable DV (gaussianReal 0 1) := by
    apply Integrable.const_mul
    exact hw.mul_bdd
      ((hB.comp (by fun_prop)).add
        (((hA.comp (by fun_prop)).const_mul ζ).mul (hM.comp (by fun_prop)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        simpa only [Real.norm_eq_abs] using bgen (z + r * u))
  have hderiv (u : ℝ) : HasDerivAt V (DV u) u := by
    have hs : HasDerivAt (fun x : ℝ => z + r * x) r u := by
      convert ((hasDerivAt_id u).const_mul r).const_add z using 1 <;> first | rfl | simp
    have hf : HasDerivAt (fun x => F (z + r * x)) (M (z + r * u) * r) u :=
      (dF (z + r * u)).comp u hs
    have ha : HasDerivAt (fun x => A (z + r * x)) (B (z + r * u) * r) u :=
      (dA (z + r * u)).comp u hs
    convert ((hf.const_mul ζ).exp).mul ha using 1
    dsimp only [V, DV, U]
    ring
  have hlinear : HasLinearGrowth (fun u => u * A (z + r * u)) := by
    refine ⟨0, C, le_rfl, hC, fun u => ?_⟩
    rw [abs_mul, Real.norm_eq_abs, zero_add]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (bA (z + r * u)) (abs_nonneg u)
  have hUV : Integrable (fun u => u * V u) (gaussianReal 0 1) := by
    convert field_exp_mul_linear_integrable 1 0 ζ hUm hUg
      (measurable_id.mul (hA.comp (by fun_prop))) hlinear using 1
    funext u
    dsimp only [V, Pi.mul_apply, Function.comp_apply, id_eq]
    ring
  have hibp := gaussian_integration_by_parts hderiv hV hDV hUV
  simp only [integral_tilted_eq_div]
  have hn : (∫ u, Real.exp (ζ * F (z + r * u)) * (u * A (z + r * u))
      ∂gaussianReal 0 1) =
      r * ∫ u, Real.exp (ζ * F (z + r * u)) *
        (B (z + r * u) + ζ * A (z + r * u) * M (z + r * u)) ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]
    convert hibp using 1
    congr 1
    funext u
    dsimp only [V, DV, U]
    ring
  rw [hn]
  ring

end InvariantIsing

end

end OAI
