import Mathlib
import OAI.Probability.SKBarriers.Gaussian.SmoothedObservable
import OAI.Probability.SKBarriers.Gaussian.FiberTiltedTent

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarWindow_contDiff {g : ℝ → ℝ} (hg : Continuous g) (h : ℝ) :
    ContDiff ℝ 1 (scalarWindow g h) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (scalarWindow_hasDerivAt hg h x).differentiableAt,?_⟩
  have he : deriv (scalarWindow g h)=scalarWindowDerivative g h := funext (fun x => (scalarWindow_hasDerivAt hg h x).deriv)
  rw [he]
  exact scalarWindowDerivative_continuous hg h

theorem scalarWindow_comp_growth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0} (hb : ∀ x, |g x|≤B)
    {h : ℝ} (hh : 0<h) (L : E →L[ℝ] ℝ) :
    HasExpGrowth (fun z => scalarWindow g h (L z)) ∧
      HasExpGrowth (fderiv ℝ (fun z => scalarWindow g h (L z))) := by
  constructor
  · exact HasExpGrowth.of_bounded B.coe_nonneg (fun z => by simpa only [Real.norm_eq_abs] using scalarWindow_bound hg hb hh (L z))
  · apply HasExpGrowth.of_bounded (show 0≤(2*(B:ℝ)/h)*‖L‖ by positivity)
    intro z
    have H := ((scalarWindow_hasDerivAt hg h (L z)).hasFDerivAt.comp z L.hasFDerivAt).fderiv
    change ‖fderiv ℝ (scalarWindow g h ∘ ⇑L) z‖≤_
    rw [H]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg L)
    rw [ContinuousLinearMap.norm_toSpanSingleton,Real.norm_eq_abs]
    exact scalarWindowDerivative_bound hb hh (L z)

theorem fiberGaussian_tent_error_C1 (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g) (hg : HasExpGrowth g)
    (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (a : Fin n → ℝ)
    (hinv : TranslationInvariant g (coordinateVector n a))
    (ε₁ ε₂ : ℝ) (hb : ∀ z, |g z|≤1)
    (h₁ : ∀ z, |fderiv ℝ V z (coordinateVector n a)|≤ε₁)
    (h₂ : ∀ z, |fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)|≤ε₂) :
    |(∫ z, (coordinateLinear n a z)^2*g z ∂(fiberGaussian n x).tilted V)-
      (∑ i, (a i)^2)*(∫ z, g z ∂(fiberGaussian n x).tilted V)|≤ε₁^2+ε₂ := by
  let := fiberGaussian_tilted_probability n V hV x
  rw [fiberGaussian_tilted_quadratic_invariant n V g hV hc hg hdg x a hinv,add_sub_cancel_left]
  have H := norm_integral_le_of_norm_le_const (μ := (fiberGaussian n x).tilted V)
    (f := fun z => g z*((fderiv ℝ V z (coordinateVector n a))^2+
      fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)))
    (C := ε₁^2+ε₂) (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      have he : |(fderiv ℝ V z (coordinateVector n a))^2+
          fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)|≤ε₁^2+ε₂ := by
        apply (abs_add_le _ _).trans
        apply add_le_add _ (h₂ z)
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (h₁ z) 2
      exact (mul_le_mul (hb z) he (abs_nonneg _) zero_le_one).trans_eq (one_mul _)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

theorem fiberGaussian_tent_error_lipschitz (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g)
    (hb : ∀ y, |g y|≤1) (L : ParameterSpace n →L[ℝ] ℝ)
    (x : ℝ) (a : Fin n → ℝ) (hinv : L (coordinateVector n a)=0) (ε₁ ε₂ : ℝ)
    (h₁ : ∀ z, |fderiv ℝ V z (coordinateVector n a)|≤ε₁)
    (h₂ : ∀ z, |fderiv ℝ (fderiv ℝ V) z (coordinateVector n a) (coordinateVector n a)|≤ε₂) :
    |(∫ z, (coordinateLinear n a z)^2*g (L z) ∂(fiberGaussian n x).tilted V)-
      (∑ i, (a i)^2)*(∫ z, g (L z) ∂(fiberGaussian n x).tilted V)|≤ε₁^2+ε₂ := by
  let μ := (fiberGaussian n x).tilted V
  let := fiberGaussian_tilted_probability n V hV x
  let h : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hh (k) : 0<h k := by dsimp [h]; positivity
  have ht : Tendsto h atTop (𝓝 0) := by simpa using tendsto_one_div_add_atTop_nhds_zero_nat
  let G : ℕ → ParameterSpace n → ℝ := fun k z => scalarWindow g (h k) (L z)
  have hc (k) : ContDiff ℝ 1 (G k) := (scalarWindow_contDiff hg.continuous (h k)).comp L.contDiff
  have hb' (k z) : |G k z|≤1 := scalarWindow_bound hg.continuous (B:=1) hb (hh k) (L z)
  have hlim (z) : Tendsto (fun k => G k z) atTop (𝓝 (g (L z))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun k => g (L z)-(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.sub (ht.const_mul (M:ℝ)))
      (show Tendsto (fun k => g (L z)+(M:ℝ)*h k) atTop (𝓝 (g (L z))) by simpa using tendsto_const_nhds.add (ht.const_mul (M:ℝ)))
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).1; dsimp [G]; linarith
    · intro k; have := (abs_le.mp (scalarWindow_approx hg (hh k) (L z))).2; dsimp [G]; linarith
  have HI (k) : |(∫ z, (coordinateLinear n a z)^2*G k z ∂μ)-
      (∑ i,(a i)^2)*(∫ z, G k z ∂μ)|≤ε₁^2+ε₂ := by
    have he := scalarWindow_comp_growth hg.continuous (B:=1) hb (hh k) L
    apply fiberGaussian_tent_error_C1 n V (G k) hV (hc k) he.1 he.2 x a _ ε₁ ε₂ (hb' k) h₁ h₂
    intro z t
    simp only [G,map_add,map_smul,hinv,smul_zero,add_zero]
  have hi : Integrable (fun z => (coordinateLinear n a z)^2) μ :=
    by
      simpa only [pow_two] using
        ((HasExpGrowth.linear (coordinateLinear n a)).mul (HasExpGrowth.linear (coordinateLinear n a))).integrable_tilted_fiberGaussian
          n V hV ((coordinateLinear n a).continuous.mul (coordinateLinear n a).continuous) x
  have H₁ := tendsto_integral_of_dominated_convergence (μ:=μ)
    (F:=fun k z => (coordinateLinear n a z)^2*G k z)
    (f:=fun z => (coordinateLinear n a z)^2*g (L z))
    (fun z => (coordinateLinear n a z)^2)
    (fun k => (((coordinateLinear n a).continuous.pow 2).mul (hc k).continuous).aestronglyMeasurable)
    hi (fun k => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hb' k z) (sq_nonneg _)).trans_eq (mul_one _)))
    (ae_of_all _ (fun z => (hlim z).const_mul _))
  have H₂ := tendsto_integral_of_dominated_convergence (μ:=μ)
    (F:=G) (f:=fun z => g (L z)) (fun _ => (1:ℝ))
    (fun k => (hc k).continuous.aestronglyMeasurable) (integrable_const 1)
    (fun k => ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb' k z))
    (ae_of_all _ hlim)
  exact le_of_tendsto (H₁.sub (H₂.const_mul _)).abs (Eventually.of_forall HI)

end SK.Analytic

end
end

end OAI
