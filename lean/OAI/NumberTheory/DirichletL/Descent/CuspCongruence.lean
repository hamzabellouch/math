import OAI.NumberTheory.DirichletL.Descent.MarkedReflection

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open MeasureTheory CompletedGauss CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

private theorem cusp_sum_kernel_integral {ι : Type*} [Fintype ι]
    (d : ι → SourceCuspDatum) (w : ι → ℂ) (F : ℝ → ℂ)
    (hF : ∀ v : ℝ, 0 < v → F v = ∑ i, w i * cuspBarProfile cubicSourceConjugateFunction (d i).point v)
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (d i).smoothedKernel W X) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        besselSmoothingIntegrand F thetaBesselScale (Vstar W) X ((-1 : ℂ) + t * Complex.I) := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G : ι → ℝ → ℂ := fun i => cuspBarProfile cubicSourceConjugateFunction (d i).point
  let J : ι → ℝ → ℂ := fun i t =>
    besselSmoothingIntegrand (G i) thetaBesselScale (Vstar W) X ((-1 : ℂ) + t * Complex.I)
  have hVs := Vstar_support W lo hi hsupp
  have hV := Vstar_contDiff W lo hi hlo hsupp hW
  have hint (i : ι) : Integrable (J i) :=
    besselSmoothingIntegrand_reflected_integrable (G i) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d i).index (d i).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d i).index) (d i).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d i).heightScale_pos
      (d i).multiplier (d i).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) lo hi hlo hVs hV X hX
  have hline (i : ι) : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, J i t) =
      (d i).smoothedKernel W X :=
    besselSmoothingIntegral_reflected_kernel (G i) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d i).index (d i).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d i).index) (d i).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d i).heightScale_pos
      (d i).multiplier (d i).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) lo hi hlo hVs hV X hX
  have hexpand (t : ℝ) :
      besselSmoothingIntegrand F thetaBesselScale (Vstar W) X ((-1 : ℂ) + t * Complex.I) =
        ∑ i, w i * J i t :=
    besselSmoothingIntegrand_finite_sum F G w hF thetaBesselScale (Vstar W) X _
      (fun i => (d i).cuspBarProfile_mellin_entire.1 _)
  simp_rw [hexpand]
  rw [integral_finsetSum Finset.univ (fun i _ => (hint i).const_mul (w i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, ← hline]
  ring

theorem cusp_kernel_sum_congr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (d : ι → SourceCuspDatum) (w : ι → ℂ)
    (e : κ → SourceCuspDatum) (z : κ → ℂ)
    (hmult : ∀ n : Eis,
      (∑ i, w i * ShortDraftTrace.breveE (-cuspFrequency n * (d i).point)) =
        ∑ k, z k * ShortDraftTrace.breveE (-cuspFrequency n * (e k).point))
    (W : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hsupp : Function.support W ⊆ Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0 < X) :
    (∑ i, w i * (d i).smoothedKernel W X) = ∑ k, z k * (e k).smoothedKernel W X := by
  let F : ℝ → ℂ := fun v => ∑ i, w i * cuspBarProfile cubicSourceConjugateFunction (d i).point v
  have hprofile (v : ℝ) (hv : 0 < v) :
      F v = ∑ k, z k * cuspBarProfile cubicSourceConjugateFunction (e k).point v := by
    rw [show F v = ∑ i, w i * cuspBarProfile cubicSourceConjugateFunction (d i).point v from rfl,
      ← finiteConjugateSource_wirtingerBar_sum _ _ v hv,
      ← finiteConjugateSource_wirtingerBar_sum _ _ v hv,
      finiteConjugateSource_wirtingerBar, finiteConjugateSource_wirtingerBar]
    simp_rw [hmult]
  rw [cusp_sum_kernel_integral d w F (fun _ _ => rfl) W lo hi hlo hsupp hW X hX,
    cusp_sum_kernel_integral e z F hprofile W lo hi hlo hsupp hW X hX]

theorem markedCompletedT_of_cusp_multiplier {ι κ : Type*} [Fintype κ]
    (p : ι → Eis) (S : Finset ι) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (d : κ → SourceCuspDatum) (w : κ → ℂ)
    (hmult : ∀ n : Eis, (∑ k, w k * ShortDraftTrace.breveE (-cuspFrequency n * (d k).point)) =
      markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ k, w k * (d k).smoothedKernel W X := by
  rw [markedCompletedT_canonical_reflection p S hp Ψ hΨ Q hperiod c hc hcQ
    W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply cusp_kernel_sum_congr (finiteTwistCusp c hc)
    (finiteAdditiveFourierCoeff (quotientTrace c hc)
      (markedThetaQuotient p S Ψ c)) d w ?_ W lo hi hlo hsupp hW X hX
  intro n
  simp_rw [finiteTwistCusp_point]
  rw [thetaFourierTranslation_inversion c hc, hmult]

end
end SevenEighths.InverseMoment

end OAI
