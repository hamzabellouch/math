import OAI.Analysis.ModularTheory.DualKernelPairing
import OAI.Analysis.ModularTheory.FieldPairing
import OAI.Analysis.OperatorAlgebra.KernelIntegralBounds
import OAI.Analysis.OperatorAlgebra.GaussianKernelFubini

namespace OAI

/-! Identification of integrated covariant kernels with bounded Gaussian
regularizations of the actual convolution-smoothed fixed point. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weightedScalarSliceKernel
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ)) (x y : H) (p : ℝ × ℝ) : ℂ :=
  star (u p.1) * v p.2 * scalarKernelMatrixCoefficient T f g x y p

lemma weightedScalarSliceKernel_integrable
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ))
    (hu : Integrable (u : ℝ → ℂ)) (hv : Integrable (v : ℝ → ℂ)) (x y : H) :
    Integrable (weightedScalarSliceKernel T f g u v x y) (volume.prod volume) :=
  integrable_weighted_scalar_kernel u v hu hv (scalarKernelMatrixCoefficient T f g x y)
    (scalarKernelMatrixCoefficient_continuous T f g x y) _
    (scalarKernelMatrixCoefficient_bound T f g x y)

lemma characterWeightedKernel_integrable (A : ℝ × ℝ → ℂ)
    (hA : Integrable A (volume.prod volume)) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ => BoundedRecovery.spectralCharacter r (p.2 - p.1) * A p)
      (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => BoundedRecovery.spectralCharacter r (p.2 - p.1)) :=
    (BoundedRecovery.spectralCharacter r).continuous.comp (continuous_snd.sub continuous_fst)
  apply hA.mono (hc.aestronglyMeasurable.mul hA.aestronglyMeasurable)
  filter_upwards [] with p
  simp only [Pi.mul_apply, norm_mul,
    BoundedRecovery.spectralCharacter_norm, one_mul]
  exact le_rfl

theorem gaussianSmoothedKernel_pairing
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ))
    (hu : Integrable (u : ℝ → ℂ)) (hv : Integrable (v : ℝ → ℂ))
    (n : ℕ) (x y : H) :
    inner ℂ (modularDualGaussianAverage (convolutionSmoothedOperator T f g hf hg) n
      (scalarVectorLp volume u x)) (scalarVectorLp volume v y) =
      ∫ p : ℝ × ℝ, gaussianSchurFactor n (p.2 - p.1) *
        weightedScalarSliceKernel T f g u v x y p ∂volume.prod volume := by
  let X := convolutionSmoothedOperator T f g hf hg
  let A := weightedScalarSliceKernel T f g u v x y
  have hA : Integrable A (volume.prod volume) := weightedScalarSliceKernel_integrable T f g u v hu hv x y
  have hi := BoundedRecovery.integrable_smul_bounded_orbit
    realGaussianDensity_integrable.ofReal
    ((modularDualConjugation_continuous X (scalarVectorLp volume u x)).comp
      (continuous_id.div_const (n + 1 : ℝ)))
    (fun r => ((modularDualConjugation volume (r / (n + 1 : ℝ)) X).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (modularDualConjugation_norm_le X _) (norm_nonneg _)))
  change Integrable (fun r : ℝ => (realGaussianDensity r : ℂ) •
    modularDualConjugation volume (r / (n + 1 : ℝ)) X (scalarVectorLp volume u x)) at hi
  change inner ℂ (∫ r : ℝ, (realGaussianDensity r : ℂ) •
    modularDualConjugation volume (r / (n + 1 : ℝ)) X (scalarVectorLp volume u x)) _ = _
  refine (inner_integral_left hi (scalarVectorLp volume v y)).trans ?_
  calc
    _ = ∫ r : ℝ, (realGaussianDensity r : ℂ) *
        ∫ p : ℝ × ℝ, BoundedRecovery.spectralCharacter (-(r / (n + 1 : ℝ)))
          (p.2 - p.1) * A p ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards [] with r
      rw [inner_smul_left, Complex.conj_ofReal]
      congr 1
      change inner ℂ (modularDualConjugation volume (r / (n + 1 : ℝ))
        (convolutionSmoothedOperator T f g hf hg) (scalarVectorLp volume u x)) _ = _
      rw [modularDual_convolutionSmoothed_pairing T f g u v hf hg hu hv]
      exact (integral_prod _ (characterWeightedKernel_integrable A hA _)).symm
    _ = _ := gaussian_character_kernel_integral A hA n

lemma gaussianWeightedKernel_integrable (A : ℝ × ℝ → ℂ)
    (hA : Integrable A (volume.prod volume)) (n : ℕ) :
    Integrable (fun p : ℝ × ℝ => gaussianSchurFactor n (p.2 - p.1) * A p)
      (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => gaussianSchurFactor n (p.2 - p.1)) :=
    (gaussianSchurFactor_continuous n).comp (continuous_snd.sub continuous_fst)
  apply hA.mono (hc.aestronglyMeasurable.mul hA.aestronglyMeasurable)
  filter_upwards [] with p
  simp only [Pi.mul_apply, norm_mul]
  exact (mul_le_mul_of_nonneg_right (gaussianSchurFactor_norm_le n _) (norm_nonneg _)).trans_eq
    (one_mul _)

lemma gaussianSchurFactor_star_integrable (n : ℕ) :
    Integrable (fun r => star (gaussianSchurFactor n r)) := by
  apply (gaussianSchurFactor_integrable n).norm.mono'
    (gaussianSchurFactor_integrable n).aestronglyMeasurable.star
  filter_upwards [] with r
  simp only [Pi.star_apply, norm_star]
  exact le_rfl

theorem integratedGaussianKernel_pairing (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : ∀ s f, T (modularRightTranslation volume S.D s f) =
      modularRightTranslation volume S.D s (T f))
    (f g u v : Lp ℂ 2 (volume : Measure ℝ))
    (hu : Integrable (u : ℝ → ℂ)) (hv : Integrable (v : ℝ → ℂ))
    (n : ℕ) (x y : H) :
    inner ℂ (modularKernelRegularization S T f g (fun r => star (gaussianSchurFactor n r))
      (gaussianSchurFactor_star_integrable n) (scalarVectorLp volume u x))
      (scalarVectorLp volume v y) =
      ∫ p : ℝ × ℝ, gaussianSchurFactor n (p.2 - p.1) *
        weightedScalarSliceKernel T f g u v x y p ∂volume.prod volume := by
  let A := weightedScalarSliceKernel T f g u v x y
  have hA : Integrable A (volume.prod volume) := weightedScalarSliceKernel_integrable T f g u v hu hv x y
  refine (modularKernelRegularization_pairing S T hT f g u v
    (fun r => star (gaussianSchurFactor n r)) (gaussianSchurFactor_star_integrable n) x y).trans ?_
  simp only [star_star]
  change (∫ r : ℝ, ∫ s : ℝ, gaussianSchurFactor n r * A (s - r, s)) = _
  rw [kernel_integral_change_variables A hA (gaussianSchurFactor n)
    (gaussianSchurFactor_continuous n) 1 (gaussianSchurFactor_norm_le n)]
  exact (integral_prod _ (gaussianWeightedKernel_integrable A hA n)).symm

omit [CompleteSpace H] in
lemma operator_eq_of_integrable_scalar_pairs
    (T R : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (h : ∀ (u v : Lp ℂ 2 (volume : Measure ℝ)), Integrable (u : ℝ → ℂ) →
      Integrable (v : ℝ → ℂ) → ∀ x y : H,
      inner ℂ (T (scalarVectorLp volume u x)) (scalarVectorLp volume v y) =
      inner ℂ (R (scalarVectorLp volume u x)) (scalarVectorLp volume v y)) : T = R := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  apply scalarVectorLp_operator_ext volume
  intro u x v y
  have hx : Continuous (fun a : Lp ℂ 2 (volume : Measure ℝ) => scalarVectorLp volume a x) :=
    ((ContinuousLinearMap.toSpanSingleton ℂ x).compLpL 2 volume).continuous
  have hy : Continuous (fun a : Lp ℂ 2 (volume : Measure ℝ) => scalarVectorLp volume a y) :=
    ((ContinuousLinearMap.toSpanSingleton ℂ y).compLpL 2 volume).continuous
  apply hd.induction_on (p := fun u =>
    inner ℂ (T (scalarVectorLp volume u x)) (scalarVectorLp volume v y) =
      inner ℂ (R (scalarVectorLp volume u x)) (scalarVectorLp volume v y)) u
  · exact isClosed_eq ((T.continuous.comp hx).inner continuous_const)
      ((R.continuous.comp hx).inner continuous_const)
  · intro u₀
    let a : Lp ℂ 2 (volume : Measure ℝ) := u₀.toLp 2 volume
    change inner ℂ (T (scalarVectorLp volume a x)) (scalarVectorLp volume v y) =
      inner ℂ (R (scalarVectorLp volume a x)) (scalarVectorLp volume v y)
    refine hd.induction_on (p := fun b : Lp ℂ 2 (volume : Measure ℝ) =>
      inner ℂ (T (scalarVectorLp volume a x)) (scalarVectorLp volume b y) =
        inner ℂ (R (scalarVectorLp volume a x)) (scalarVectorLp volume b y)) v
      (isClosed_eq (continuous_const.inner hy) (continuous_const.inner hy)) ?_
    intro v₀
    exact h (u₀.toLp 2 volume) (v₀.toLp 2 volume)
        (u₀.integrable.congr (u₀.coeFn_toLp 2 volume).symm)
        (v₀.integrable.congr (v₀.coeFn_toLp 2 volume).symm) x y

theorem modularKernelRegularization_eq_dualAverage
    (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : ∀ s f, T (modularRightTranslation volume S.D s f) =
      modularRightTranslation volume S.D s (T f))
    (f g : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → ℂ)) (hg : Integrable (g : ℝ → ℂ)) (n : ℕ) :
    modularKernelRegularization S T f g (fun r => star (gaussianSchurFactor n r))
        (gaussianSchurFactor_star_integrable n) =
      modularDualGaussianAverage (convolutionSmoothedOperator T f g hf hg) n := by
  apply operator_eq_of_integrable_scalar_pairs
  intro u v hu hv x y
  exact (integratedGaussianKernel_pairing S T hT f g u v hu hv n x y).trans
    (gaussianSmoothedKernel_pairing T f g u v hf hg hu hv n x y).symm

end WeakPureInfiniteness

end

end OAI
