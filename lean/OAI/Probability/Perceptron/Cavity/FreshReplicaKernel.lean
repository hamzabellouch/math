import Mathlib
import OAI.Probability.Perceptron.Interpolation.ArrayGeometry

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

private lemma freshKernel_extension_exists (f : ℝ →ᵇ ℝ) (r : ℕ) :
    ∃ F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ,
      ‖F‖=‖gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin r) f)‖ ∧
      ∀ C : CovarianceMatrix (Fin r), F C.val=gaussianCovarianceKernel (gaussianReplicaTest f) C := by
  let : NormalSpace (Matrix (Fin r) (Fin r) ℝ) := inferInstanceAs (NormalSpace (Fin r→Fin r→ℝ))
  obtain ⟨F,hF,he⟩ := (gaussianCovarianceKernel (gaussianReplicaTest (ι := Fin r) f)).exists_extension_norm_eq_of_isClosedEmbedding
    (isClosed_matrix_posSemidef r).isClosedEmbedding_subtypeVal
  exact ⟨F,hF,fun C => congrFun he C⟩

def freshReplicaMatrixKernel (f : ℝ →ᵇ ℝ) (r : ℕ) : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ :=
  Classical.choose (freshKernel_extension_exists f r)

lemma freshReplicaMatrixKernel_gram (f : ℝ →ᵇ ℝ) (r : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : Fin r→E) :
    freshReplicaMatrixKernel f r (Matrix.gram ℝ v)=
      ∫ z, gaussianReplicaTest f z ∂multivariateGaussian 0 (Matrix.gram ℝ v) :=
  (Classical.choose_spec (freshKernel_extension_exists f r)).2 (gramCovariance v)

def freshReplicaArrayKernel (f : ℝ →ᵇ ℝ) (r : ℕ) : CompactArray CompactJointOverlap →ᵇ ℝ :=
  (freshReplicaMatrixKernel f r).compContinuous
    ⟨fun Q => fun i j : Fin r => (Q i j).1.val,by fun_prop⟩

lemma freshReplicaArrayKernel_source (f : ℝ →ᵇ ℝ) (r : ℕ) {N k : ℕ}
    (x : ℕ→NormalizedSpin N×IndexedLeaf k) :
    freshReplicaArrayKernel f r (sourceJointArray x)=
      ∫ z, gaussianReplicaTest f z ∂multivariateGaussian 0
        (Matrix.gram ℝ (fun i : Fin r => (x i).1.val)) := by
  change freshReplicaMatrixKernel f r _=_
  convert freshReplicaMatrixKernel_gram f r (fun i : Fin r => (x i).1.val) using 1
  congr 1

lemma freshReplicaArrayKernel_tendsto {ν : ℕ→ProbabilityMeasure (CompactArray CompactJointOverlap)}
    {ν₀ : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hν : Tendsto ν atTop (𝓝 ν₀)) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    Tendsto (fun n => ∫ Q, freshReplicaArrayKernel f r Q ∂ν n) atTop
      (𝓝 (∫ Q, freshReplicaArrayKernel f r Q ∂ν₀)) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (freshReplicaArrayKernel f r)).continuousAt.tendsto.comp hν

lemma freshPattern_moment_measurable_spins
    {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : S→E) (hv : Measurable v) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (∫ x, f (inner ℝ (v x) g) ∂μ)^r ∂stdGaussian E)=
      ∫ xs : Fin r→S, ∫ z, gaussianReplicaTest f z ∂multivariateGaussian 0
        (Matrix.gram ℝ (fun i => v (xs i))) ∂Measure.pi (fun _ => μ) := by
  classical
  let F : E×(Fin r→S)→ℝ := fun p => ∏ i, f (inner ℝ (v (p.2 i)) p.1)
  have hm : Measurable F := Finset.measurable_prod _ fun i _ => f.continuous.measurable.comp
    ((hv.comp ((measurable_pi_apply i).comp measurable_snd)).inner measurable_fst)
  have hb (p : E×(Fin r→S)) : ‖F p‖≤‖f‖^r := by
    simp only [F,norm_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => f.norm_coe_le_norm _)).trans_eq
      (by simp)
  have hi : Integrable F ((stdGaussian E).prod (Measure.pi fun _ : Fin r => μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  calc
    _ = ∫ g, ∫ xs : Fin r→S, F (g,xs) ∂Measure.pi (fun _ => μ) ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [] with g
      simpa only [F,Fintype.card_fin] using
        (integral_fintype_prod_eq_pow (ι := Fin r) (fun x : S => f (inner ℝ (v x) g)) (μ := μ)).symm
    _ = ∫ xs : Fin r→S, ∫ g, F (g,xs) ∂stdGaussian E ∂Measure.pi (fun _ => μ) :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with xs
      rw [← gaussianRows_map_stdGaussian (fun i => v (xs i)),
        integral_map (gaussianRows (fun i => v (xs i))).continuous.measurable.aemeasurable
          (gaussianReplicaTest f).continuous.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [F,gaussianReplicaTest_apply,gaussianRows_apply]

lemma freshPattern_gibbs_moment {S E : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) [IsProbabilityMeasure μ]
    (v : S→E) (hv : Measurable v) (H : S→ℝ) (hH : Measurable H)
    (he : Integrable (fun x => Real.exp (H x)) μ) (f : ℝ →ᵇ ℝ) (r : ℕ) :
    (∫ g, (tiltMean μ H (fun x => f (inner ℝ (v x) g)) 1)^r ∂stdGaussian E)=
      gibbsReplicaMean μ H r (fun xs => freshReplicaMatrixKernel f r
        (Matrix.gram ℝ (fun i => v (xs i)))) := by
  have he1 : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using he
  let := tilt_law_probability_of_integrable μ he1
  simp_rw [← tilt_law_integral_of_integrable μ hH he1]
  rw [gibbsReplicaMean_integral_of_integrable μ hH he,
    freshPattern_moment_measurable_spins (tiltLaw μ H 1) v hv f r]
  apply integral_congr_ae
  exact ae_of_all _ fun xs => (freshReplicaMatrixKernel_gram f r (fun i => v (xs i))).symm

def sourceFreshMoment (n k : ℕ) (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) : ℝ :=
  ∫ a, ∫ g, (tiltMean (sourceFullSpinLeafKernel n k a)
    (sourceCouplingHamiltonian n k f p d h u a)
    (fun x => ψ (inner ℝ x.1.val g)) 1)^r ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)))
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw

lemma sourceFreshMoment_array (n k : ℕ) (f ψ : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (hh0 : ∀ i, 0≤h i) (hh : Monotone h)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℝ≥0) (r : ℕ) :
    sourceFreshMoment n k f ψ p d h u z t r=
      ∫ Q, freshReplicaArrayKernel ψ r Q ∂sourceGibbsArrayLaw n k f p d h u z t := by
  let F : CompactBlock CompactJointOverlap r→ᵇ ℝ :=
    (freshReplicaMatrixKernel ψ r).compContinuous
      ⟨fun Q => fun i j : Fin r => (Q i j).1.val,by fun_prop⟩
  have hblock := sourceGibbsArray_block_integral n k f p d h hh0 hh u z t r F.measurable
    (fun Q => F.norm_coe_le_norm Q)
  change (∫ Q, freshReplicaArrayKernel ψ r Q ∂sourceGibbsArrayLaw n k f p d h u z t)=_ at hblock
  rw [hblock]
  unfold sourceFreshMoment
  apply integral_congr_ae
  filter_upwards [sourceCoupling_all_exp_ae n k f p d h hh0 hh u 0 z t] with a ha
  have he : Integrable (fun x => Real.exp (sourceCouplingHamiltonian n k f p d h u a x))
      (sourceFullSpinLeafKernel n k a) := by
    simpa only [sourceFullSpinLeafKernel,Kernel.comap_apply,zero_mul,add_zero] using ha 0
  have hv : Measurable (fun x : NormalizedSpin (n+1)×IndexedLeaf k => x.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  rw [freshPattern_gibbs_moment _ _ hv _ (sourceCouplingHamiltonian_measurable n k f p d h u).of_uncurry_left he]
  rfl

theorem sourceFreshMoment_tendsto (k : ℕ) (f ψ : ℝ →ᵇ ℝ)
    (p d : (n : ℕ)→Fin (n+1)→ℕ) (h : ℕ→Fin (k+1)→ℝ)
    (hh0 : ∀ n i, 0≤h n i) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (z : Fin k→ℝ) (t : ℕ→ℝ≥0) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)}
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν)) (r : ℕ) :
    Tendsto (fun n => sourceFreshMoment (s n) k f ψ (p (s n)) (d (s n))
      (h (s n)) (u (s n)) z (t (s n)) r) atTop
      (𝓝 (∫ Q, freshReplicaArrayKernel ψ r Q ∂ν)) := by
  simp_rw [sourceFreshMoment_array _ _ _ _ _ _ _ (hh0 _) (hh _)]
  exact freshReplicaArrayKernel_tendsto hlim ψ r

end SphericalPerceptronFreeEnergy

end

end OAI
