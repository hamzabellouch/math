import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityConditionalIncrement

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators BoundedContinuousFunction

def cavityOldJoinedHamiltonian (n L M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M) (W : NormalizedSpin (n+1)→ℝ)
    (y : Fin M→Spin L) (p : CavityShellSpin n L) : ℝ :=
  cavityShellPatternEnergy n L M f.f (cavityJoinedPatterns (n+1) L M a.1 y) p+
    inner ℝ (bulkFeature (n+1) v p.1) a.2+W p.1

lemma cavity_actual_old_log_identity (n L M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (n+1) M)
    (hp : (cavitySphereLaw n L : Measure (Spin L)) (cavityShell L)≠0)
    (W : NormalizedSpin (n+1)→ℝ) (hW : Measurable W)
    {E : ℝ} (hE : 0≤E) (hWE : ∀ x,|W x|≤E) (y : Fin M→Spin L) :
    Real.log (∫ p,Real.exp (cavityOldJoinedHamiltonian n L M f v a W y p)
      ∂cavityShellBaseLaw n L)-bulkLogPartition n M f.f v a.1 a.2=
    Real.log (∫ p,Real.exp (cavityOldIncrement n L M f a.1 W y p)
      ∂(tiltLaw (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 1).prod
        (cavityShellProbability n L)) := by
  have hm : Measurable (cavityOldIncrement n L M f a.1 W y) := by
    have hm0 := cavityOldIncrement_measurable n L M f a.1 W hW
    exact Measurable.of_uncurry_right
      (f:=fun p y=>cavityOldIncrement n L M f a.1 W y p) hm0
  have hB : 0≤2*M*‖f.f‖+E := by positivity
  have hVB : ∀ p,|cavityOldIncrement n L M f a.1 W y p|≤2*M*‖f.f‖+E :=
    cavityOldIncrement_bound n L M f a.1 W hWE y
  have hh:=cavity_actual_bulk_log_factorization n L M f.f v a hp
    (cavityOldIncrement n L M f a.1 W y) hm hB hVB
  apply Eq.trans _ hh
  congr 3
  funext p
  congr 1
  unfold cavityOldJoinedHamiltonian bulkHamiltonian cavityOldIncrement
  ring

theorem cavity_normalized_old_increment_lower (n k M : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (v : ℕ→ℝ) (a : BulkDisorder (n+1) M) (W : NormalizedSpin (n+1)→ℝ)
    (hW : Measurable W) {E : ℝ} (hE : 0≤E) (hWE : ∀ x,|W x|≤E) :
    let μ := tiltLaw (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 1
    let K : ℝ:=M/(n+1:ℕ)*‖f.dilationMark h1‖
    let A : NormalizedSpin (n+1)→Fin M→ℝ:=fun x i=>f.d1 (∑ j,a.1 i j*x.val j)
    (∫ y : Fin M→Spin (k+1),(Real.log (∫ p,Real.exp (cavityOldJoinedHamiltonian n (k+1) M f v a W y p)
      ∂cavityShellBaseLaw n (k+1))-bulkLogPartition n M f.f v a.1 a.2) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))≥
    (∫ y : Fin M→Spin (k+1),Real.log (∫ x,Real.exp (W x+(k+1:ℕ)*bulkC (n+1) M f a.1 x/2)*
      sphericalExp k (cavityVectorField M (k+1) (A x) (Real.sqrt (n+1:ℕ))⁻¹ y)
        (Real.sqrt (k+1:ℕ)) ∂μ) ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))-K/2-
      Real.exp (2*(E+((k+1:ℕ)+1)*K/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)-
      (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
        (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
        ∂Measure.pi (fun _=>stdGaussian (Spin (k+1)))) := by
  have := tilt_law_probability (unitSphereLaw (n+1))
    (bulkHamiltonian_section_measurable (n+1) M f.f v a)
    (show 0≤M*‖f.f‖+bulkFeatureBound (n+1) v*‖a.2‖ from by
      apply add_nonneg (by positivity)
      apply mul_nonneg
      · unfold bulkFeatureBound
        positivity
      · positivity)
    (bulkHamiltonian_bound (n+1) M f.f v a) 1
  dsimp only
  simp_rw [cavity_actual_old_log_identity n (k+1) M f v a hp W hW hE hWE]
  exact cavity_conditional_old_increment_lower n k M f h1 h2 h3 hn hp
    (tiltLaw (unitSphereLaw (n+1)) (bulkHamiltonian (n+1) M f.f v a.1 a.2) 1)
    a.1 W hW hE hWE

lemma cavity_truncated_countable_kernel {S I : Type*} [MeasurableSpace S]
    [Fintype I] [DecidableEq I] (v : ℕ→S→ℝ) (L : S→ℕ)
    (Ψ : EuclideanSpace ℝ I→ᵇℝ) (n : ℕ) (xs : I→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i=>truncatedCountableGaussianField v L n g (xs i)))
      ∂countableGaussianLaw)=
      cavityMatrixKernel Ψ (fun i j=>gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
  let rows : I→EuclideanSpace ℝ (Fin n):=fun i=>
    WithLp.toLp 2 (fun j=>maskedGaussianCoefficient v L j.val (xs i))
  have hg : Matrix.gram ℝ rows=(fun i j=>gaussianPrefixCovariance v v L n (xs i) (xs j)) := by
    ext i j
    change (∑ l : Fin n,maskedGaussianCoefficient v L l.val (xs j)*
      maskedGaussianCoefficient v L l.val (xs i))=_
    exact Finset.sum_congr rfl fun l _=>mul_comm _ _
  rw [←hg,cavityMatrixKernel_posSemidef _ _ (Matrix.posSemidef_gram ℝ rows),
    ←gaussianRows_map_stdGaussian rows,
    integral_map (gaussianRows rows).continuous.measurable.aemeasurable Ψ.continuous.aestronglyMeasurable,
    ←map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  have hp:=gaussianCoordinatePrefix_measurePreserving n
  have hm : AEStronglyMeasurable (fun y : Fin n→ℝ=>Ψ (gaussianRows rows (WithLp.toLp 2 y)))
      (Measure.pi fun _ : Fin n=>gaussianReal 0 1) := by fun_prop
  rw [←hp.map_eq] at hm ⊢
  rw [integral_map hp.measurable.aemeasurable hm]
  apply integral_congr_ae
  exact ae_of_all _ fun g=>rfl

lemma cavity_countable_kernel {S I : Type*} [MeasurableSpace S]
    [Fintype I] [DecidableEq I] (v : ℕ→S→ℝ) (L : S→ℕ)
    (Ψ : EuclideanSpace ℝ I→ᵇℝ) (xs : I→S) :
    (∫ g, Ψ (WithLp.toLp 2 (fun i=>countableGaussianField v L g (xs i)))
      ∂countableGaussianLaw)=
      cavityMatrixKernel Ψ (fun i j=>countableGaussianCovariance v v L (xs i) (xs j)) := by
  have he : ∀ᶠ n : ℕ in atTop,∀ i : I,∀ g,
      truncatedCountableGaussianField v L n g (xs i)=countableGaussianField v L g (xs i) :=
    Filter.eventually_all.mpr (fun i=>truncatedCountableGaussianField_eventually_eq v L (xs i))
  have hc : ∀ᶠ n : ℕ in atTop,∀ i j : I,
      gaussianPrefixCovariance v v L n (xs i) (xs j)=countableGaussianCovariance v v L (xs i) (xs j) :=
    Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (fun j=>
      gaussianPrefixCovariance_eventually_eq v v L (xs i) (xs j)))
  obtain ⟨n,hn,hc⟩:=(he.and hc).exists
  have hh:=cavity_truncated_countable_kernel v L Ψ n xs
  simp_rw [hn,hc] at hh
  exact hh

def cavityCountableField {S J : Type*} [Fintype J] (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (g : ℕ→ℝ) (x : S) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j=>countableGaussianField v L g (x,j))

lemma cavityCountableField_measurable {S J : Type*} [MeasurableSpace S]
    [Fintype J] [MeasurableSpace J] (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (hv : ∀ i,Measurable (v i)) (hL : Measurable L) :
    Measurable (fun p : (ℕ→ℝ)×S=>cavityCountableField v L p.1 p.2) := by
  apply (MeasurableEquiv.toLp 2 (J→ℝ)).measurable.comp
  apply Measurable.of_eval
  intro j
  exact (countableGaussianField_measurable hv hL).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

theorem cavity_countable_moment {S J : Type*} [MeasurableSpace S]
    [Fintype J] [DecidableEq J] [MeasurableSpace J]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (v : ℕ→S×J→ℝ) (L : S×J→ℕ)
    (hv : ∀ i,Measurable (v i)) (hL : Measurable L)
    (Ψ : EuclideanSpace ℝ J→ᵇℝ) (r : ℕ) :
    (∫ g, (∫ x, Ψ (cavityCountableField v L g x) ∂μ)^r ∂countableGaussianLaw)=
      ∫ xs : Fin r→S,cavityMatrixKernel (cavityTestReplica Ψ r)
        (fun i j : J×Fin r=>countableGaussianCovariance v v L (xs i.2,i.1) (xs j.2,j.1))
          ∂Measure.pi (fun _=>μ) := by
  let F : (ℕ→ℝ)×(Fin r→S)→ℝ:=fun p=>∏ i,Ψ (cavityCountableField v L p.1 (p.2 i))
  have hm : Measurable F := Finset.measurable_prod _ fun i _=>
    Ψ.measurable.comp ((cavityCountableField_measurable v L hv hL).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hb p : ‖F p‖≤‖Ψ‖^r := by
    simp only [F,norm_prod]
    exact (Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun _ _=>Ψ.norm_coe_le_norm _)).trans_eq (by simp)
  have hi : Integrable F (countableGaussianLaw.prod (Measure.pi fun _ : Fin r=>μ)) :=
    Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  calc
    _=∫ g,∫ xs : Fin r→S,F (g,xs) ∂Measure.pi (fun _=>μ) ∂countableGaussianLaw := by
      apply integral_congr_ae
      exact ae_of_all _ fun g=>by
        simpa only [F,Fintype.card_fin] using
          (integral_fintype_prod_eq_pow (ι:=Fin r) (fun x=>Ψ (cavityCountableField v L g x)) (μ:=μ)).symm
    _=∫ xs : Fin r→S,∫ g,F (g,xs) ∂countableGaussianLaw ∂Measure.pi (fun _=>μ) := integral_integral_swap hi
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ fun xs=>by
        simpa only [cavityTestReplica_apply,cavityCountableField,F] using
          cavity_countable_kernel v L (cavityTestReplica Ψ r) (fun p : J×Fin r=>(xs p.2,p.1))

end SphericalPerceptronFreeEnergy
end

end OAI
