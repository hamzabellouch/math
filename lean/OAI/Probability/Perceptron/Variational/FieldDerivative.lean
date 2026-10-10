import Mathlib
import OAI.Probability.Perceptron.Variational.FieldContinuity
import OAI.Probability.Perceptron.Variational.IndexedObservableTransport

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma sourceFeature_square_bound (N : ℕ) (p : Fin N→ℕ) (u : Fin N→ℝ) (x : NormalizedSpin N) :
    (∑ i, sourceEnrichedFeature N p u x i^2) ≤ (enrichedFeatureBound N u:ℝ)^2 := by
  have he := congrArg (fun r : ℝ => r^2) (sourceEnrichedFeature_norm N p u x)
  simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le

lemma sourceKernelPressure_gaussianMean_base (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (h' h : Fin (k+1)→ℝ) (a : SourceBaseData n k) :
    (∫ g, sourceKernelPressure n k f p d u h' (a,g) ∂countableGaussianLaw) =
      (1/(n+1:ℕ))*indexedGaussianMean k (sourceSpinLeafKernel n k a)
        (sourceBaseEnergy n k f h a) (sourceEnrichedFeature (n+1) p u)
        (sourceFieldCoefficients p d h')+h (Fin.last k)-h' (Fin.last k) := by
  let W : NormalizedSpin (n+1)×IndexedLeaf k→ℝ := fun x =>
    normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1
  have hW : Measurable W := by
    have hm := enrichedIndexedBoundedEnergy_measurable n a.1 k f (patternPrefix (n+1) a.1 a.2.1) (fun _ => 0)
    unfold enrichedIndexedBoundedEnergy at hm
    simpa only [mul_zero,sub_zero] using hm
  have he := indexedGaussianMean_add_const k (sourceSpinLeafKernel n k a) hW
    (sourceEnrichedFeature_measurable (n+1) p u)
    (fun x => normalizedPatternEnergy_bound (n+1) a.1 f _ x.1)
    (sourceFeature_square_bound (n+1) p u) (sourceFieldCoefficients p d h')
    (-((n+1:ℕ)*h (Fin.last k)))
  rw [sourceKernelPressure_gaussianMean]
  change _ = (1/(n+1:ℕ))*indexedGaussianMean k (sourceSpinLeafKernel n k a)
    (fun x => W x+ -((n+1:ℕ)*h (Fin.last k))) (sourceEnrichedFeature (n+1) p u)
    (sourceFieldCoefficients p d h')+h (Fin.last k)-h' (Fin.last k)
  rw [he]
  dsimp only [W]
  field_simp
  ring

theorem sourceConditional_field_right_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) {h a : Fin (k+1)→ℝ}
    (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h) (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) :
    let w := indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u)
    let L := indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) (S := NormalizedSpin (n+1)) k
    HasDerivWithinAt (fun t => ∫ g, sourceKernelPressure n k f p d u (fun l => h l+t*a l) (b,g)
        ∂countableGaussianLaw)
      ((1/(n+1:ℕ))*((∫ g, indexedResponse k (sourceSpinLeafKernel n k b)
          (countableGaussianCovariance w w L) (sourceCouplingHamiltonian n k f p d h u (b,g))
        ∂countableGaussianLaw)/2)-a (Fin.last k)) (Ici 0) 0 := by
  have hW := (sourceBaseEnergy_measurable n k f h).of_uncurry_left (x := b)
  have hA := enrichedIndexedBoundedEnergy_bound n b.1 k f (patternPrefix (n+1) b.1 b.2.1) h
  have hd := indexedGaussianMean_right_response k (sourceSpinLeafKernel n k b)
    hW (sourceEnrichedFeature_measurable (n+1) p u) (sq_nonneg (enrichedFeatureBound (n+1) u:ℝ))
    hA (sourceFeature_square_bound (n+1) p u)
    (sourceFieldCoefficients p d h) (sourceDirectionCoefficients p a)
    (fun t => sourceFieldCoefficients p d (fun l => h l+t*a l))
    (fun t ht => sourceFieldCoefficients_affine_covariance p d hh0 hh ha0 ha ht)
  have he := (hd.const_mul (1/(n+1:ℕ):ℝ)).sub
    (((hasDerivAt_id (0:ℝ)).mul_const (a (Fin.last k))).hasDerivWithinAt (s := Ici 0))
  dsimp only at he ⊢
  simp only [one_mul] at he
  apply he.congr
  · intro t ht
    rw [sourceKernelPressure_gaussianMean_base n k f p d u _ h b]
    dsimp only [Pi.sub_apply,id_eq]
    ring
  · rw [sourceKernelPressure_gaussianMean_base n k f p d u _ h b]
    simp only [Pi.sub_apply,id_eq,zero_mul,add_zero,sub_zero]
    ring


def sourceFieldObservable {N k : ℕ} (a : Fin (k+1)→ℝ)
    (x : Fin 2→NormalizedSpin N×IndexedLeaf k) : ℝ :=
  a (indexedCommonDepth k (x 0).2 (x 1).2)*spinOverlap (x 1).1 (x 0).1

lemma sourceFieldObservable_measurable {N k : ℕ} (a : Fin (k+1)→ℝ) :
    Measurable (sourceFieldObservable (N := N) a) := by
  have ht : Measurable (fun x : Fin 2→NormalizedSpin N×IndexedLeaf k => a (indexedCommonDepth k (x 0).2 (x 1).2)) :=
    (Measurable.of_discrete (f := fun x : IndexedLeaf k×IndexedLeaf k => a (indexedCommonDepth k x.1 x.2))).comp
      (((measurable_pi_apply 0).snd).prodMk ((measurable_pi_apply 1).snd))
  have hr : Measurable (fun x : Fin 2→NormalizedSpin N×IndexedLeaf k => spinOverlap (x 1).1 (x 0).1) :=
    (measurable_subtype_coe.comp ((measurable_pi_apply 1).fst)).inner
      (measurable_subtype_coe.comp ((measurable_pi_apply 0).fst))
  exact ht.mul hr

lemma sourceFieldObservable_bound {N k : ℕ} {a : Fin (k+1)→ℝ}
    (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a) (x : Fin 2→NormalizedSpin N×IndexedLeaf k) :
    |sourceFieldObservable a x| ≤ a (Fin.last k) := by
  rw [sourceFieldObservable,abs_mul,abs_of_nonneg (ha0 _)]
  exact (mul_le_mul_of_nonneg_left (spinOverlap_abs_le _ _) (ha0 _)).trans
    (by simpa only [mul_one] using ha (Fin.le_last _))

lemma sourceConditional_field_observable_bound (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) (g : ℕ→ℝ) :
    |gibbsReplicaMean (sourceSpinLeafKernel n k b) (sourceCouplingHamiltonian n k f p d h u (b,g)) 2
      (sourceFieldObservable a)| ≤ a (Fin.last k) :=
  tiltMean_bound_general _
    (replicaPotential_measurable (sourceCouplingHamiltonian_section n k f p d h u (b,g)) 2)
    (sourceFieldObservable_measurable a) (ha0 _) (sourceFieldObservable_bound ha0 ha)

lemma sourceConditional_field_observable_integrable (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (b : SourceBaseData n k) :
    Integrable (fun g => gibbsReplicaMean (sourceSpinLeafKernel n k b)
      (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a)) countableGaussianLaw := by
  have hm : Measurable (Function.uncurry (fun g => sourceCouplingHamiltonian n k f p d h u (b,g))) :=
    (sourceCouplingHamiltonian_measurable n k f p d h u).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact kernel_replicaMean_bounded_integrable (Kernel.const _ (sourceSpinLeafKernel n k b)) countableGaussianLaw
    (H := fun g => sourceCouplingHamiltonian n k f p d h u (b,g)) (G := fun _ => sourceFieldObservable a)
    hm ((sourceFieldObservable_measurable a).comp measurable_snd) (ha0 _)
    (fun _ => sourceFieldObservable_bound ha0 ha)

lemma sourceConditional_partition_pos_ae (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    (b : SourceBaseData n k) :
    ∀ᵐ g ∂countableGaussianLaw,
      0 < tiltPartition (sourceSpinLeafKernel n k b) (sourceCouplingHamiltonian n k f p d h u (b,g)) 1 := by
  have he := (countableGaussianHamiltonian_exp_joint_integrable (sourceSpinLeafKernel n k b)
    ((sourceBaseEnergy_measurable n k f h).of_uncurry_left (x := b))
    (indexedGaussianRow_measurable k (sourceFieldCoefficients p d h) (sourceEnrichedFeature_measurable (n+1) p u))
    (indexedGaussianRowLength_measurable k)
    (enrichedIndexedBoundedEnergy_bound n b.1 k f (patternPrefix (n+1) b.1 b.2.1) h)
    (indexedGaussianRow_square_total k (sourceFieldCoefficients p d h) (sourceEnrichedFeature (n+1) p u)
      (sourceFeature_square_bound (n+1) p u)) 1).prod_left_ae
  exact he.mono fun g hg => tilt_partition_pos_of_integrable _ hg

lemma tiltMean_const_of_pos {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (H : S→ℝ) (t c : ℝ) (hpos : 0 < tiltPartition μ H t) :
    tiltMean μ H (fun _ => c) t=c := by
  unfold tiltMean tiltIntegral
  rw [integral_mul_const]
  change tiltPartition μ H t*c/tiltPartition μ H t=c
  field_simp

lemma sourceConditional_response_eq (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ)
    {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a) (b : SourceBaseData n k) :
    let w := indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u)
    let L := indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) (S := NormalizedSpin (n+1)) k
    (∫ g, indexedResponse k (sourceSpinLeafKernel n k b) (countableGaussianCovariance w w L)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) ∂countableGaussianLaw) =
      2*(n+1:ℕ)*a (Fin.last k)-2*(n+1:ℕ)*(∫ g, gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a) ∂countableGaussianLaw) := by
  dsimp only
  have hd (x : NormalizedSpin (n+1)×IndexedLeaf k) : spinOverlap x.1 x.1=1 := by
    have hx : ‖x.1.val‖=1 := by simp
    simp [spinOverlap,hx]
  have he : ∀ᵐ g ∂countableGaussianLaw, indexedResponse k (sourceSpinLeafKernel n k b)
      (countableGaussianCovariance
        (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u))
        (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature (n+1) p u))
        (indexedGaussianRowLength (I := EnrichedIndex (n+1) (n+1) p) k))
      (sourceCouplingHamiltonian n k f p d h u (b,g)) =
      2*(n+1:ℕ)*a (Fin.last k)-2*(n+1:ℕ)*gibbsReplicaMean (sourceSpinLeafKernel n k b)
        (sourceCouplingHamiltonian n k f p d h u (b,g)) 2 (sourceFieldObservable a) := by
    filter_upwards [sourceConditional_partition_pos_ae n k f p d u h b] with g hg
    simp only [indexedResponse,sourceDirection_covariance p u ha0 ha,indexedCommonDepth_self,hd,mul_one]
    rw [tiltMean_const_of_pos _ _ _ _ hg]
    congr 1
    change tiltMean _ _ (fun x : Fin 2→NormalizedSpin (n+1)×IndexedLeaf k => 2*(n+1:ℕ)*a (indexedCommonDepth k (x 0).2 (x 1).2)*spinOverlap (x 1).1 (x 0).1) 1 = _
    rw [show (fun x : Fin 2→NormalizedSpin (n+1)×IndexedLeaf k =>
      2*(n+1:ℕ)*a (indexedCommonDepth k (x 0).2 (x 1).2)*spinOverlap (x 1).1 (x 0).1) =
      (fun x => (2*(n+1:ℕ))*sourceFieldObservable a x) from funext fun x => by
        unfold sourceFieldObservable
        ring,tiltMean_const_mul_general]
    rfl
  rw [integral_congr_ae he,integral_sub (integrable_const _)
    ((sourceConditional_field_observable_integrable n k f p d u h ha0 ha b).const_mul _),
    integral_const,probReal_univ,one_smul,integral_const_mul]

end SphericalPerceptronFreeEnergy
end

end OAI
