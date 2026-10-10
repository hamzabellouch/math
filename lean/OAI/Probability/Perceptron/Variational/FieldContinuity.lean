import Mathlib
import OAI.Probability.Perceptron.Interpolation.PerturbationContact
import OAI.Probability.Perceptron.Variational.GaussianComparison

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

def sourceFieldCoefficients {N k : ℕ} (p d : Fin N→ℕ) (h : Fin (k+1)→ℝ) :
    Fin (k+1)→EnrichedIndex N N p→ℝ :=
  hierarchyRowCoefficients k (profileGaussianRoot (enrichedCoordinateLevel p d h))
    (profileGaussianStep (enrichedCoordinateLevel p d h))

lemma sourceFieldCoefficients_continuous {N k : ℕ} (p d : Fin N→ℕ) :
    Continuous (@sourceFieldCoefficients N k p d) := by
  have hc (l : Fin (k+1)) (i : EnrichedIndex N N p) :
      Continuous (fun h : Fin (k+1)→ℝ => enrichedCoordinateLevel p d h l i) := by
    cases i <;> simp only [enrichedCoordinateLevel] <;> fun_prop
  apply continuous_pi
  intro l
  apply continuous_pi
  intro i
  simp only [sourceFieldCoefficients,profileGaussian_coefficient]
  induction l using Fin.cases with
  | zero => simpa only [Fin.cases_zero] using (hc 0 i).sqrt
  | succ l => simpa only [Fin.cases_succ, Pi.sub_apply] using ((hc l.succ i).sub (hc l.castSucc i)).sqrt

def sourceFieldDistance {N k : ℕ} (p d : Fin N→ℕ) (u : Fin N→ℝ)
    (h' h : Fin (k+1)→ℝ) : ℝ :=
  let D := indexedCoefficientSquare k (sourceFieldCoefficients p d h)*(enrichedFeatureBound N u:ℝ)^2
  let E := indexedCoefficientSquare k (fun l i => sourceFieldCoefficients p d h' l i-
    sourceFieldCoefficients p d h l i)*(enrichedFeatureBound N u:ℝ)^2
  (1/(N:ℝ))*(2*(Real.sqrt (2*D+2*E)*Real.sqrt E))+|h' (Fin.last k)-h (Fin.last k)|

lemma sourceFieldDistance_continuous {N k : ℕ} (p d : Fin N→ℕ) (u : Fin N→ℝ)
    (h : Fin (k+1)→ℝ) : Continuous (fun h' => sourceFieldDistance p d u h' h) := by
  have hc := sourceFieldCoefficients_continuous (k := k) p d
  have he : Continuous (fun h' => indexedCoefficientSquare k
      (fun l i => sourceFieldCoefficients p d h' l i-sourceFieldCoefficients p d h l i)) := by
    simpa only [Function.comp_def,Pi.sub_def] using
      (indexedCoefficientSquare_continuous (I := EnrichedIndex N N p) k).comp
        (hc.sub (continuous_const (y := sourceFieldCoefficients p d h)))
  unfold sourceFieldDistance
  exact (continuous_const.mul (continuous_const.mul
    ((continuous_const.add (continuous_const.mul (he.mul continuous_const))).sqrt.mul
      (he.mul continuous_const).sqrt))).add ((continuous_apply _).sub continuous_const).abs

lemma sourceFieldDistance_self {N k : ℕ} (p d : Fin N→ℕ) (u : Fin N→ℝ)
    (h : Fin (k+1)→ℝ) : sourceFieldDistance p d u h h=0 := by
  simp [sourceFieldDistance,indexedCoefficientSquare]

lemma sourceKernelPressure_gaussianMean (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (h : Fin (k+1)→ℝ) (a : SourceBaseData n k) :
    (∫ g, sourceKernelPressure n k f p d u h (a,g) ∂countableGaussianLaw) =
      (1/(n+1:ℕ))*indexedGaussianMean k (sourceSpinLeafKernel n k a)
        (fun x => normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1)
        (sourceEnrichedFeature (n+1) p u) (sourceFieldCoefficients p d h)-h (Fin.last k) := by
  let W : NormalizedSpin (n+1)×IndexedLeaf k→ℝ := fun x =>
    normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1
  have hW : Measurable W := by
    have hm := enrichedIndexedBoundedEnergy_measurable n a.1 k f (patternPrefix (n+1) a.1 a.2.1) (fun _ => 0)
    unfold enrichedIndexedBoundedEnergy at hm
    simpa only [mul_zero,sub_zero] using hm
  have hA (x) : |W x|≤(a.1:ℝ)*‖f‖ := normalizedPatternEnergy_bound (n+1) a.1 f _ x.1
  have hD (x) : (∑ i, sourceEnrichedFeature (n+1) p u x i^2)≤(enrichedFeatureBound (n+1) u:ℝ)^2 := by
    have he := congrArg (fun r : ℝ => r^2) (sourceEnrichedFeature_norm (n+1) p u x)
    simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le
  have he := indexedGaussianMean_add_const k (sourceSpinLeafKernel n k a) hW
    (sourceEnrichedFeature_measurable (n+1) p u) hA hD (sourceFieldCoefficients p d h)
    (-((n+1:ℕ)*h (Fin.last k)))
  simp only [sourceKernelPressure,integral_const_mul]
  change (1/(n+1:ℕ):ℝ)*indexedGaussianMean k (sourceSpinLeafKernel n k a)
    (fun x => W x + -((n+1:ℕ)*h (Fin.last k))) (sourceEnrichedFeature (n+1) p u) (sourceFieldCoefficients p d h) = _
  rw [he]
  dsimp only [W]
  field_simp
  ring

lemma sourceConditional_field_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (h' h : Fin (k+1)→ℝ) (a : SourceBaseData n k) :
    |(∫ g, sourceKernelPressure n k f p d u h' (a,g) ∂countableGaussianLaw)-
      ∫ g, sourceKernelPressure n k f p d u h (a,g) ∂countableGaussianLaw| ≤
        sourceFieldDistance p d u h' h := by
  have hW : Measurable (fun x : NormalizedSpin (n+1)×IndexedLeaf k =>
      normalizedPatternEnergy (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1) := by
    have hm := enrichedIndexedBoundedEnergy_measurable n a.1 k f (patternPrefix (n+1) a.1 a.2.1) (fun _ => 0)
    unfold enrichedIndexedBoundedEnergy at hm
    simpa only [mul_zero,sub_zero] using hm
  have H := indexedGaussianMean_comparison k (sourceSpinLeafKernel n k a)
    hW (sourceEnrichedFeature_measurable (n+1) p u)
    (sq_nonneg (enrichedFeatureBound (n+1) u:ℝ))
    (fun x => normalizedPatternEnergy_bound (n+1) a.1 f (patternPrefix (n+1) a.1 a.2.1) x.1)
    (fun x => show (∑ i, sourceEnrichedFeature (n+1) p u x i^2)≤(enrichedFeatureBound (n+1) u:ℝ)^2 from by
      have he := congrArg (fun r : ℝ => r^2) (sourceEnrichedFeature_norm (n+1) p u x)
      simpa only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] using he.le)
    (sourceFieldCoefficients p d h') (sourceFieldCoefficients p d h)
  rw [sourceKernelPressure_gaussianMean,sourceKernelPressure_gaussianMean]
  rw [show ∀ a b c e : ℝ, a-b-(c-e)=(a-c)-(b-e) by intros; ring]
  apply (abs_sub _ _).trans
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/(n+1:ℕ))]
  exact add_le_add (mul_le_mul_of_nonneg_left H (by positivity : (0:ℝ)≤1/(n+1:ℕ))) le_rfl

lemma sourceExpectedPressure_field_comparison (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (h' h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    |sourceExpectedPressure n k f p d h' z t u-sourceExpectedPressure n k f p d h z t u|≤
      sourceFieldDistance p d u h' h := by
  have hi (v) := (sourceKernelPressure_memLp n k f p d u v z hz hz0 hz1 t).integrable (by norm_num)
  unfold sourceExpectedPressure
  rw [integral_prod _ (hi h'),integral_prod _ (hi h),← integral_sub (hi h').integral_prod_left (hi h).integral_prod_left]
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := sourceBaseDataLaw n k z t)
    (f := fun a => (∫ g, sourceKernelPressure n k f p d u h' (a,g) ∂countableGaussianLaw)-
      ∫ g, sourceKernelPressure n k f p d u h (a,g) ∂countableGaussianLaw)
    (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using
      sourceConditional_field_comparison n k f p d u h' h a)

lemma sourceExpectedPressure_field_continuous (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (u : Fin (n+1)→ℝ) (z : Fin k→ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    Continuous (fun h => sourceExpectedPressure n k f p d h z t u) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (g := fun h' => sourceFieldDistance p d u h' h) ?_ ?_
  · intro h'
    simpa only [Real.norm_eq_abs] using sourceExpectedPressure_field_comparison n k f p d u h' h z hz hz0 hz1 t
  · have hc : Tendsto (fun h' => sourceFieldDistance p d u h' h) (𝓝 h)
        (𝓝 (sourceFieldDistance p d u h h)) := (sourceFieldDistance_continuous p d u h).continuousAt
    rwa [sourceFieldDistance_self] at hc

def sourceDirectionProfile {N k : ℕ} (p : Fin N→ℕ) (a : Fin (k+1)→ℝ)
    (l : Fin (k+1)) : EnrichedIndex N N p→ℝ :=
  Sum.elim (fun _ => 2*a l) (fun _ => 0)

def sourceDirectionCoefficients {N k : ℕ} (p : Fin N→ℕ) (a : Fin (k+1)→ℝ) :
    Fin (k+1)→EnrichedIndex N N p→ℝ :=
  hierarchyRowCoefficients k (profileGaussianRoot (sourceDirectionProfile p a))
    (profileGaussianStep (sourceDirectionProfile p a))

lemma sourceDirectionProfile_nonneg {N k : ℕ} (p : Fin N→ℕ) {a : Fin (k+1)→ℝ}
    (ha0 : ∀ l, 0 ≤ a l) (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    0 ≤ sourceDirectionProfile p a l i := by
  cases i with
  | inl i => exact mul_nonneg (by norm_num) (ha0 l)
  | inr i => exact le_rfl

lemma sourceDirectionProfile_monotone {N k : ℕ} (p : Fin N→ℕ) {a : Fin (k+1)→ℝ}
    (ha : Monotone a) (i : EnrichedIndex N N p) :
    Monotone (fun l => sourceDirectionProfile p a l i) := by
  cases i with
  | inl i => exact fun l m hlm => mul_le_mul_of_nonneg_left (ha hlm) (by norm_num)
  | inr i => exact monotone_const

lemma sourceFieldCoefficients_affine_covariance {N k : ℕ} (p d : Fin N→ℕ)
    {h a : Fin (k+1)→ℝ} (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a) {t : ℝ} (ht : 0 ≤ t)
    (l : Fin (k+1)) (i : EnrichedIndex N N p) :
    sourceFieldCoefficients p d (fun l => h l+t*a l) l i^2 =
      sourceFieldCoefficients p d h l i^2+t*sourceDirectionCoefficients p a l i^2 := by
  have hv (r : Fin (k+1)) : enrichedCoordinateLevel p d (fun l => h l+t*a l) r i =
      enrichedCoordinateLevel p d h r i+t*sourceDirectionProfile p a r i := by
    cases i <;> simp [enrichedCoordinateLevel,sourceDirectionProfile]
    ring
  have hq0 := enrichedCoordinateLevel_nonneg p d hh0
  have hqm := enrichedCoordinateLevel_monotone p d hh
  have hr0 := sourceDirectionProfile_nonneg p ha0
  have hrm := sourceDirectionProfile_monotone p ha
  simp only [sourceFieldCoefficients,sourceDirectionCoefficients,profileGaussian_coefficient]
  induction l using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero,hv,Real.sq_sqrt (hq0 0 i),Real.sq_sqrt (hr0 0 i)]
    rw [Real.sq_sqrt (add_nonneg (hq0 0 i) (mul_nonneg ht (hr0 0 i)))]
  | succ l =>
    have hb := sub_nonneg.mpr (hqm i (Fin.castSucc_le_succ l))
    have hc := sub_nonneg.mpr (hrm i (Fin.castSucc_le_succ l))
    simp only [Fin.cases_succ,hv,Real.sq_sqrt hb,Real.sq_sqrt hc]
    have hd : 0 ≤ enrichedCoordinateLevel p d h l.succ i+t*sourceDirectionProfile p a l.succ i-
        (enrichedCoordinateLevel p d h l.castSucc i+t*sourceDirectionProfile p a l.castSucc i) := by
      nlinarith [mul_nonneg ht hc]
    rw [Real.sq_sqrt hd]
    ring

lemma sourceDirection_feature_cross {N k : ℕ} (p : Fin N→ℕ)
    (u : Fin N→ℝ) (a : Fin (k+1)→ℝ) (l : Fin (k+1)) (x y : NormalizedSpin N) :
    (∑ i : EnrichedIndex N N p, sourceDirectionProfile p a l i*
      sourceEnrichedFeature N p u x i*sourceEnrichedFeature N p u y i) =
      2*(N:ℝ)*a l*spinOverlap x y := by
  rw [Fintype.sum_sum_type]
  simp only [sourceDirectionProfile,Sum.elim_inl,Sum.elim_inr,zero_mul,Finset.sum_const_zero,add_zero]
  change (∑ i : Fin N, 2*a l*(Real.sqrt (N:ℝ)*x.val i)*(Real.sqrt (N:ℝ)*y.val i)) =
    2*(N:ℝ)*a l*(∑ i : Fin N, y.val i*x.val i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = 2*a l*(Real.sqrt (N:ℝ))^2*(y.val i*x.val i) := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; ring

lemma sourceDirection_covariance {N k : ℕ} (p : Fin N→ℕ)
    (u : Fin N→ℝ) {a : Fin (k+1)→ℝ} (ha0 : ∀ l, 0 ≤ a l) (ha : Monotone a)
    (x y : NormalizedSpin N×IndexedLeaf k) :
    countableGaussianCovariance
      (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature N p u))
      (indexedGaussianRow k (sourceDirectionCoefficients p a) (sourceEnrichedFeature N p u))
      (indexedGaussianRowLength (I := EnrichedIndex N N p) k) x y =
      2*(N:ℝ)*a (indexedCommonDepth k y.2 x.2)*spinOverlap x.1 y.1 := by
  unfold sourceDirectionCoefficients
  rw [profileGaussianRow_covariance _ (sourceDirectionProfile_nonneg p ha0 0)
    (sourceDirectionProfile_monotone p ha),sourceDirection_feature_cross]

end SphericalPerceptronFreeEnergy
end

end OAI
