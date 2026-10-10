import Mathlib
import OAI.Probability.Perceptron.Interpolation.PerturbationContact
import OAI.Probability.Perceptron.Cascade.PoissonDensityDerivative

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def sourceCountExpectedLog (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ) (M : ℕ) : ℝ :=
  ∫ a, enrichedPoissonLog n k f p d u h (M,a) ∂enrichedRowsDisorderLaw n k p z

lemma sourceCountExpectedLog_increment (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (M : ℕ) :
    |sourceCountExpectedLog n k f p d h z u (M+1)-sourceCountExpectedLog n k f p d h z u M|≤‖f‖ :=
  enrichedPoissonLog_mean_succ n k f p d u h z hz hz0 hz1 M

lemma sourceExpectedPressure_poissonMean (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    sourceExpectedPressure n k f p d h z t u =
      (1/(n+1:ℕ))*poissonRealMean (sourceCountExpectedLog n k f p d h z u) ((n+1:ℕ)*(t:ℝ)) := by
  let P := (sourceBaseDataLaw n k z t).prod countableGaussianLaw
  have hr := sourceDisorderReassoc_preserving n k z t
  have hs := sourceDisorderRealization_preserving n k p z t
  have hi := (enrichedPoissonLog_variance n k f p d u h z hz hz0 hz1 ((n+1:ℕ)*t)).1
  have hi' : AEStronglyMeasurable (enrichedRandomPressure n k f p d u h)
      (enrichedPoissonDisorderLaw n k p z t) := (hi.const_mul (1/(n+1:ℕ))).aestronglyMeasurable
  have hm := sourceIndexedPressure_memLp n k f p d u h z hz hz0 hz1 t
  rw [sourceExpectedPressure]
  rw [integral_congr_ae ((sourceKernelPressure_ae n k f p d h z hz hz0 hz1 t).mono fun a ha => ha u)]
  rw [← integral_map hr.measurable.aemeasurable (by rw [hr.map_eq]; exact hm.aestronglyMeasurable),hr.map_eq]
  unfold sourceIndexedPressure
  change (∫ a, enrichedRandomPressure n k f p d u h (sourceDisorderRealization n k p a)
    ∂sourceIndexedDisorderLaw n k z t)=_
  rw [← integral_map hs.measurable.aemeasurable (by rw [hs.map_eq]; exact hi'),hs.map_eq]
  simp only [enrichedRandomPressure,integral_const_mul]
  apply congrArg ((1/(n+1:ℕ):ℝ)* ·)
  change (∫ a, enrichedPoissonLog n k f p d u h a ∂enrichedPoissonDisorderLaw n k p z t) =
    poissonRealMean (sourceCountExpectedLog n k f p d h z u) (((n+1:ℕ)*t:ℝ≥0):ℝ)
  rw [poissonRealMean_eq_integral (norm_nonneg f)
    (sourceCountExpectedLog_increment n k f p d h z u hz hz0 hz1) ((n+1:ℕ)*t)]
  exact integral_prod _ (hi.integrable (by norm_num))

def sourceDensityIncrement (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ) (t : ℝ≥0) : ℝ :=
  ∫ M, sourceCountExpectedLog n k f p d h z u (M+1)-sourceCountExpectedLog n k f p d h z u M
    ∂poissonMeasure ((n+1:ℕ)*t)

lemma sourceDensityIncrement_bound (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    |sourceDensityIncrement n k f p d h z u t|≤‖f‖ := by
  simpa only [sourceDensityIncrement,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := poissonMeasure ((n+1:ℕ)*t))
      (f := fun M => sourceCountExpectedLog n k f p d h z u (M+1)-sourceCountExpectedLog n k f p d h z u M)
      (ae_of_all _ fun M => by simpa only [Real.norm_eq_abs] using
        sourceCountExpectedLog_increment n k f p d h z u hz hz0 hz1 M)

lemma sourceExpectedPressure_density_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => sourceExpectedPressure n k f p d h z s.toNNReal u)
      (sourceDensityIncrement n k f p d h z u t) t := by
  let F := sourceCountExpectedLog n k f p d h z u
  have hF := sourceCountExpectedLog_increment n k f p d h z u hz hz0 hz1
  have hd := ((hasDerivAt_poissonRealMean (norm_nonneg f) hF ((n+1:ℕ)*(t:ℝ))).comp (t:ℝ)
    ((hasDerivAt_id (t:ℝ)).const_mul ((n+1:ℕ):ℝ))).const_mul (1/(n+1:ℕ):ℝ)
  have hD : poissonRealMean (fun M => F (M+1)-F M) ((n+1:ℕ)*(t:ℝ))=
      sourceDensityIncrement n k f p d h z u t := by
    have hinc : ∀ M, |(F (M+1+1)-F (M+1))-(F (M+1)-F M)|≤2*‖f‖ := fun M =>
      (abs_sub _ _).trans (by linarith [hF (M+1),hF M])
    simpa only [sourceDensityIncrement,NNReal.coe_mul,NNReal.coe_natCast] using
      poissonRealMean_eq_integral (by positivity : 0≤2*‖f‖) hinc ((n+1:ℕ)*t)
  have hd' : HasDerivAt (fun s : ℝ => (1/(n+1:ℕ))*poissonRealMean F ((n+1:ℕ)*s))
      (sourceDensityIncrement n k f p d h z u t) t := by
    apply hd.congr_deriv
    change (1/(n+1:ℕ))*(poissonRealMean _ _ *((n+1:ℕ)*1))=_
    rw [hD]
    field_simp
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0:ℝ)<(t:ℝ) from ht)] with s hs
  rw [sourceExpectedPressure_poissonMean n k f p d h z u hz hz0 hz1,
    Real.coe_toNNReal _ hs.le]

lemma sourceExpectedPressure_density_continuous (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1)→ℕ)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) :
    Continuous (fun t : ℝ≥0 => sourceExpectedPressure n k f p d h z t u) := by
  have hc : Continuous (poissonRealMean (sourceCountExpectedLog n k f p d h z u)) :=
    continuous_iff_continuousAt.mpr fun r =>
      (hasDerivAt_poissonRealMean (norm_nonneg f)
        (sourceCountExpectedLog_increment n k f p d h z u hz hz0 hz1) r).continuousAt
  simp_rw [sourceExpectedPressure_poissonMean n k f p d h z u hz hz0 hz1]
  exact continuous_const.mul (hc.comp (continuous_const.mul NNReal.continuous_coe))

end SphericalPerceptronFreeEnergy
end

end OAI
