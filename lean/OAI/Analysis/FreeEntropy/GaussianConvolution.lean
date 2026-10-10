import OAI.Analysis.FreeEntropy.CompactIntegration

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
def smoothedDensity (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫a,normalKernel s (x-a) ∂μ
def smoothedTimeDerivative (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∫a,normalTimeDerivative s (x-a) ∂μ
def smoothedGradient (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ :=
  ∫a,normalGradient s (x-a) i ∂μ
def smoothedSecond (μ : Measure (EuclideanSpace ℝ ι)) (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ :=
  ∫a,normalSecond s (x-a) i ∂μ
 theorem normalKernel_le (s : ℝ) (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x ≤ Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)) := by
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))
 theorem normalKernel_integrable_finite (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) : Integrable (fun a => normalKernel s (x-a)) μ := by
  apply (integrable_const (Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)))).mono'
    (((normalKernel_continuous_space s).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun a => by change ‖normalKernel s (x-a)‖≤_; rw [Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _)]; exact normalKernel_le s hs _)
 theorem smoothedDensity_pos (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) : 0<smoothedDensity μ s x := by
  rw [smoothedDensity,integral_pos_iff_support_of_nonneg (fun a => (normalKernel_pos _ _).le) (normalKernel_integrable_finite μ hs x)]
  have h : Function.support (fun a => normalKernel s (x-a))=univ := by
    ext a; simp [Function.mem_support,(normalKernel_pos s (x-a)).ne']
  simp [h]
 theorem smoothedDensity_continuous (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Continuous (smoothedDensity μ s) := by
  apply continuous_of_dominated (bound := fun _ => Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)))
  · intro x; exact (normalKernel_integrable_finite μ hs x).aestronglyMeasurable
  · intro x; exact ae_of_all _ (fun a => by change ‖normalKernel s (x-a)‖≤_; rw [Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _)]; exact normalKernel_le s hs _)
  · exact integrable_const _
  · exact ae_of_all _ (fun a => (normalKernel_continuous_space s).comp (continuous_id.sub continuous_const))
 theorem normalKernel_product_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Integrable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => normalKernel s (z.2-z.1)) (μ.prod volume) := by
  apply (integrable_prod_iff (((normalKernel_continuous_space s).comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable)).mpr
  constructor
  · exact ae_of_all _ (fun a => (normalKernel_integrable hs).comp_sub_right a)
  · simpa only [Function.comp_apply,Pi.sub_apply,Prod.fst,Prod.snd,Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _),integral_sub_right_eq_self,normalKernel_integral hs] using (integrable_const (1:ℝ) : Integrable (fun _ : EuclideanSpace ℝ ι => (1:ℝ)) μ)
 theorem smoothedDensity_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Integrable (smoothedDensity μ s) := by
  exact (normalKernel_product_integrable μ hs).integral_prod_right
 theorem smoothedDensity_integral (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : ∫x,smoothedDensity μ s x = 1 := by
  unfold smoothedDensity
  rw [integral_integral_swap (f := fun x a => normalKernel s (x-a)) (show Integrable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => normalKernel s (z.1-z.2)) (volume.prod μ) from (normalKernel_product_integrable μ hs).swap)]
  simp only [integral_sub_right_eq_self,normalKernel_integral hs,integral_const,probReal_univ,one_smul]
 theorem smoothedDensity_hasDeriv_time (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K)
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t => smoothedDensity μ t x) (smoothedTimeDerivative μ s x) s := by
  apply (hasDerivAt_integral_compact μ hK hμ (fun t a => normalKernel t (x-a)) (fun t a => normalTimeDerivative t (x-a))
    (a := s/2) (b := s+1) (by linarith) (by linarith) ?_ ?_ ?_ ?_).2
  · intro t ht; exact (normalKernel_continuous_space t).comp (continuous_const.sub continuous_id)
  · intro t ht
    unfold normalTimeDerivative normalKernel
    fun_prop
  · apply normalTimeDerivative_continuousOn.comp ((continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn)
    intro z hz; dsimp; linarith [hz.1.1]
  · intro t ht a ha
    exact normalKernel_hasDeriv_time (by linarith [ht.1]) (x-a)
 theorem smoothedDensity_hasDeriv_coordinate [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K)
    (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t => smoothedDensity μ s (x+t • EuclideanSpace.single i 1))
      (smoothedGradient μ s (x+r • EuclideanSpace.single i 1) i) r := by
  apply (hasDerivAt_integral_compact μ hK hμ (fun t a => normalKernel s (x+t • EuclideanSpace.single i 1-a))
    (fun t a => normalGradient s (x+t • EuclideanSpace.single i 1-a) i) (a := r-1) (b := r+1) (by linarith) (by linarith) ?_ ?_ ?_ ?_).2
  · intro t ht; exact (normalKernel_continuous_space s).comp (continuous_const.sub continuous_id)
  · intro t ht; exact (normalGradient_continuous s i).comp (continuous_const.sub continuous_id)
  · exact ((normalGradient_continuous s i).comp ((continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd)).continuousOn
  · intro t ht a ha
    simpa only [add_sub_right_comm] using normalKernel_hasDeriv_coordinate_at s (x-a) i t
 theorem smoothedGradient_hasDeriv_coordinate [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K)
    (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t => smoothedGradient μ s (x+t • EuclideanSpace.single i 1) i)
      (smoothedSecond μ s (x+r • EuclideanSpace.single i 1) i) r := by
  apply (hasDerivAt_integral_compact μ hK hμ (fun t a => normalGradient s (x+t • EuclideanSpace.single i 1-a) i)
    (fun t a => normalSecond s (x+t • EuclideanSpace.single i 1-a) i) (a := r-1) (b := r+1) (by linarith) (by linarith) ?_ ?_ ?_ ?_).2
  · intro t ht; exact (normalGradient_continuous s i).comp (continuous_const.sub continuous_id)
  · intro t ht; exact (normalSecond_continuous s i).comp (continuous_const.sub continuous_id)
  · exact ((normalSecond_continuous s i).comp ((continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd)).continuousOn
  · intro t ht a ha
    simpa only [add_sub_right_comm] using normalGradient_hasDeriv_coordinate s (x-a) i t
 theorem smoothed_heatEquation (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K) (s : ℝ) (x : EuclideanSpace ℝ ι) :
    smoothedTimeDerivative μ s x = (1/2:ℝ)*∑i, smoothedSecond μ s x i := by
  classical
  unfold smoothedTimeDerivative smoothedSecond
  simp only [normal_heatEquation,integral_const_mul]
  rw [integral_finsetSum]
  intro i hi
  exact integrable_of_compact_ae μ hK hμ (((normalSecond_continuous s i).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (((normalSecond_continuous s i).comp (continuous_const.sub continuous_id)).continuousOn)
end FiniteEntropySeparation

end

end OAI
