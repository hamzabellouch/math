import OAI.Analysis.LiebThirring.LocalCompactness

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

lemma cutoff_memLp (s : Set ℝ) (hs : MeasurableSet s) (f : L2C) :
    MemLp (s.indicator f) 2 volume := (Lp.memLp f).indicator hs

def cutoffLM (s : Set ℝ) (hs : MeasurableSet s) : L2C →ₗ[ℂ] L2C where
  toFun f := (cutoff_memLp s hs f).toLp (s.indicator f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(cutoff_memLp s hs (f+g)).coeFn_toLp,
      (cutoff_memLp s hs f).coeFn_toLp,(cutoff_memLp s hs g).coeFn_toLp,
      Lp.coeFn_add ((cutoff_memLp s hs f).toLp (s.indicator f))
        ((cutoff_memLp s hs g).toLp (s.indicator g)),Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h4,h2,h3]
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      exact h5
    · simp only [indicator_of_notMem hx,zero_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(cutoff_memLp s hs (c • f)).coeFn_toLp,
      (cutoff_memLp s hs f).coeFn_toLp,
      Lp.coeFn_smul c ((cutoff_memLp s hs f).toLp (s.indicator f)),
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [Pi.smul_apply] at h3 h4
    simp only [RingHom.id_apply]
    rw [h1,h3,h2]
    by_cases hx : x ∈ s <;> simp [hx,h4]

lemma cutoffLM_norm (s : Set ℝ) (hs : MeasurableSet s) (f : L2C) :
    ‖cutoffLM s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(cutoff_memLp s hs f).coeFn_toLp] with x hx
  change ‖((cutoff_memLp s hs f).toLp (s.indicator f)) x‖ ≤ _
  rw [hx]
  exact norm_indicator_le_norm_self _ _

def cutoffL (s : Set ℝ) (hs : MeasurableSet s) : L2C →L[ℂ] L2C :=
  (cutoffLM s hs).mkContinuous 1 (by simpa only [one_mul] using cutoffLM_norm s hs)

lemma cutoffL_ae (s : Set ℝ) (hs : MeasurableSet s) (f : L2C) :
    cutoffL s hs f =ᵐ[volume] s.indicator f := (cutoff_memLp s hs f).coeFn_toLp

variable {R : ℝ} (hR : 0 ≤ R) {g : ℝ → ℂ} (hg : MemLp g 2 volume)

private def extendedBCF (f : Interval R →ᵇ ℂ) (x : ℝ) : ℂ :=
  f (projIcc (-R) R (by linarith) x)

private lemma extendedBCF_continuous (f : Interval R →ᵇ ℂ) : Continuous (extendedBCF hR f) :=
  f.continuous.comp continuous_projIcc

include hg in
private lemma weightedBCF_memLp (f : Interval R →ᵇ ℂ) :
    MemLp (fun x ↦ g x*extendedBCF hR f x) 2 volume := by
  apply hg.of_le_mul (c := ‖f‖) (hg.aestronglyMeasurable.mul (extendedBCF_continuous hR f).aestronglyMeasurable)
  exact Eventually.of_forall fun x ↦ by
    change ‖g x * extendedBCF hR f x‖ ≤ ‖f‖ * ‖g x‖
    rw [norm_mul,mul_comm ‖g x‖]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (norm_nonneg _)

def weightedBCF (f : Interval R →ᵇ ℂ) : L2C :=
  (weightedBCF_memLp hR hg f).toLp _

lemma weightedBCF_ae (f : Interval R →ᵇ ℂ) :
    weightedBCF hR hg f =ᵐ[volume] (fun x ↦ g x*extendedBCF hR f x) :=
  (weightedBCF_memLp hR hg f).coeFn_toLp

lemma weightedBCF_lipschitz (f f' : Interval R →ᵇ ℂ) :
    dist (weightedBCF hR hg f) (weightedBCF hR hg f') ≤ ‖hg.toLp g‖*dist f f' := by
  rw [dist_eq_norm,dist_eq_norm,mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedBCF_ae hR hg f,weightedBCF_ae hR hg f',
    Lp.coeFn_sub (weightedBCF hR hg f) (weightedBCF hR hg f'),hg.coeFn_toLp] with x h1 h2 h3 h4
  simp only [Pi.sub_apply] at h3
  rw [h3,h1,h2,h4,← mul_sub,norm_mul,mul_comm ‖g x‖]
  exact mul_le_mul_of_nonneg_right ((f-f').norm_coe_le_norm _) (norm_nonneg _)

lemma weightedBCF_continuous : Continuous (weightedBCF hR hg) :=
  (show LipschitzWith ⟨‖hg.toLp g‖,norm_nonneg _⟩ (weightedBCF hR hg) from
    LipschitzWith.of_dist_le_mul (weightedBCF_lipschitz hR hg)).continuous

lemma weightedBCF_localRep_ae (hsupp : ∀ x ∉ Interval R, g x = 0) (u : H1C) :
    weightedBCF hR hg (localRep R u) =ᵐ[volume] (fun x ↦ g x * valL u x) := by
  filter_upwards [weightedBCF_ae hR hg (localRep R u), continuousRep_ae u] with x hx hu
  rw [hx]
  by_cases hs : x ∈ Interval R
  · simp only [extendedBCF,projIcc_of_mem _ hs,localRep,
      BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk]
    rw [hu]
  · rw [hsupp x hs,zero_mul,zero_mul]

lemma localRep_isCompact (R : ℝ) : IsCompactOperator (localRep R) := by
  apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact (localRep R)).mpr
  exact ⟨Metric.closedBall 0 1,Metric.closedBall_mem_nhds 0 zero_lt_one,
    closure (localRep R '' Metric.closedBall 0 1),localRep_compact R,subset_closure⟩

lemma weightedBCF_localRep_isCompact :
    IsCompactOperator (fun u : H1C ↦ weightedBCF hR hg (localRep R u)) :=
  (localRep_isCompact R).continuous_comp (weightedBCF_continuous hR hg)

end SharpLiebThirring.OperatorProof

end

end OAI
