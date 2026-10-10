import OAI.Analysis.NodalLength.Potential

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

def parametrixCutoff : ContDiffBump (0:Plane) := ⟨1/8,1/4,by norm_num,by norm_num⟩
def parametrixInner : ContDiffBump (0:Plane) := ⟨1/16,1/8,by norm_num,by norm_num⟩
def parametrixSmoothLog (x : Plane) : ℝ := Real.log (‖x‖^2+(parametrixInner x)^2)/2

def parametrixCorrection (x : Plane) : ℝ := (parametrixCutoff x-1)*parametrixSmoothLog x
def parametrixKernel (x : Plane) : ℝ := euclideanLaplacian parametrixCorrection x
def logParametrix (x : Plane) : ℝ := parametrixCutoff x*Real.log ‖x‖

lemma smooth_parametrixSmoothLog : Smooth parametrixSmoothLog := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact (contDiff_id.norm_sq (𝕜:=ℝ)).add (parametrixInner.contDiff.pow 2)
  · intro x
    by_cases hx : x=0
    · subst x
      have ho : parametrixInner (0:Plane)=1 := parametrixInner.one_of_mem_closedBall (by simp [parametrixInner,Metric.mem_closedBall])
      simp [ho]
    · have hpos : 0<‖x‖^2+(parametrixInner x)^2 :=
        add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hx)) (sq_nonneg _)
      exact hpos.ne'

lemma smooth_parametrixCorrection : Smooth parametrixCorrection :=
  (parametrixCutoff.contDiff.sub contDiff_const).mul smooth_parametrixSmoothLog
lemma smooth_parametrixKernel : Smooth parametrixKernel := smooth_laplacian smooth_parametrixCorrection

lemma parametrixSmoothLog_eq {x : Plane} (hx : (1/8:ℝ)≤‖x‖) :
    parametrixSmoothLog x=Real.log ‖x‖ := by
  have hz : parametrixInner x=0 := parametrixInner.zero_of_le_dist (by simpa [parametrixInner,dist_zero_right] using hx)
  simp only [parametrixSmoothLog,hz,zero_pow (by decide : (2:ℕ)≠0),add_zero,Real.log_pow,Nat.cast_ofNat]
  ring

lemma logParametrix_eq (x : Plane) :
    logParametrix x=Real.log ‖x‖+parametrixCorrection x := by
  by_cases hx : ‖x‖≤(1/8:ℝ)
  · have ho : parametrixCutoff x=1 := parametrixCutoff.one_of_mem_closedBall (by simpa [parametrixCutoff,Metric.mem_closedBall,dist_zero_right] using hx)
    simp [logParametrix,parametrixCorrection,ho]
  · rw [parametrixCorrection,parametrixSmoothLog_eq (le_of_not_ge hx)]
    dsimp [logParametrix]; ring

lemma laplacian_of_log_germ {f : Plane → ℝ} (hf : Smooth f) {x : Plane} (hx : x≠0)
    (he : f=ᶠ[𝓝 x](fun y => Real.log ‖y‖)) : euclideanLaplacian f x=0 := by
  let g : ℂ → ℝ := f∘planeComplex.symm
  have hg : ContDiff ℝ ∞ g := hf.comp planeComplex.symm.toContinuousLinearEquiv.contDiff
  have hh : HarmonicAt (fun z : ℂ => Real.log ‖z‖) (planeComplex x) :=
    analyticAt_id.harmonicAt_log_norm (by simpa using hx)
  have he' : g=ᶠ[𝓝 (planeComplex x)](fun z : ℂ => Real.log ‖z‖) := by
    have htend : Tendsto planeComplex.symm (𝓝 (planeComplex x)) (𝓝 x) := by
      simpa only [planeComplex.symm_apply_apply] using (planeComplex.symm.continuous.continuousAt (x:=planeComplex x)).tendsto
    have ht := he.comp_tendsto htend
    filter_upwards [ht] with z hz
    simpa only [g,Function.comp_apply,LinearIsometryEquiv.norm_map] using hz
  have hhg : HarmonicAt g (planeComplex x) := (harmonicAt_congr_nhds he').mpr hh
  have hzero := hhg.2.self_of_nhds
  have heq := congrFun (laplacian_comp_isometry planeComplex.symm hf) (planeComplex x)
  rw [← plane_laplacian_eq_mathlib hf] at heq
  simpa only [g,Function.comp_apply,planeComplex.symm_apply_apply,Pi.zero_apply] using heq.symm.trans hzero

lemma parametrixKernel_zero {x : Plane} (hx : (1/4:ℝ)<‖x‖) : parametrixKernel x=0 := by
  have he : (fun y => -parametrixCorrection y)=ᶠ[𝓝 x](fun y => Real.log ‖y‖) := by
    filter_upwards [(continuous_norm.continuousAt.eventually (eventually_gt_nhds hx))] with y hy
    have hz : parametrixCutoff y=0 := parametrixCutoff.zero_of_le_dist (by simpa [parametrixCutoff,dist_zero_right] using hy.le)
    rw [parametrixCorrection,hz,parametrixSmoothLog_eq (by linarith)]
    ring
  have hh := laplacian_of_log_germ smooth_parametrixCorrection.neg (by intro h; norm_num [h] at hx) he
  have heq : (fun y => -parametrixCorrection y)=(fun y => (-1:ℝ)*parametrixCorrection y) := by funext y; ring
  rw [heq,laplacian_const_mul smooth_parametrixCorrection] at hh
  simpa only [neg_one_mul,neg_eq_zero,parametrixKernel] using hh

lemma compact_parametrixKernel : HasCompactSupport parametrixKernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (1/4:ℝ))
  intro x hx
  exact parametrixKernel_zero (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx)

lemma logParametrix_zero {x : Plane} (hx : (1/4:ℝ)≤‖x‖) : logParametrix x=0 := by
  have hz : parametrixCutoff x=0 := parametrixCutoff.zero_of_le_dist (by simpa [parametrixCutoff,dist_zero_right] using hx)
  simp [logParametrix,hz]

lemma integral_parametrix_identity {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) :
    (∫x,logParametrix x*euclideanLaplacian ψ x)=2*Real.pi*ψ 0+(∫x,parametrixKernel x*ψ x) := by
  have hlog : Integrable (fun x : Plane => Real.log ‖x‖*euclideanLaplacian ψ x) := by
    obtain ⟨R,hR,hzero⟩ := (compact_laplacian hcψ).exists_pos_le_norm
    obtain ⟨M,hM⟩ := (smooth_laplacian hψ).continuous.norm.bddAbove_range_of_hasCompactSupport (compact_laplacian hcψ).norm
    have hi := (IntegrableOn.integrable_indicator ((log_norm_integrableOn_ball R).norm) measurableSet_ball).mul_const M
    apply hi.mono' ((Real.measurable_log.comp measurable_norm).mul (smooth_laplacian hψ).continuous.measurable).aestronglyMeasurable
    filter_upwards [] with x
    change ‖Real.log ‖x‖*euclideanLaplacian ψ x‖≤((Metric.ball (0:Plane) R).indicator (fun x => ‖Real.log ‖x‖‖) x)*M
    by_cases hx : x∈Metric.ball (0:Plane) R
    · rw [indicator_of_mem hx,norm_mul]
      exact mul_le_mul_of_nonneg_left (hM (mem_range_self x)) (norm_nonneg _)
    · rw [hzero x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx),mul_zero,norm_zero,indicator_of_notMem hx,zero_mul]
  have hc : Integrable (fun x => parametrixCorrection x*euclideanLaplacian ψ x) :=
    integrable_mul_compact_right smooth_parametrixCorrection (smooth_laplacian hψ) (compact_laplacian hcψ)
  simp_rw [logParametrix_eq,add_mul]
  rw [integral_add hlog hc,logarithmic_fundamental_solution hψ hcψ,integral_mul_laplacian smooth_parametrixCorrection hψ hcψ]
  rfl
end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def rconv (f g : Plane → ℝ) : Plane → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] g
lemma rconv_eq (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f y*g (x-y) := rfl
lemma rconv_swap (f g : Plane → ℝ) (x : Plane) : rconv f g x=∫y,f (x-y)*g y :=
  convolution_eq_swap (ContinuousLinearMap.mul ℝ ℝ)

lemma smooth_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Smooth (rconv f g) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hg

lemma partial_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    coordPartial (rconv f g) i=rconv f (coordPartial g i) := by
  funext x
  have hh := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf.locallyIntegrable (hg.of_le (by simp : (1:ℕ∞ω)≤(∞:ℕ∞ω))) x
  have he : fderiv ℝ (rconv f g) x=(f ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR Plane,volume] fderiv ℝ g) x := by
    convert! hh.fderiv using 1
  change (fderiv ℝ (rconv f g) x) _=_
  rw [he,convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable
    (hc.fderiv ℝ) ((hg.fderiv_right (by simp : (∞:ℕ∞ω)+1≤(∞:ℕ∞ω))).continuous)]
  rfl

lemma laplacian_rconv {f g : Plane → ℝ} (hf : Integrable f) (hg : Smooth g)
    (hc : HasCompactSupport g) :
    euclideanLaplacian (rconv f g)=rconv f (euclideanLaplacian g) := by
  funext x
  simp only [euclideanLaplacian,partial_rconv hf hg hc,
    partial_rconv hf (smooth_partial hg _) (compact_partial hc _)]
  simp only [rconv_eq,euclideanLaplacian,Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact (compact_partial (compact_partial hc i) i).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable (smooth_partial (smooth_partial hg i) i).continuous x

lemma partial_reflection {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) (i : Fin 2) :
    coordPartial (fun y => f (z-y)) i x= -coordPartial f i (z-x) := by
  have hh := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).const_sub z)
  have he : fderiv ℝ (fun y => f (z-y)) x= -(fderiv ℝ f (z-x)) := by
    convert! hh.fderiv using 1
    ext v
    simp
  change (fderiv ℝ (fun y => f (z-y)) x) _=_
  rw [he]
  rfl

lemma laplacian_reflection {f : Plane → ℝ} (hf : Smooth f) (z x : Plane) :
    euclideanLaplacian (fun y => f (z-y)) x=euclideanLaplacian f (z-x) := by
  unfold euclideanLaplacian
  apply Finset.sum_congr rfl
  intro i _
  have hrf : Smooth (fun y => coordPartial f i (z-y)) := (smooth_partial hf i).comp (contDiff_const.sub contDiff_id)
  rw [show coordPartial (fun y => f (z-y)) i=(fun y => -coordPartial f i (z-y)) from funext (fun y => partial_reflection hf z y i),
    partial_neg hrf,
    partial_reflection (smooth_partial hf i),neg_neg]

lemma compact_reflection {f : Plane → ℝ} (hc : HasCompactSupport f) (z : Plane) :
    HasCompactSupport (fun y => f (z-y)) := by
  convert! hc.comp_homeomorph ((Homeomorph.neg Plane).trans (Homeomorph.addRight z)) using 1
  ext y
  congr 1
  change z-y= -y+z
  abel

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma integrable_logParametrix : Integrable logParametrix := by
  let F := (Metric.ball (0:Plane) 1).indicator (fun x => Real.log ‖x‖)
  have hi : Integrable F := (log_norm_integrableOn_ball 1).integrable_indicator measurableSet_ball
  have he : logParametrix=(fun x => parametrixCutoff x*F x) := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) 1
    · simp [logParametrix,F,hx]
    · have hn : 1≤‖x‖ := by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx
      rw [logParametrix_zero (by linarith)]
      simp [F,hx]
  rw [he]
  exact hi.bdd_mul parametrixCutoff.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (parametrixCutoff.nonneg)] using parametrixCutoff.le_one))

lemma compact_logParametrix : HasCompactSupport logParametrix := by
  apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) (1/4:ℝ))
  intro x hx
  have hh : (1/4:ℝ)<‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  exact logParametrix_zero hh.le

lemma laplacian_parametrix_convolution {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) (x : Plane) :
    euclideanLaplacian (rconv logParametrix ψ) x=2*Real.pi*ψ x+rconv parametrixKernel ψ x := by
  rw [laplacian_rconv integrable_logParametrix hψ hcψ,rconv_eq,rconv_eq]
  have hs : Smooth (fun y => ψ (x-y)) := hψ.comp (contDiff_const.sub contDiff_id)
  have hh := integral_parametrix_identity hs (compact_reflection hcψ x)
  simpa only [laplacian_reflection hψ,sub_zero] using hh

lemma parametrix_convolution_support {ψ : Plane → ℝ}
    (hs : tsupport ψ⊆Metric.ball (0:Plane) 3) :
    HasCompactSupport (rconv logParametrix ψ) ∧ tsupport (rconv logParametrix ψ)⊆Metric.ball (0:Plane) 4 := by
  have hzero : ∀x, (13/4:ℝ)≤‖x‖ → rconv logParametrix ψ x=0 := by
    intro x hx
    rw [rconv_eq]
    apply integral_eq_zero_of_ae
    filter_upwards [] with y
    change logParametrix y*ψ (x-y)=0
    by_cases hy : (1/4:ℝ)≤‖y‖
    · rw [logParametrix_zero hy,zero_mul]
    · have hy' : ‖y‖<(1/4:ℝ) := lt_of_not_ge hy
      have hn : 3<‖x-y‖ := by have ht := norm_sub_norm_le x y; linarith
      have hz : ψ (x-y)=0 := image_eq_zero_of_notMem_tsupport (fun ht => by
        have hb : ‖x-y‖<3 := by simpa only [Metric.mem_ball,dist_zero_right] using hs ht
        linarith)
      rw [hz,mul_zero]
  have hts : tsupport (rconv logParametrix ψ)⊆Metric.closedBall (0:Plane) (13/4:ℝ) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra hn
    have hn' : (13/4:ℝ)<‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hn
    exact hx (hzero x hn'.le)
  refine ⟨(isCompact_closedBall (0:Plane) (13/4:ℝ)).of_isClosed_subset (isClosed_tsupport _) hts,?_⟩
  intro x hx
  have hn : ‖x‖≤(13/4:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hts hx
  change dist x 0<4
  rw [dist_zero_right]
  linarith

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma rconv_duality {w φ K : Plane → ℝ} (hw : Integrable w) (hφ : Integrable φ)
    (hK : Continuous K) (hcK : HasCompactSupport K) :
    (∫x,w x*rconv K φ x)=(∫x,rconv w (fun y => K (-y)) x*φ x) := by
  obtain ⟨M,hM⟩ := hK.norm.bddAbove_range_of_hasCompactSupport hcK.norm
  have hp : Integrable (fun p : Plane×Plane => w p.1*K (p.1-p.2)*φ p.2) (volume.prod volume) := by
    apply ((hw.norm.mul_prod hφ.norm).mul_const M).mono'
      ((hw.aestronglyMeasurable.comp_fst.mul (hK.measurable.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul hφ.aestronglyMeasurable.comp_snd)
    filter_upwards [] with p
    change ‖w p.1*K (p.1-p.2)*φ p.2‖≤(‖w p.1‖*‖φ p.2‖)*M
    rw [norm_mul,norm_mul]
    calc
      _ ≤ ‖w p.1‖*M*‖φ p.2‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hM (mem_range_self (p.1-p.2))) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ = ∫x,∫z,w x*K (x-z)*φ z := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [rconv_swap,← integral_const_mul,mul_assoc]
    _ = ∫z,∫x,w x*K (x-z)*φ z := integral_integral_swap hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [rconv_eq,neg_sub,integral_mul_const]

lemma norm_rconv_le {w K : Plane → ℝ} (hw : Integrable w)
    (hK : Continuous K) (hcK : HasCompactSupport K) {C : ℝ} (hC : ∀x,‖K x‖≤C) (x : Plane) :
    ‖rconv w K x‖≤C*(∫y,‖w y‖) := by
  have hi := hcK.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hw.locallyIntegrable hK x
  calc
    _ ≤ ∫y,‖w y*K (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫y,‖w y‖*C := by
      apply integral_mono_ae hi.norm (hw.norm.mul_const C)
      filter_upwards [] with y
      change ‖w y*K (x-y)‖≤‖w y‖*C
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC (x-y)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const,mul_comm]

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

def WeakHarmonicOn (w : Plane → ℝ) (Ω : Set Plane) : Prop :=
  ∀ (ψ : Plane → ℝ), Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
    (∫x,w x*euclideanLaplacian ψ x)=0

def weylRepresentative (w : Plane → ℝ) : Plane → ℝ :=
  fun x => -(2*Real.pi)⁻¹*rconv w (fun y => parametrixKernel (-y)) x

lemma smooth_weylRepresentative {w : Plane → ℝ} (hw : Integrable w) :
    Smooth (weylRepresentative w) := by
  apply contDiff_const.mul
  exact smooth_rconv hw (smooth_parametrixKernel.comp contDiff_id.neg)
    (compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane))

lemma weylRepresentative_test {w : Plane → ℝ} (hw : Integrable w)
    (hweak : WeakHarmonicOn w (Metric.ball (0:Plane) 4)) {ψ : Plane → ℝ}
    (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ⊆Metric.ball (0:Plane) 3) :
    (∫x,w x*ψ x)=(∫x,weylRepresentative w x*ψ x) := by
  have hiψ : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hcψ
  have hiK : Integrable parametrixKernel := smooth_parametrixKernel.continuous.integrable_of_hasCompactSupport compact_parametrixKernel
  have hcv : Smooth (rconv parametrixKernel ψ) := smooth_rconv hiK hψ hcψ
  have hccv : HasCompactSupport (rconv parametrixKernel ψ) :=
    compact_parametrixKernel.convolution (ContinuousLinearMap.mul ℝ ℝ) hcψ
  have hi1 := integrable_mul_continuous_compact hw hψ.continuous hcψ
  have hi2 := integrable_mul_continuous_compact hw hcv.continuous hccv
  obtain ⟨hcQ,hsQ⟩ := parametrix_convolution_support hsψ
  have h0 := hweak (rconv logParametrix ψ) (smooth_rconv integrable_logParametrix hψ hcψ) hcQ hsQ
  simp_rw [laplacian_parametrix_convolution hψ hcψ] at h0
  have he : (fun x => w x*(2*Real.pi*ψ x+rconv parametrixKernel ψ x))=
      (fun x => (2*Real.pi)*(w x*ψ x)+w x*rconv parametrixKernel ψ x) := by funext x; ring
  rw [he,integral_add (hi1.const_mul _) hi2,integral_const_mul,
    rconv_duality hw hiψ smooth_parametrixKernel.continuous compact_parametrixKernel] at h0
  have he' : (fun x => weylRepresentative w x*ψ x)=
      (fun x => -(2*Real.pi)⁻¹*(rconv w (fun y => parametrixKernel (-y)) x*ψ x)) := by
    funext x; dsimp [weylRepresentative]; ring
  rw [he',integral_const_mul]
  have hp : 2*Real.pi≠0 := by positivity
  field_simp
  linarith

lemma weylRepresentative_ae {w : Plane → ℝ} (hw : Integrable w)
    (hweak : WeakHarmonicOn w (Metric.ball (0:Plane) 4)) :
    ∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → w x=weylRepresentative w x := by
  have hh := smooth_weylRepresentative hw
  have ha := Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hw.locallyIntegrable.sub hh.continuous.locallyIntegrable).locallyIntegrableOn (Metric.ball (0:Plane) 3))
    (fun ψ hψ hcψ hsψ => ?_)
  · filter_upwards [ha] with x hx hmem
    exact sub_eq_zero.mp (hx hmem)
  have hiw := integrable_mul_continuous_compact hw hψ.continuous hcψ
  have hih := integrable_mul_compact_right hh hψ hcψ
  have he : (fun x => ψ x • (w x-weylRepresentative w x))=
      (fun x => w x*ψ x-weylRepresentative w x*ψ x) := by funext x; simp only [smul_eq_mul]; ring
  change (∫x,ψ x • (w x-weylRepresentative w x))=0
  rw [he,integral_sub hiw hih,weylRepresentative_test hw hweak hψ hcψ hsψ,sub_self]

lemma weakHarmonic_smooth {h : Plane → ℝ} (hh : Smooth h) {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hweak : WeakHarmonicOn h Ω) :
    ∀x∈Ω,euclideanLaplacian h x=0 := by
  have hΔ := smooth_laplacian hh
  have ha : ∀ᵐx : Plane,x∈Ω → euclideanLaplacian h x=0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hΔ.continuous.locallyIntegrable.locallyIntegrableOn Ω)
    intro ψ hψ hcψ hsψ
    have hi := hweak ψ hψ hcψ hsψ
    rw [integral_mul_laplacian hh hψ hcψ] at hi
    simpa only [smul_eq_mul,mul_comm] using hi
  have hae : euclideanLaplacian h=ᵐ[volume.restrict Ω]0 := by
    filter_upwards [ae_restrict_of_ae ha,self_mem_ae_restrict hΩ.measurableSet] with x hx hmem
    exact hx hmem
  exact Measure.eqOn_open_of_ae_eq hae hΩ hΔ.continuous.continuousOn continuous_const.continuousOn

lemma weylRepresentative_harmonic {w : Plane → ℝ} (hw : Integrable w)
    (hweak : WeakHarmonicOn w (Metric.ball (0:Plane) 4)) :
    ∀x∈Metric.ball (0:Plane) 3,euclideanLaplacian (weylRepresentative w) x=0 := by
  apply weakHarmonic_smooth (smooth_weylRepresentative hw) Metric.isOpen_ball
  intro ψ hψ hcψ hsψ
  have he : (fun x => weylRepresentative w x*euclideanLaplacian ψ x)=ᵐ[volume]
      (fun x => w x*euclideanLaplacian ψ x) := by
    filter_upwards [weylRepresentative_ae hw hweak] with x hx
    by_cases hm : x∈Metric.ball (0:Plane) 3
    · rw [hx hm]
    · have hz : euclideanLaplacian ψ x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hm (hsψ (laplacian_tsupport_subset ψ ht)))
      simp only [hz,mul_zero]
  rw [integral_congr_ae he]
  apply hweak ψ hψ hcψ
  intro x hx
  exact Metric.ball_subset_ball (by norm_num : (3:ℝ)≤4) (hsψ hx)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma partial_weylRepresentative {w : Plane → ℝ} (hw : Integrable w) (i : Fin 2) (x : Plane) :
    coordPartial (weylRepresentative w) i x = -(2*Real.pi)⁻¹*
      rconv w (coordPartial (fun y => parametrixKernel (-y)) i) x := by
  have hk : Smooth (fun y => parametrixKernel (-y)) := smooth_parametrixKernel.comp contDiff_id.neg
  have hc : HasCompactSupport (fun y => parametrixKernel (-y)) := compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane)
  change coordPartial (fun y => -(2*Real.pi)⁻¹*rconv w (fun z => parametrixKernel (-z)) y) i x = _
  rw [partial_const_mul (smooth_rconv hw hk hc),partial_rconv hw hk hc]

lemma partial2_weylRepresentative {w : Plane → ℝ} (hw : Integrable w) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial (weylRepresentative w) i) j x = -(2*Real.pi)⁻¹*
      rconv w (coordPartial (coordPartial (fun y => parametrixKernel (-y)) i) j) x := by
  have hk : Smooth (fun y => parametrixKernel (-y)) := smooth_parametrixKernel.comp contDiff_id.neg
  have hc : HasCompactSupport (fun y => parametrixKernel (-y)) := compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane)
  have he : coordPartial (weylRepresentative w) i =
      (fun x => -(2*Real.pi)⁻¹*rconv w (coordPartial (fun y => parametrixKernel (-y)) i) x) := by
    funext x; exact partial_weylRepresentative hw i x
  rw [he,partial_const_mul (smooth_rconv hw (smooth_partial hk i) (compact_partial hc i)),
    partial_rconv hw (smooth_partial hk i) (compact_partial hc i)]

lemma uniform_weyl_derivative_bounds : ∃C : ℝ,0≤C ∧ ∀w : Plane → ℝ, Integrable w →
    ∀x : Plane, (∀i : Fin 2,|coordPartial (weylRepresentative w) i x|≤C*∫y,‖w y‖) ∧
      (∀i j : Fin 2,|coordPartial (coordPartial (weylRepresentative w) i) j x|≤C*∫y,‖w y‖) := by
  let K := fun y : Plane => parametrixKernel (-y)
  have hk : Smooth K := smooth_parametrixKernel.comp contDiff_id.neg
  have hc : HasCompactSupport K := compact_parametrixKernel.comp_homeomorph (Homeomorph.neg Plane)
  have hbound (f : Plane → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f) : ∃C : ℝ,0≤C ∧ ∀x,‖f x‖≤C := by
    obtain ⟨C,hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hcf.norm
    refine ⟨max 0 C,le_max_left _ _,fun x => ?_⟩
    exact (hC (mem_range_self x)).trans (le_max_right _ _)
  choose C₁ hC₁p hC₁ using fun i : Fin 2 => hbound (coordPartial K i) (smooth_partial hk i).continuous (compact_partial hc i)
  choose C₂ hC₂p hC₂ using fun i j : Fin 2 => hbound (coordPartial (coordPartial K i) j)
    (smooth_partial (smooth_partial hk i) j).continuous (compact_partial (compact_partial hc i) j)
  let C := (∑i,C₁ i)+(∑i,∑j,C₂ i j)
  have hCp : 0≤C := add_nonneg (Finset.sum_nonneg (fun i _ => hC₁p i))
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC₂p i j)))
  have hb₁ (i : Fin 2) : C₁ i≤C := by
    exact (Finset.single_le_sum (fun j _ => hC₁p j) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC₂p i j))))
  have hb₂ (i j : Fin 2) : C₂ i j≤C := by
    exact ((Finset.single_le_sum (fun j _ => hC₂p i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hC₂p i j)) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => hC₁p i)))
  refine ⟨|(2*Real.pi)⁻¹| *C,mul_nonneg (abs_nonneg _) hCp,?_⟩
  intro w hw x
  constructor
  · intro i
    rw [partial_weylRepresentative hw,abs_mul,abs_neg,← Real.norm_eq_abs]
    calc
      _ ≤ |(2*Real.pi)⁻¹| *(C*∫y,‖w y‖) := mul_le_mul_of_nonneg_left
        ((norm_rconv_le hw (smooth_partial hk i).continuous (compact_partial hc i) (fun z => (hC₁ i z).trans (hb₁ i)) x)) (abs_nonneg _)
      _ = _ := by simp only [Real.norm_eq_abs]; ring
  · intro i j
    rw [partial2_weylRepresentative hw,abs_mul,abs_neg,← Real.norm_eq_abs]
    calc
      _ ≤ |(2*Real.pi)⁻¹| *(C*∫y,‖w y‖) := mul_le_mul_of_nonneg_left
        ((norm_rconv_le hw (smooth_partial (smooth_partial hk i) j).continuous
          (compact_partial (compact_partial hc i) j) (fun z => (hC₂ i j z).trans (hb₂ i j)) x)) (abs_nonneg _)
      _ = _ := by simp only [Real.norm_eq_abs]; ring

end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
