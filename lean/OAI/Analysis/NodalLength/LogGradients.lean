import OAI.Analysis.NodalLength.StoppedTrees

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
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

def logGradient (x : Plane) : Plane := (‖x‖^2)⁻¹ • x

lemma norm_logGradient (x : Plane) : ‖logGradient x‖=‖x‖⁻¹ := by
  by_cases hx : x=0
  · simp [hx,logGradient]
  · have hn := norm_pos_iff.mpr hx
    rw [logGradient,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(‖x‖^2)⁻¹)]
    field_simp

lemma measurable_logGradient : Measurable logGradient :=
  ((measurable_id.norm.pow_const 2).inv).smul measurable_id

lemma inv_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Plane => ‖x‖⁻¹) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (α:=1) (C:=1) (by simp [Plane]) (by simp [Plane])
    _ (measurable_id.norm.inv.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Pi.inv_apply,id_eq,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    Real.rpow_neg_one,one_mul,le_refl]

lemma inverse_translate_local {R S : ℝ} {z : Plane} (hz : ‖z‖<S) :
    IntegrableOn (fun x : Plane => ‖x-z‖⁻¹) (Metric.ball 0 R) ∧
    (∫x in Metric.ball (0:Plane) R,‖x-z‖⁻¹) ≤
      ∫x in Metric.ball (0:Plane) (R+S),‖x‖⁻¹ := by
  let F := (Metric.ball (0:Plane) (R+S)).indicator (fun x => ‖x‖⁻¹)
  have hiF : Integrable F := (inv_norm_integrableOn_ball (R+S)).integrable_indicator measurableSet_ball
  have hit : Integrable (fun x : Plane => F (x-z)) :=
    (measurePreserving_sub_right volume z).integrable_comp hiF.aestronglyMeasurable |>.mpr hiF
  have he : ∀x∈Metric.ball (0:Plane) R,‖x-z‖⁻¹=F (x-z) := by
    intro x hx
    have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
    have hnorm : ‖x-z‖<R+S := (norm_sub_le x z).trans_lt (add_lt_add hxR hz)
    simp only [F,indicator_of_mem (show x-z∈Metric.ball (0:Plane) (R+S) by simpa only [Metric.mem_ball,dist_zero_right] using hnorm)]
  refine ⟨hit.integrableOn.congr_fun (fun x hx => (he x hx).symm) measurableSet_ball,?_⟩
  calc
    _ = ∫x in Metric.ball (0:Plane) R,F (x-z) := setIntegral_congr_fun measurableSet_ball (fun x hx => he x hx)
    _ ≤ ∫x,F (x-z) := integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall (fun x => indicator_nonneg (fun x _ => inv_nonneg.mpr (norm_nonneg x)) _)) hit
    _ = ∫x,F x := integral_sub_right_eq_self F z
    _ = _ := by rw [integral_indicator measurableSet_ball]

lemma inversePotential_prod_integrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    Integrable (fun p : Plane×Plane => ‖p.1-p.2‖⁻¹)
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
  have hm : Measurable (fun p : Plane×Plane => ‖p.1-p.2‖⁻¹) :=
    ((measurable_fst.sub measurable_snd).norm).inv
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨?_,?_⟩
  · filter_upwards [hs] with z hz using (inverse_translate_local (R:=R) hz).1
  · apply (integrable_const (∫x in Metric.ball (0:Plane) (R+S),‖x‖⁻¹)).mono'
      hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hs] with z hz
    simp only [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (_ : Plane)))]
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => inv_nonneg.mpr (norm_nonneg _)))]
    exact (inverse_translate_local (R:=R) hz).2

lemma logGradientPotential_prod_integrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    Integrable (fun p : Plane×Plane => logGradient (p.1-p.2))
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
  apply (inversePotential_prod_integrable ν hs R).mono'
    (measurable_logGradient.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  exact Eventually.of_forall (fun p => (norm_logGradient _).le)

def aeLogGradient (ν : Measure Plane) (x : Plane) : Plane := ∫z,logGradient (x-z) ∂ν

lemma aeLogGradient_integrableOn (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) : IntegrableOn (aeLogGradient ν) (Metric.ball 0 R) :=
  (logGradientPotential_prod_integrable ν hs R).integral_prod_left

lemma ae_inverse_kernel_integrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) (R : ℝ) :
    ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) R),
      (∀ᵐz ∂ν,x≠z) ∧ Integrable (fun z => ‖x-z‖⁻¹) ν := by
  filter_upwards [ae_restrict_of_ae (ae_source_ne ν),
    (inversePotential_prod_integrable ν hs R).prod_right_ae] with x hx hi
  exact ⟨hx,hi⟩

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma truncated_gradient_dominating {R ρ : ℝ} (hR : 1≤R) (hρ : 0<ρ)
    {x y z : Plane} (hy : ‖y-x‖≤ρ) (hz : x≠z) :
    ‖farGradient R ρ y z‖ ≤ 2*‖x-z‖⁻¹ ∧
      |farWeight R ρ y z/ρ| ≤ (2*R+2)*‖x-z‖⁻¹ := by
  have hd : 0<‖x-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have htri : ‖x-z‖≤‖y-z‖+ρ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x y z
    rw [norm_sub_rev x y] at ht
    linarith
  by_cases hf : 2*R*ρ<‖y-z‖
  · have he : 0<‖y-z‖ := by nlinarith
    have hr : ρ≤‖y-z‖ := by nlinarith
    have hgg : ‖farGradient R ρ y z‖=‖y-z‖⁻¹ := by
      rw [farGradient,ite_eq_left hf]
      exact norm_logGradient _
    have hff : farWeight R ρ y z/ρ=ρ/‖y-z‖^2 := by
      rw [farWeight,ite_eq_left hf]
      field_simp
    rw [hgg,hff,abs_of_nonneg (div_nonneg hρ.le (sq_nonneg _))]
    have hg : ‖y-z‖⁻¹≤2*‖x-z‖⁻¹ := by
      have hh : (1:ℝ)/‖y-z‖≤2/‖x-z‖ := (div_le_div_iff₀ he hd).mpr (by nlinarith)
      simpa only [one_div,div_eq_mul_inv,one_mul] using hh
    refine ⟨hg,?_⟩
    have hw : ρ/‖y-z‖^2≤‖y-z‖⁻¹ := by
      rw [div_le_iff₀ (sq_pos_of_pos he)]
      have heq : ‖y-z‖⁻¹*‖y-z‖^2=‖y-z‖ := by field_simp
      rw [heq]
      exact hr
    calc
      _ ≤ 2*‖x-z‖⁻¹ := hw.trans hg
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hle := le_of_not_gt hf
    rw [farGradient,ite_eq_right hf,farWeight,ite_eq_right hf,norm_zero,one_div,
      abs_of_pos (inv_pos.mpr hρ)]
    refine ⟨by positivity,?_⟩
    have hh : (1:ℝ)/ρ≤(2*R+2)/‖x-z‖ := (div_le_div_iff₀ hρ hd).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh

lemma tendsto_truncated_kernels {R : ℝ} {ρ : ℕ → ℝ} {y : ℕ → Plane} {x : Plane}
    (_hρ : ∀n,0<ρ n) (hρlim : Tendsto ρ atTop (𝓝 0))
    (hy : ∀n,‖y n-x‖≤ρ n) {z : Plane} (hz : x≠z) :
    Tendsto (fun n => farGradient R (ρ n) (y n) z) atTop (𝓝 (logGradient (x-z))) ∧
    Tendsto (fun n => farWeight R (ρ n) (y n) z/ρ n) atTop (𝓝 0) := by
  have hylim : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n =>norm_nonneg _) hy hρlim
  have hd : ‖x-z‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  have hδlim : Tendsto (fun n => ‖y n-z‖) atTop (𝓝 ‖x-z‖) := (hylim.sub_const z).norm
  have hcut : Tendsto (fun n =>2*R*ρ n) atTop (𝓝 0) := by simpa using hρlim.const_mul (2*R)
  have hevent : ∀ᶠn in atTop,2*R*ρ n<‖y n-z‖ :=
    hcut.eventually_lt hδlim (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
  refine ⟨?_,?_⟩
  · have ht := ((hδlim.pow 2).inv₀ (pow_ne_zero _ hd)).smul (hylim.sub_const z)
    apply ht.congr'
    filter_upwards [hevent] with n hn
    simp only [farGradient,ite_eq_left hn]
  · have ht : Tendsto (fun n =>ρ n/‖y n-z‖^2) atTop (𝓝 0) := by
      simpa only [Pi.div_def,zero_div] using hρlim.div (hδlim.pow 2) (pow_ne_zero _ hd)
    apply ht.congr'
    filter_upwards [hevent] with n hn
    rw [farWeight,ite_eq_left hn]
    field_simp

theorem truncated_potential_limits (ν : Measure Plane) {R : ℝ} (hR : 1≤R)
    {ρ : ℕ → ℝ} {y : ℕ → Plane} {x : Plane}
    (hρ : ∀n,0<ρ n) (hρlim : Tendsto ρ atTop (𝓝 0))
    (hy : ∀n,‖y n-x‖≤ρ n) (hsep : ∀ᵐz ∂ν,x≠z)
    (hi : Integrable (fun z => ‖x-z‖⁻¹) ν) :
    Tendsto (fun n => ∫z,farGradient R (ρ n) (y n) z ∂ν) atTop (𝓝 (aeLogGradient ν x)) ∧
    Tendsto (fun n => (∫z,farWeight R (ρ n) (y n) z ∂ν)/ρ n) atTop (𝓝 0) := by
  refine ⟨?_,?_⟩
  · apply tendsto_integral_of_dominated_convergence (fun z =>2*‖x-z‖⁻¹)
      (fun n =>(measurable_farGradient R (ρ n) (y n)).aestronglyMeasurable) (hi.const_mul 2)
    · intro n
      filter_upwards [hsep] with z hz using (truncated_gradient_dominating hR (hρ n) (hy n) hz).1
    · filter_upwards [hsep] with z hz using (tendsto_truncated_kernels hρ hρlim hy hz).1
  · have ht := tendsto_integral_of_dominated_convergence (μ:=ν) (f:=fun _ : Plane =>(0:ℝ))
      (fun z =>(2*R+2)*‖x-z‖⁻¹)
      (fun n =>((measurable_farWeight R (ρ n) (y n)).div_const (ρ n)).aestronglyMeasurable)
      (hi.const_mul (2*R+2)) (fun n =>?_) ?_
    · simpa only [integral_div,integral_zero] using ht
    · filter_upwards [hsep] with z hz using (by simpa only [Real.norm_eq_abs] using
        (truncated_gradient_dominating hR (hρ n) (hy n) hz).2)
    · filter_upwards [hsep] with z hz using (tendsto_truncated_kernels hρ hρlim hy hz).2

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma partial_regularizedLog_bound {ε : ℝ} (hε : 0<ε) (i : Fin 2) (x : Plane) :
    ‖coordPartial (regularizedLog ε) i x‖ ≤ ‖x‖⁻¹ := by
  by_cases hx : x=0
  · simp [hx,partial_regularizedLog hε]
  have hn : 0<‖x‖ := norm_pos_iff.mpr hx
  rw [partial_regularizedLog hε,norm_div,Real.norm_of_nonneg (logDenom_pos hε x).le]
  apply (div_le_iff₀ (logDenom_pos hε x)).mpr
  calc
    ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
    _ = ‖x‖⁻¹*‖x‖^2 := by field_simp
    _ ≤ ‖x‖⁻¹*logDenom ε x := mul_le_mul_of_nonneg_left (by dsimp [logDenom]; nlinarith [sq_nonneg ε]) (by positivity)

lemma partial_regularizedLog_tendsto (i : Fin 2) {x : Plane} (hx : x≠0) :
    Tendsto (fun ε : ℝ => coordPartial (regularizedLog ε) i x) (𝓝[>]0)
      (𝓝 (logGradient x i)) := by
  have hn : ‖x‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have ht : Tendsto (fun ε : ℝ => x i/(‖x‖^2+ε^2)) (𝓝[>]0) (𝓝 (x i/‖x‖^2)) := by
    apply Tendsto.div tendsto_const_nhds _ hn
    simpa using ((tendsto_const_nhds (x:=‖x‖^2)).add ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).pow 2)).mono_left nhdsWithin_le_nhds
  have he : x i/‖x‖^2=logGradient x i := by simp [logGradient,div_eq_mul_inv,mul_comm]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (partial_regularizedLog hε i x).symm

lemma partial_regularizedLog_test_limit (i : Fin 2) {g : Plane → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun ε : ℝ => ∫x,coordPartial (regularizedLog ε) i x*g x) (𝓝[>]0)
      (𝓝 (∫x,logGradient x i*g x)) := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  let B := fun x : Plane => ‖x‖⁻¹*M
  have hiB : IntegrableOn B (Metric.ball 0 R) := (inv_norm_integrableOn_ball R).mul_const M
  have hne : ∀ᵐx : Plane,x≠0 := by simp [ae_iff]
  have ht := tendsto_integral_filter_of_dominated_convergence (l:=𝓝[>] (0:ℝ)) B
    (F:=fun ε x =>coordPartial (regularizedLog ε) i x*g x)
    (f:=fun x =>logGradient x i*g x)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using
      ((smooth_partial (smooth_regularizedLog hε) i).continuous.mul hg).aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [] with x
      rw [norm_mul]
      exact mul_le_mul (partial_regularizedLog_bound hε i x) (hM (mem_range_self x))
        (norm_nonneg _) (by positivity)) hiB
    (by filter_upwards [ae_restrict_of_ae hne] with x hx using
      (partial_regularizedLog_tendsto i hx).mul_const (g x))
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  simpa only [he] using ht

lemma logarithmic_gradient_distribution {ψ : Plane → ℝ} (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 2) :
    (∫x,Real.log ‖x‖*coordPartial ψ i x)= -(∫x,logGradient x i*ψ x) := by
  have hl := regularizedLog_test_limit (smooth_partial hψ i).continuous (compact_partial hcψ i)
  have hr := (partial_regularizedLog_test_limit i hψ.continuous hcψ).neg
  have he : (fun ε : ℝ => ∫x,regularizedLog ε x*coordPartial ψ i x)=ᶠ[𝓝[>]0]
      (fun ε => -(∫x,coordPartial (regularizedLog ε) i x*ψ x)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_mul_partial (smooth_regularizedLog hε) hψ hcψ i
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma logarithmic_gradient_distribution_translate {ψ : Plane → ℝ} (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 2) (z : Plane) :
    (∫x,Real.log ‖x-z‖*coordPartial ψ i x)= -(∫x,logGradient (x-z) i*ψ x) := by
  rw [← integral_add_right_eq_self (fun x => Real.log ‖x-z‖*coordPartial ψ i x) z,
    ← integral_add_right_eq_self (fun x => logGradient (x-z) i*ψ x) z]
  simp only [add_sub_cancel_right]
  have hs : Smooth (fun x => ψ (x+z)) := hψ.comp (contDiff_id.add contDiff_const)
  have hc : HasCompactSupport (fun x => ψ (x+z)) := hcψ.comp_homeomorph (Homeomorph.addRight z)
  simpa only [partial_translate hψ] using logarithmic_gradient_distribution hs hc i

lemma aeLogGradient_component_test_swap (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {g : Plane → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (i : Fin 2) :
    (∫x,aeLogGradient ν x i*g x) = ∫z,(∫x,logGradient (x-z) i*g x) ∂ν := by
  obtain ⟨R,hR,hzero⟩ := hc.exists_pos_le_norm
  obtain ⟨M,hM⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have he (f : Plane → ℝ) : (∫x in Metric.ball (0:Plane) R,f x*g x)=(∫x,f x*g x) := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x∈Metric.ball (0:Plane) R
    · simp [hx]
    · have hz : g x=0 := hzero x (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hx)
      simp [hx,hz]
  have hp := logGradientPotential_prod_integrable ν hs R
  have hi : Integrable (fun p : Plane×Plane => logGradient (p.1-p.2) i)
      ((volume.restrict (Metric.ball 0 R)).prod ν) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).integrable_comp hp
  have hint : Integrable (fun p : Plane×Plane => logGradient (p.1-p.2) i*g p.1)
      ((volume.restrict (Metric.ball 0 R)).prod ν) := by
    apply (hi.norm.mul_const M).mono'
      (hi.aestronglyMeasurable.mul (hg.measurable.comp measurable_fst).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖logGradient (p.1-p.2) i*g p.1‖≤‖logGradient (p.1-p.2) i‖*M
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM (mem_range_self p.1)) (norm_nonneg _)
  rw [← he (fun x =>aeLogGradient ν x i)]
  calc
    _ = ∫x in Metric.ball (0:Plane) R,∫z,logGradient (x-z) i*g x ∂ν := by
      apply integral_congr_ae
      filter_upwards [hp.prod_right_ae] with x hx
      rw [integral_mul_const]
      have hc := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).integral_comp_comm hx
      exact congrArg (fun t : ℝ => t*g x) hc.symm
    _ = ∫z,(∫x in Metric.ball (0:Plane) R,logGradient (x-z) i*g x) ∂ν := integral_integral_swap hint
    _ = _ := by simp only [he]

lemma aeLogPotential_gradient_distribution (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {ψ : Plane → ℝ} (hψ : Smooth ψ) (hcψ : HasCompactSupport ψ)
    (i : Fin 2) :
    (∫x,aeLogPotential ν x*coordPartial ψ i x)= -(∫x,aeLogGradient ν x i*ψ x) := by
  rw [aeLogPotential_test_swap ν hs (smooth_partial hψ i).continuous (compact_partial hcψ i),
    aeLogGradient_component_test_swap ν hs hψ.continuous hcψ i]
  simp only [logarithmic_gradient_distribution_translate hψ hcψ,integral_neg]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

def WeakGradientZeroOn (w : Plane → ℝ) (Ω : Set Plane) : Prop :=
  ∀(ψ : Plane → ℝ), Smooth ψ → HasCompactSupport ψ → tsupport ψ⊆Ω →
    ∀i : Fin 2,(∫x,w x*coordPartial ψ i x)=0

lemma weakGradient_rconv_partial {w : Plane → ℝ} (hw : Integrable w) {R : ℝ}
    (hzero : WeakGradientZeroOn w (Metric.ball (0:Plane) R))
    (φ : ContDiffBump (0:Plane)) {z : Plane} (hz : ‖z‖+φ.rOut<R) (i : Fin 2) :
    coordPartial (rconv w (φ.normed volume)) i z=0 := by
  have hφ : Smooth (φ.normed volume) := φ.contDiff_normed
  have hcφ := φ.hasCompactSupport_normed (μ:=volume)
  let ψ : Plane → ℝ := fun x =>φ.normed volume (z-x)
  have hψ : Smooth ψ := hφ.comp (contDiff_const.sub contDiff_id)
  have hcψ : HasCompactSupport ψ := hcφ.comp_homeomorph (Homeomorph.subLeft z)
  have hsψ : tsupport ψ⊆Metric.ball (0:Plane) R := by
    apply closure_minimal _ Metric.isClosed_closedBall |>.trans
      (Metric.closedBall_subset_ball (show ‖z‖+φ.rOut<R from hz))
    intro x hx
    have hx' : z-x∈Function.support (φ.normed volume) := hx
    rw [φ.support_normed_eq] at hx'
    have hd : ‖z-x‖<φ.rOut := by simpa only [Metric.mem_ball,dist_zero_right] using hx'
    have hn := norm_sub_norm_le z x
    simp only [Metric.mem_closedBall,dist_zero_right]
    have ht := norm_sub_le z (z-x)
    simp only [sub_sub_cancel] at ht
    linarith
  have hh := hzero ψ hψ hcψ hsψ i
  have hp : coordPartial ψ i=(fun x => -coordPartial (φ.normed volume) i (z-x)) :=
    funext (fun x =>partial_reflection hφ z x i)
  rw [hp] at hh
  simp only [mul_neg,integral_neg,neg_eq_zero] at hh
  rw [partial_rconv hw hφ hcφ,rconv_eq]
  exact hh

lemma weakGradient_rconv_constant {w : Plane → ℝ} (hw : Integrable w) {R r : ℝ}
    (hzero : WeakGradientZeroOn w (Metric.ball (0:Plane) R))
    (φ : ContDiffBump (0:Plane)) (hr : r+φ.rOut≤R)
    {x y : Plane} (hx : x∈Metric.ball (0:Plane) r) (hy : y∈Metric.ball (0:Plane) r) :
    rconv w (φ.normed volume) x=rconv w (φ.normed volume) y := by
  have hs := smooth_rconv hw (φ.contDiff_normed (μ:=volume)) φ.hasCompactSupport_normed
  apply Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0:Plane) r).isPreconnected
    (hs.differentiable (by simp)).differentiableOn _ hx hy
  intro z hz
  apply norm_le_zero_iff.mp
  have hz' : ‖z‖<r := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have hh := fderiv_norm_le_two (f:=rconv w (φ.normed volume)) (C:=0) le_rfl z
    (fun i =>by rw [weakGradient_rconv_partial hw hzero φ (by linarith) i,abs_zero])
  simpa only [mul_zero] using hh

def gradientBump (n : ℕ) : ContDiffBump (0:Plane) :=
  ⟨1/(2*((n:ℝ)+1)),1/((n:ℝ)+1),by positivity,by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]⟩

lemma gradientBump_tendsto : Tendsto (fun n => (gradientBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma rconv_normed_eq (w : Plane → ℝ) (φ : ContDiffBump (0:Plane)) (x : Plane) :
    rconv w (φ.normed volume) x=
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] w) x := by
  rw [rconv_swap,convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul,mul_comm]

lemma ae_gradientBump_converges {w : Plane → ℝ} (hw : Integrable w) :
    ∀ᵐx : Plane,Tendsto (fun n => rconv w ((gradientBump n).normed volume) x) atTop (𝓝 (w x)) := by
  have hratio : ∀ᶠn : ℕ in atTop,(gradientBump n).rOut≤2*(gradientBump n).rIn := by
    filter_upwards [] with n
    change 1/((n:ℝ)+1)≤2*(1/(2*((n:ℝ)+1)))
    have hn : (n:ℝ)+1≠0 := by positivity
    field_simp
    norm_num
  have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ:=volume) gradientBump_tendsto hratio hw.locallyIntegrable
  simpa only [rconv_normed_eq] using hh

theorem weakGradient_constant_ae {w : Plane → ℝ} (hw : Integrable w) {R : ℝ} (hR : 0<R)
    (hzero : WeakGradientZeroOn w (Metric.ball (0:Plane) R)) :
    ∃c : ℝ,∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) R),w x=c := by
  have hlim := ae_gradientBump_converges hw
  obtain ⟨a,ha,halim⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (μ:=volume) (s:=Metric.ball (0:Plane) R)
    (Metric.measure_ball_pos volume (0:Plane) hR).ne' (ae_restrict_of_ae hlim)
  refine ⟨w a,?_⟩
  filter_upwards [ae_restrict_of_ae hlim,self_mem_ae_restrict measurableSet_ball] with x hxlim hx
  have haR : ‖a‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using ha
  have hxR : ‖x‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  obtain ⟨r,hlo,hhi⟩ := exists_between (max_lt haR hxR)
  have he : (fun n =>rconv w ((gradientBump n).normed volume) x)=ᶠ[atTop]
      (fun n =>rconv w ((gradientBump n).normed volume) a) := by
    filter_upwards [gradientBump_tendsto.eventually (eventually_lt_nhds (sub_pos.mpr hhi))] with n hn
    exact weakGradient_rconv_constant (r:=r) hw hzero (gradientBump n) (by linarith)
      (by simpa only [Metric.mem_ball,dist_zero_right] using (le_max_right ‖a‖ ‖x‖).trans_lt hlo)
      (by simpa only [Metric.mem_ball,dist_zero_right] using (le_max_left ‖a‖ ‖x‖).trans_lt hlo)
  exact tendsto_nhds_unique hxlim (halim.congr' he.symm)

end SharpNodal.Profiles

noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma aeLogPotential_locallyIntegrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) : LocallyIntegrable (aeLogPotential ν) volume := by
  intro x
  exact ⟨Metric.ball (0:Plane) (‖x‖+1),Metric.isOpen_ball.mem_nhds (by
    simp only [Metric.mem_ball,dist_zero_right]; linarith),aeLogPotential_integrableOn ν hs _⟩

lemma aeLogGradient_locallyIntegrable (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) : LocallyIntegrable (aeLogGradient ν) volume := by
  intro x
  exact ⟨Metric.ball (0:Plane) (‖x‖+1),Metric.isOpen_ball.mem_nhds (by
    simp only [Metric.mem_ball,dist_zero_right]; linarith),aeLogGradient_integrableOn ν hs _⟩

lemma potential_sum_gradient_distribution (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {h ψ : Plane → ℝ} (hh : Smooth h) (hψ : Smooth ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin 2) :
    (∫x,(h x+aeLogPotential ν x)*coordPartial ψ i x)=
      -(∫x,(coordPartial h i x+aeLogGradient ν x i)*ψ x) := by
  have hip := integrable_aeLogPotential_mul_compact ν hs (smooth_partial hψ i).continuous (compact_partial hcψ i)
  have hg : LocallyIntegrable (fun x =>aeLogGradient ν x i) volume := by
    intro x
    obtain ⟨u,hu,hi⟩ := aeLogGradient_locallyIntegrable ν hs x
    exact ⟨u,hu,(EuclideanSpace.proj i : Plane →L[ℝ] ℝ).integrable_comp hi⟩
  have hig : Integrable (fun x =>aeLogGradient ν x i*ψ x) := by
    exact hg.integrable_smul_right_of_hasCompactSupport hψ.continuous hcψ
  simp_rw [add_mul]
  rw [integral_add (integrable_mul_compact_right hh (smooth_partial hψ i) (compact_partial hcψ i)) hip,
    integral_add (integrable_mul_compact_right (smooth_partial hh i) hψ hcψ) hig,
    integral_mul_partial hh hψ hcψ i,aeLogPotential_gradient_distribution ν hs hψ hcψ i]
  ring

lemma potential_zeroGradient_weak (ν : Measure Plane) [IsFiniteMeasure ν] {S : ℝ}
    (hs : ∀ᵐz ∂ν,‖z‖<S) {h : Plane → ℝ} (hh : Smooth h)
    (he : ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 2),
      fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)=0) :
    WeakGradientZeroOn ((Metric.ball (0:Plane) 3).indicator (fun x =>h x+aeLogPotential ν x))
      (Metric.ball (0:Plane) 2) := by
  intro ψ hψ hcψ hsψ i
  have hsP : tsupport (coordPartial ψ i)⊆Metric.ball (0:Plane) 2 := (partial_tsupport_subset _ _).trans hsψ
  have hcut : (fun x =>((Metric.ball (0:Plane) 3).indicator (fun x =>h x+aeLogPotential ν x) x)*coordPartial ψ i x)=
      (fun x =>(h x+aeLogPotential ν x)*coordPartial ψ i x) := by
    funext x
    by_cases hx : x∈Metric.ball (0:Plane) 3
    · rw [indicator_of_mem hx]
    · have hz : coordPartial ψ i x=0 := image_eq_zero_of_notMem_tsupport (fun ht =>
        hx (Metric.ball_subset_ball (by norm_num : (2:ℝ)≤3) (hsP ht)))
      simp only [hz,mul_zero]
  rw [hcut,potential_sum_gradient_distribution ν hs hh hψ hcψ i,neg_eq_zero]
  apply integral_eq_zero_of_ae
  have hea := (ae_restrict_iff' measurableSet_ball).mp he
  filter_upwards [hea] with x hx
  by_cases hm : x∈Metric.ball (0:Plane) 2
  · have hi := congrArg (fun L : Plane →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) (hx hm)
    have hi' : coordPartial h i x+aeLogGradient ν x i=0 := by
      simpa only [add_apply,zero_apply,innerSL_apply_apply,
        EuclideanSpace.inner_single_right,coordPartial,starRingEnd_apply,star_trivial,one_mul] using hi
    simp only [hi',zero_mul,Pi.zero_apply]
  · simp only [image_eq_zero_of_notMem_tsupport (fun ht =>hm (hsψ ht)),mul_zero,Pi.zero_apply]

lemma profile_eq_constant_of_ae {Ω U : Set Plane} {V : Plane → EReal}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Ω,V x≤0) (htest : FullTestProperty Ω V)
    (hU : IsOpen U) (hUΩ : U⊆Ω) {c : ℝ}
    (he : ∀ᵐx ∂volume.restrict U,V x=(c:EReal)) : ∀x∈U,V x=(c:EReal) := by
  have hupper := profile_le_continuous_of_ae (hV.upperSemicontinuousOn _) hneg htest hU hUΩ
    (g:=fun _ =>c) continuous_const (he.mono (fun _ hx =>hx.le))
  have hle : ∀ᵐx ∂volume.restrict U,(c:EReal)≤V x := he.mono (fun _ hx =>hx.ge)
  have hnull : volume (U∩V ⁻¹' Iio (c:EReal))=0 := by
    have hh := ae_imp_of_ae_restrict hle
    simpa only [ae_iff,Classical.not_imp,not_le,Set.inter_def,Set.preimage,Set.mem_Iio,Set.mem_ofPred_eq] using hh
  have hempty := (hU.inter (hV.isOpen_preimage (c:EReal))).eq_empty_of_measure_zero hnull
  intro x hx
  refine le_antisymm (hupper x hx) ?_
  by_contra hn
  have hm : x∈U∩V ⁻¹' Iio (c:EReal) := ⟨hx,lt_of_not_ge hn⟩
  rw [hempty] at hm
  exact hm

theorem profile_nonzero_gradient (ν : Measure Plane) [IsFiniteMeasure ν]
    (hs : ∀ᵐz ∂ν,‖z‖<4) {V : Plane → EReal} {h : Plane → ℝ}
    (hV : UpperSemicontinuous V) (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a)
    (hh : Smooth h) (hrep : ∀ᵐx : Plane,x∈Metric.ball (0:Plane) 3 → (V x).toReal=h x+aeLogPotential ν x)
    (hnonconstant : ∃x∈Metric.ball (0:Plane) 2,∃y∈Metric.ball (0:Plane) 2,V x≠V y) :
    ∃x∈Metric.ball (0:Plane) 2,(∀ᵐz ∂ν,x≠z) ∧ Integrable (fun z =>‖x-z‖⁻¹) ν ∧
      fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)≠0 := by
  by_contra hno
  have hzero : ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 2),fderiv ℝ h x+innerSL ℝ (aeLogGradient ν x)=0 := by
    filter_upwards [ae_inverse_kernel_integrable ν hs 2,self_mem_ae_restrict measurableSet_ball] with x hx hm
    by_contra hn
    exact hno ⟨x,hm,hx.1,hx.2,hn⟩
  let w := (Metric.ball (0:Plane) 3).indicator (fun x =>h x+aeLogPotential ν x)
  have hw : Integrable w := by
    apply IntegrableOn.integrable_indicator _ measurableSet_ball
    exact (hh.continuous.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall (0:Plane) 3)).mono_set Metric.ball_subset_closedBall
      |>.add (aeLogPotential_integrableOn ν hs 3)
  obtain ⟨c,hc⟩ := weakGradient_constant_ae hw (by norm_num : (0:ℝ)<2) (potential_zeroGradient_weak ν hs hh hzero)
  have hcast : ∀ᵐx ∂volume.restrict (Metric.ball (0:Plane) 2),V x=(c:EReal) := by
    filter_upwards [hc,ae_restrict_of_ae hrep,
      ae_restrict_of_ae (profile_finite_ae_D3 (hV.upperSemicontinuousOn _) hneg htest hanchor),
      self_mem_ae_restrict measurableSet_ball] with x hcx hrep hf hm
    have h3 := Metric.ball_subset_ball (by norm_num : (2:ℝ)≤3) hm
    rw [← EReal.coe_toReal (hf h3).2 (hf h3).1,hrep h3]
    have hwx : w x=h x+aeLogPotential ν x := indicator_of_mem h3 _
    rw [← hwx,hcx]
  have hall := profile_eq_constant_of_ae hV hneg htest Metric.isOpen_ball
    (Metric.ball_subset_ball (by norm_num : (2:ℝ)≤1000)) hcast
  obtain ⟨x,hx,y,hy,hne⟩ := hnonconstant
  exact hne ((hall x hx).trans (hall y hy).symm)

end SharpNodal.Profiles

end
end
end
end
end
end

end OAI
