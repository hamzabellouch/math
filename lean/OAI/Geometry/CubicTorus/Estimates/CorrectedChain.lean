import Mathlib
import OAI.Geometry.CubicTorus.Estimates.ChainMass

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_chain_stability {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (l : List WallVariation) (b : WallVariation)
    (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
        torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E) ∧
      IsLocalMin (correctedChainArea l b γ μ) 0 ∧
      0≤deriv (deriv (correctedChainArea l b γ μ)) 0 := by
  obtain ⟨γ,hγ,heq⟩ := smooth_quotient_extension
    (contDiff_const.sub (simultaneousMass_smooth l E)) (simultaneousFlux_smooth l b E)
    (by simpa using hB)
  have heq' : γ =ᶠ[𝓝 0] chainCorrection l b E := heq
  have hγ0 : γ 0=0 := heq'.eq_of_nhds.trans (chainCorrection_zero l b hE)
  have hvol : ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
      torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E := by
    filter_upwards [heq',chainCorrection_eventually_exact l b hE hB] with t ht hv
    simpa only [correctedChain,ht] using hv
  have hlocal : IsLocalMin (correctedChainArea l b γ μ) 0 := by
    filter_upwards [hvol] with t ht
    rw [correctedChainArea_zero l b hγ0,hμ.1]
    have hfin := chainRegion_finite ht.1 hE hmin.1.2
    have hleast := hmin.2.2 _ hfin (ht.2.trans hmin.2.1)
    have harea := perimeter_chainRegion_le_normalArea ht.1 hE hμ
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleast.trans harea)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _),correctedChainArea] using hh
  exact ⟨γ,hγ,hγ0,hvol,hlocal,second_derivative_nonneg_of_local_min hlocal
    (correctedChainArea_smoothAt l b hγ hγ0 μ).continuousAt⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def correctedChain (l : List Variation) (b : Variation) (γ : ℝ → ℝ) (t : ℝ) : VariationChain :=
  simultaneousChain l t++[(b,γ t)]

def correctedChainArea (l : List Variation) (b : Variation) (γ : ℝ → ℝ)
    (μ : FiniteMeasure NormalBundle) (t : ℝ) : ℝ :=
  ∫ z,‖chainCofactor (correctedChain l b γ t) z.1 z.2‖ ∂(μ : Measure NormalBundle)

lemma correctedChainCofactor_smooth (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ×(Cover×Cover) ↦ chainCofactor (correctedChain l b γ p.1) p.2.1 p.2.2) := by
  simp only [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
  exact (simultaneousCofactor_smooth l).add ((hγ.comp contDiff_fst).fun_smul
    ((wallVelocity_contDiff b).comp
      (((simultaneousMove_smooth l).comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk
        (simultaneousCofactor_smooth l))))

lemma correctedChainArea_smoothAt (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0)
    (μ : FiniteMeasure NormalBundle) : ContDiffAt ℝ (⊤ : ℕ∞) (correctedChainArea l b γ μ) 0 := by
  apply normalArea_smoothAt (correctedChainCofactor_smooth l b hγ) ?_ μ
  intro p _
  simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]

lemma correctedChainArea_zero (l : List Variation) (b : Variation)
    {γ : ℝ → ℝ} (hγ0 : γ 0=0) (μ : FiniteMeasure NormalBundle) :
    correctedChainArea l b γ μ 0=(μ.mass : ℝ) := by
  unfold correctedChainArea
  simp_rw [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0,
    zero_smul,add_zero,simultaneousCofactor_zero,fun z : NormalBundle ↦ z.2.property]
  simp only [integral_const,smul_eq_mul,mul_one]
  rfl

theorem isMinimizerAt_chain_stability {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (l : List Variation) (b : Variation)
    (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ γ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) γ ∧ γ 0=0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
        torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E) ∧
      IsLocalMin (correctedChainArea l b γ μ) 0 ∧
      0≤deriv (deriv (correctedChainArea l b γ μ)) 0 := by
  obtain ⟨γ,hγ,heq⟩ := smooth_quotient_extension
    (contDiff_const.sub (simultaneousMass_smooth l E)) (simultaneousFlux_smooth l b E)
    (by simpa using hB)
  have heq' : γ =ᶠ[𝓝 0] chainCorrection l b E := heq
  have hγ0 : γ 0=0 := heq'.eq_of_nhds.trans (chainCorrection_zero l b hE)
  have hvol : ∀ᶠ t in 𝓝 (0 : ℝ),ChainValid (correctedChain l b γ t) ∧
      torusVolume (chainRegion (correctedChain l b γ t) E)=torusVolume E := by
    filter_upwards [heq',chainCorrection_eventually_exact l b hE hB] with t ht hv
    simpa only [correctedChain,ht] using hv
  have hlocal : IsLocalMin (correctedChainArea l b γ μ) 0 := by
    filter_upwards [hvol] with t ht
    rw [correctedChainArea_zero l b hγ0,hμ.1]
    have hfin := chainRegion_finite ht.1 hE hmin.1.2
    have hleast := hmin.2.2 _ hfin (ht.2.trans hmin.2.1)
    have harea := perimeter_chainRegion_le_normalArea ht.1 hE hμ
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hleast.trans harea)
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun z ↦ norm_nonneg _),correctedChainArea] using hh
  exact ⟨γ,hγ,hγ0,hvol,hlocal,second_derivative_nonneg_of_local_min hlocal
    (correctedChainArea_smoothAt l b hγ hγ0 μ).continuousAt⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma hasDerivAt_norm_curve {f : ℝ → X} {v : X} {t : ℝ}
    (hf : HasDerivAt f v t) (h0 : f t≠0) :
    HasDerivAt (fun s ↦ ‖f s‖) (⟪f t,v⟫/‖f t‖) t := by
  have hh := hf.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hh
  convert hh using 1; ring

lemma second_derivative_norm_curve {C : ℝ → X} (hC : ContDiff ℝ (⊤ : ℕ∞) C)
    (h0 : ‖C 0‖=1) :
    deriv (deriv (fun t ↦ ‖C t‖)) 0 = ‖deriv C 0‖^2 - ⟪C 0,deriv C 0⟫^2 +
      ⟪C 0,deriv (deriv C) 0⟫ := by
  have hn : C 0≠0 := by intro hz; rw [hz,norm_zero] at h0; norm_num at h0
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ),C t≠0 := hC.continuous.continuousAt.eventually_ne hn
  have hd := (hC.differentiable (by simp) 0).hasDerivAt
  have hd' := ((contDiff_infty_iff_deriv.mp hC).2.differentiable (by simp) 0).hasDerivAt
  have hg := hasDerivAt_norm_curve hd hn
  have heq : deriv (fun t ↦ ‖C t‖) =ᶠ[𝓝 0] (fun t ↦ ⟪C t,deriv C t⟫/‖C t‖) := by
    filter_upwards [hne] with t ht
    exact (hasDerivAt_norm_curve ((hC.differentiable (by simp) t).hasDerivAt) ht).deriv
  rw [heq.deriv_eq]
  have hh := ((hd.inner ℝ hd').fun_div hg (by rw [h0]; norm_num)).deriv
  simp only [h0,div_one,one_pow,mul_one,real_inner_self_eq_norm_sq] at hh
  rw [hh]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicTorus

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E] in
lemma deriv_parameter_slice
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E]
    {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : X) :
    deriv (fun s ↦ F (s,x)) t=fderiv ℝ F (t,x) (1,0) :=
  ((hF.differentiable (by simp) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

lemma second_deriv_parameter_slice {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) (x : X) :
    deriv (deriv (fun s ↦ F (s,x))) t=
      fderiv ℝ (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) (t,x) (1,0) := by
  rw [show deriv (fun s ↦ F (s,x))=(fun s ↦ fderiv ℝ F (s,x) (1,0)) from
    funext fun s ↦ deriv_parameter_slice hF s x]
  exact deriv_parameter_slice ((hF.fderiv_right (by simp)).clm_apply contDiff_const) t x

lemma second_deriv_compact_parameter_integral {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {F : ℝ×X → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (t : ℝ) :
    deriv (deriv (fun s ↦ ∫ x,F (s,x) ∂μ)) t=
      ∫ x,deriv (deriv (fun s ↦ F (s,x))) t ∂μ := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×X ↦ fderiv ℝ F p (1,0)) :=
    (hF.fderiv_right (by simp)).clm_apply contDiff_const
  rw [show deriv (fun s ↦ ∫ x,F (s,x) ∂μ)=(fun s ↦ ∫ x,fderiv ℝ F (s,x) (1,0) ∂μ) from
    funext fun s ↦ (hasDerivAt_compact_parameter_integral hK hμ hF s).deriv,
    (hasDerivAt_compact_parameter_integral hK hμ hd t).deriv]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ (second_deriv_parameter_slice hF t x).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalArea_second_derivative {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle))) 0 =
      ∫ z,‖deriv (fun t ↦ C (t,normalEmbedding z)) 0‖^2 -
        ⟪(z.2 : Cover),deriv (fun t ↦ C (t,normalEmbedding z)) 0⟫^2 +
        ⟪(z.2 : Cover),deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0⟫
        ∂(μ : Measure NormalBundle) := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  let F : ℝ×(Cover×Cover) → ℝ := fun p ↦ smoothNormalLength (C p)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := smoothNormalLength_smooth.comp hC
  have heq : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) =ᶠ[𝓝 0]
      (fun t ↦ ∫ p,F (t,p) ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    filter_upwards [hsmall] with t ht
    rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
    · apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [heq.deriv.deriv_eq,second_deriv_compact_parameter_integral normalCarrier_compact (normalMap_ae_carrier μ) hF]
  have hm : AEStronglyMeasurable (fun p : Cover×Cover ↦ deriv (deriv (fun t ↦ F (t,p))) 0)
      (Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    simp_rw [second_deriv_parameter_slice hF]
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ fderiv ℝ F p (1,0)) :=
      (hF.fderiv_right (by simp)).clm_apply contDiff_const
    have hdd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦
        fderiv ℝ (fun q ↦ fderiv ℝ F q (1,0)) p (1,0)) :=
      (hd.fderiv_right (by simp)).clm_apply contDiff_const
    exact (hdd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have hz : (fun t ↦ F (t,normalEmbedding z)) =ᶠ[𝓝 0] (fun t ↦ ‖C (t,normalEmbedding z)‖) := by
    filter_upwards [hsmall] with t ht
    exact smoothNormalLength_eq (ht _ (normalEmbedding_mem z))
  dsimp only
  rw [hz.deriv.deriv_eq]
  have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
    hC.comp (contDiff_id.prodMk contDiff_const)
  have hc0 := h0 _ (normalEmbedding_mem z)
  rw [second_derivative_norm_curve hcz (by rw [hc0]; exact z.2.property),hc0]
  rfl

end CubicTorus

end
end

section

noncomputable section
open Filter
open scoped Topology
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma deriv_smooth (f : ℝ → X) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv f) := (contDiff_infty_iff_deriv.mp hf).2

lemma deriv_smooth_add {f g : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : deriv (fun t ↦ f t+g t)=fun t ↦ deriv f t+deriv g t := by
  funext t
  exact ((hf.differentiable (by simp) t).hasDerivAt.add
    (hg.differentiable (by simp) t).hasDerivAt).deriv

lemma deriv_smooth_smul {f : ℝ → ℝ} {g : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    deriv (fun t ↦ f t • g t)=fun t ↦ deriv f t • g t+f t • deriv g t := by
  funext t
  simpa only [add_comm] using ((hf.differentiable (by simp) t).hasDerivAt.fun_smul
    (hg.differentiable (by simp) t).hasDerivAt).deriv

lemma second_deriv_zero_smul {f : ℝ → ℝ} {g : ℝ → X}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (h0 : f 0=0) (hd0 : deriv f 0=0) :
    deriv (deriv (fun t ↦ f t • g t)) 0=deriv (deriv f) 0 • g 0 := by
  rw [deriv_smooth_smul hf hg,deriv_smooth_add ((deriv_smooth f hf).fun_smul hg)
    (hf.fun_smul (deriv_smooth g hg)),deriv_smooth_smul (deriv_smooth f hf) hg,
    deriv_smooth_smul hf (deriv_smooth g hg)]
  simp [h0,hd0]

lemma correction_second_derivative {m f γ : ℝ → ℝ}
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (h0 : γ 0=0) (hf0 : f 0≠0)
    (hdm : deriv m 0=0) (hex : (fun t ↦ m t+γ t*f t) =ᶠ[𝓝 0] fun _ ↦ m 0) :
    deriv γ 0=0 ∧ deriv (deriv γ) 0*f 0= -deriv (deriv m) 0 := by
  have hd := hex.deriv_eq
  have hdprod : deriv (fun t ↦ γ t*f t) 0=deriv γ 0*f 0 := by
    simpa [h0] using ((hγ.differentiable (by simp) 0).hasDerivAt.fun_mul
      (hf.differentiable (by simp) 0).hasDerivAt).deriv
  rw [deriv_smooth_add hm (hγ.mul hf)] at hd
  dsimp only at hd
  rw [hdprod,hdm,zero_add,deriv_const] at hd
  have hdγ := (mul_eq_zero.mp hd).resolve_right hf0
  refine ⟨hdγ,?_⟩
  have hdd := hex.deriv.deriv_eq
  rw [deriv_smooth_add hm (hγ.mul hf),deriv_smooth_add (deriv_smooth m hm)
    (deriv_smooth _ (hγ.mul hf)),deriv_const',deriv_const] at hdd
  dsimp only at hdd
  have he := second_deriv_zero_smul hγ hf h0 hdγ
  simp only [smul_eq_mul] at he
  rw [he] at hdd
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalArea_second_zero_correction {C P : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (h0 : ∀ p∈normalCarrier,C (0,p)=p.2) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (hdγ : deriv γ 0=0)
    (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z)‖
      ∂(μ : Measure NormalBundle))) 0 =
      deriv (deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle))) 0+
        deriv (deriv γ) 0*(∫ z,⟪(z.2 : Cover),P (0,normalEmbedding z)⟫ ∂(μ : Measure NormalBundle)) := by
  let D : ℝ×(Cover×Cover) → Cover := fun p ↦ C p+γ p.1 • P p
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := hC.add ((hγ.comp contDiff_fst).fun_smul hP)
  have hD0 : ∀ p∈normalCarrier,D (0,p)=p.2 := by intro p hp; simp [D,hγ0,h0 p hp]
  change deriv (deriv (fun t ↦ ∫ z,‖D (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle))) 0 = _
  rw [normalArea_second_derivative hD hD0,normalArea_second_derivative hC h0]
  have hid (z : NormalBundle) :
      deriv (fun t ↦ D (t,normalEmbedding z)) 0=deriv (fun t ↦ C (t,normalEmbedding z)) 0 := by
    have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
      hC.comp (contDiff_id.prodMk contDiff_const)
    have hpz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ P (t,normalEmbedding z)) :=
      hP.comp (contDiff_id.prodMk contDiff_const)
    change deriv (fun t ↦ C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z)) 0 = _
    rw [deriv_smooth_add hcz (hγ.fun_smul hpz),deriv_smooth_smul hγ hpz]
    simp [hγ0,hdγ]
  have hidd (z : NormalBundle) :
      deriv (deriv (fun t ↦ D (t,normalEmbedding z))) 0=
        deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0+deriv (deriv γ) 0 • P (0,normalEmbedding z) := by
    have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
      hC.comp (contDiff_id.prodMk contDiff_const)
    have hpz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ P (t,normalEmbedding z)) :=
      hP.comp (contDiff_id.prodMk contDiff_const)
    change deriv (deriv (fun t ↦ C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z))) 0 = _
    rw [deriv_smooth_add hcz (hγ.fun_smul hpz),
      deriv_smooth_add (deriv_smooth _ hcz) (deriv_smooth _ (hγ.fun_smul hpz))]
    dsimp only
    rw [second_deriv_zero_smul hγ hpz hγ0 hdγ]
  simp_rw [hid,hidd,inner_add_right,real_inner_smul_right,← add_assoc]
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ fderiv ℝ C p (1,0)) :=
    (hC.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦
      fderiv ℝ (fun q ↦ fderiv ℝ C q (1,0)) p (1,0)) :=
    (hd.fderiv_right (by simp)).clm_apply contDiff_const
  have hv : Continuous (fun z : NormalBundle ↦ deriv (fun t ↦ C (t,normalEmbedding z)) 0) := by
    simp_rw [deriv_parameter_slice hC]
    exact hd.continuous.comp (continuous_const.prodMk normalEmbedding_continuous)
  have hw : Continuous (fun z : NormalBundle ↦ deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0) := by
    simp_rw [second_deriv_parameter_slice hC]
    exact hdd.continuous.comp (continuous_const.prodMk normalEmbedding_continuous)
  have hi : Integrable (fun z : NormalBundle ↦ ‖deriv (fun t ↦ C (t,normalEmbedding z)) 0‖^2-
      ⟪(z.2 : Cover),deriv (fun t ↦ C (t,normalEmbedding z)) 0⟫^2+
      ⟪(z.2 : Cover),deriv (deriv (fun t ↦ C (t,normalEmbedding z))) 0⟫) (μ : Measure NormalBundle) :=
    (((hv.norm.pow 2).sub ((continuous_normalUnit.inner hv).pow 2)).add
      (continuous_normalUnit.inner hw)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hip : Integrable (fun z : NormalBundle ↦ ⟪(z.2 : Cover),P (0,normalEmbedding z)⟫)
      (μ : Measure NormalBundle) :=
    (continuous_normalUnit.inner (hP.continuous.comp (continuous_const.prodMk normalEmbedding_continuous))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add hi (hip.const_mul _),integral_const_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def normalFirstVariation (μ : FiniteMeasure NormalBundle) (a : Variation) : ℝ :=
  ∫ z,⟪(z.2 : Cover),coordinateNormalVelocity a.coordinate a.function z.1 z.2⟫ ∂(μ : Measure NormalBundle)

theorem isMinimizerAt_chain_second_variation {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (b : Variation) (hB : directionalFlux E b.coordinate b.function≠0)
    (hH : normalFirstVariation μ b=H*directionalFlux E b.coordinate b.function)
    (l : List Variation) (hl : deriv (fun t ↦ chainMass (simultaneousChain l t) E) 0=0) :
    0≤deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
      ∂(μ : Measure NormalBundle))) 0-H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 := by
  obtain ⟨γ,hγ,hγ0,hvol,_,hstable⟩ := isMinimizerAt_chain_stability hmin hE hμ l b hB
  have hex : (fun t ↦ chainMass (simultaneousChain l t) E+
      γ t*chainTransportedFlux (simultaneousChain l t) b E) =ᶠ[𝓝 0]
      (fun _ ↦ chainMass (simultaneousChain l 0) E) := by
    filter_upwards [hvol] with t ht
    rw [simultaneousMass_zero l hE,← chainMass_append]
    change chainMass (correctedChain l b γ t) E=torusVolume.real E
    rw [← volume_chainRegion ht.1 hE]
    exact congrArg ENNReal.toReal ht.2
  obtain ⟨hdγ,hddγ⟩ := correction_second_derivative (simultaneousMass_smooth l E)
    (simultaneousFlux_smooth l b E) hγ hγ0 (by simpa using hB) hl hex
  let C : ℝ×(Cover×Cover) → Cover := fun p ↦ chainCofactor (simultaneousChain l p.1) p.2.1 p.2.2
  let P : ℝ×(Cover×Cover) → Cover := fun p ↦ coordinateNormalVelocity b.coordinate b.function
    (chainMove (simultaneousChain l p.1) p.2.1) (C p)
  have hC : ContDiff ℝ (⊤ : ℕ∞) C := simultaneousCofactor_smooth l
  have hP : ContDiff ℝ (⊤ : ℕ∞) P :=
    (wallVelocity_contDiff b).comp
      (((simultaneousMove_smooth l).comp (contDiff_fst.prodMk contDiff_snd.fst)).prodMk hC)
  have he := normalArea_second_zero_correction hC hP (by intro p _; simp [C]) hγ hγ0 hdγ μ
  have hleft : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)+γ t • P (t,normalEmbedding z)‖
      ∂(μ : Measure NormalBundle))=correctedChainArea l b γ μ := by
    funext t
    simp only [correctedChainArea,correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rfl
  rw [hleft] at he
  have hpi : (∫ z,⟪(z.2 : Cover),P (0,normalEmbedding z)⟫ ∂(μ : Measure NormalBundle))=
      normalFirstVariation μ b := by simp [P,C,normalEmbedding,normalFirstVariation]
  rw [hpi,hH] at he
  simp only [simultaneousFlux_zero] at hddγ
  have herr : deriv (deriv γ) 0*(H*directionalFlux E b.coordinate b.function)=
      -H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 := by
    calc _ = H*(deriv (deriv γ) 0*directionalFlux E b.coordinate b.function) := by ring
         _ = _ := by rw [hddγ]; ring
  rw [herr] at he
  rw [he] at hstable
  simpa only [C,normalEmbedding,neg_mul,sub_eq_add_neg] using hstable

theorem isMinimizerAt_exists_stable_weakCMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hE : MeasurableSet E) :
    ∃ (a : Cover) (μ : FiniteMeasure NormalBundle) (H : ℝ),
      IsNormalMeasure ((fun z ↦ z+quotientMap a) ⁻¹' E) μ ∧
      (∀ D : WallVariation,CubicTorus.normalFirstVariation μ D=
        H*directionalFlux ((fun z ↦ z+quotientMap a) ⁻¹' E) D.coordinate D.function) ∧
      ∀ l : List Variation,
        deriv (fun t ↦ chainMass (simultaneousChain l t) ((fun z ↦ z+quotientMap a) ⁻¹' E)) 0=0 →
        0≤deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
          ∂(μ : Measure NormalBundle))) 0-
          H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) ((fun z ↦ z+quotientMap a) ⁻¹' E))) 0 := by
  obtain ⟨a,b,hb⟩ := exists_positive_wallVariation hE
    (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1)
  have hEa : MeasurableSet ((fun z ↦ z+quotientMap a) ⁻¹' E) :=
    hE.preimage (continuous_id.add continuous_const).measurable
  have hmina := isMinimizerAt_translation hmin (quotientMap a)
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hEa hmina.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_exists_coordinate_multiplier hmina hEa hμ b hb.ne'
  exact ⟨a,μ,H,hμ,hH,fun l hl ↦ isMinimizerAt_chain_second_variation hmina hEa hμ
    (Variation.ofWall b) hb.ne' (hH b) l hl⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalArea_first_derivative {C : ℝ×(Cover×Cover) → Cover}
    (hC : ContDiff ℝ (⊤ : ℕ∞) C) (h0 : ∀ p∈normalCarrier,C (0,p)=p.2)
    (μ : FiniteMeasure NormalBundle) :
    deriv (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) 0 =
      ∫ z,⟪(z.2 : Cover),deriv (fun t ↦ C (t,normalEmbedding z)) 0⟫
        ∂(μ : Measure NormalBundle) := by
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ),∀ p∈normalCarrier,1/2≤‖C (t,p)‖ := by
    apply normalCarrier_compact.eventually_forall_of_forall_eventually
    intro p hp
    apply ((hC.continuous.norm).continuousAt.eventually (eventually_gt_nhds ?_)).mono
    · intro q hq; exact hq.le
    · change 1/2<‖C (0,p)‖
      rw [h0 p hp]
      have hn : ‖p.2‖=1 := by simpa [Metric.mem_sphere,dist_zero_right] using hp.2
      rw [hn]
      norm_num
  let F : ℝ×(Cover×Cover) → ℝ := fun p ↦ smoothNormalLength (C p)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := smoothNormalLength_smooth.comp hC
  have heq : (fun t ↦ ∫ z,‖C (t,normalEmbedding z)‖ ∂(μ : Measure NormalBundle)) =ᶠ[𝓝 0]
      (fun t ↦ ∫ p,F (t,p) ∂Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    filter_upwards [hsmall] with t ht
    rw [integral_map normalEmbedding_continuous.measurable.aemeasurable]
    · apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ (smoothNormalLength_eq (ht _ (normalEmbedding_mem z))).symm
    · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [heq.deriv_eq,(hasDerivAt_compact_parameter_integral normalCarrier_compact
    (normalMap_ae_carrier μ) hF 0).deriv]
  have hm : AEStronglyMeasurable (fun p : Cover×Cover ↦ fderiv ℝ F (0,p) (1,0))
      (Measure.map normalEmbedding (μ : Measure NormalBundle)) := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ×(Cover×Cover) ↦ fderiv ℝ F p (1,0)) :=
      (hF.fderiv_right (by simp)).clm_apply contDiff_const
    exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  rw [integral_map normalEmbedding_continuous.measurable.aemeasurable hm]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  have hz : (fun t ↦ F (t,normalEmbedding z)) =ᶠ[𝓝 0] (fun t ↦ ‖C (t,normalEmbedding z)‖) := by
    filter_upwards [hsmall] with t ht
    exact smoothNormalLength_eq (ht _ (normalEmbedding_mem z))
  dsimp only
  rw [← deriv_parameter_slice hF,hz.deriv_eq]
  have hcz : ContDiff ℝ (⊤ : ℕ∞) (fun t ↦ C (t,normalEmbedding z)) :=
    hC.comp (contDiff_id.prodMk contDiff_const)
  have hc0 := h0 _ (normalEmbedding_mem z)
  have hn : C (0,normalEmbedding z)≠0 := by
    rw [hc0]
    exact norm_ne_zero_iff.mp (by rw [show ‖(normalEmbedding z).2‖=1 from z.2.property]; norm_num)
  rw [(hasDerivAt_norm_curve (hcz.differentiable (by simp) 0).hasDerivAt hn).deriv,hc0]
  simp only [normalEmbedding,z.2.property,div_one]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma simultaneousMass_single (a : Variation) {E : Set Torus} (hE : MeasurableSet E) (t : ℝ) :
    chainMass (simultaneousChain [a] t) E=torusVolume.real E+t*directionalFlux E a.coordinate a.function := by
  have h := chainMass_append [] a t E
  simpa only [simultaneousChain,List.map_cons,List.map_nil,List.nil_append,chainMass,chainJacobian,chainTransportedFlux,chainMove,mul_one,one_mul,directionalFlux,
    setIntegral_one_eq_measureReal,← realVolume_lift hE] using h

lemma correctedSingleCofactor_deriv (a b : Variation) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (x n : Cover) :
    deriv (fun t ↦ chainCofactor (correctedChain [a] b γ t) x n) 0=
      coordinateNormalVelocity a.coordinate a.function x n+
        deriv γ 0 • coordinateNormalVelocity b.coordinate b.function x n := by
  let P : ℝ → Cover := fun t ↦ coordinateNormalVelocity b.coordinate b.function
    (coordinateMove a.coordinate a.function t x) (coordinateCofactor a.coordinate a.function t x n)
  have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateMove a.coordinate a.function t x) :=
    contDiff_const.add ((contDiff_id.mul contDiff_const).smul contDiff_const)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateCofactor a.coordinate a.function t x n) := by
    simp only [coordinateCofactor_eq]
    exact contDiff_const.add (contDiff_id.fun_smul contDiff_const)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := (wallVelocity_contDiff b).comp (hm.prodMk hc)
  have he : (fun t ↦ chainCofactor (correctedChain [a] b γ t) x n)=
      (fun t ↦ n+t • coordinateNormalVelocity a.coordinate a.function x n+γ t • P t) := by
    funext t
    simp only [correctedChain,simultaneousChain,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
      chainCofactor,coordinateCofactor_eq,P]
  rw [he]
  have hd := ((hasDerivAt_const (0 : ℝ) n).fun_add
    ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateNormalVelocity a.coordinate a.function x n))).fun_add
      ((hγ.differentiable (by simp) 0).hasDerivAt.fun_smul (hP.differentiable (by simp) 0).hasDerivAt)
  simpa [hγ0,P,coordinateMove,coordinateCofactor_eq] using hd.deriv

lemma correctedSingleArea_deriv (a b : Variation) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ (⊤ : ℕ∞) γ) (hγ0 : γ 0=0) (μ : FiniteMeasure NormalBundle) :
    deriv (correctedChainArea [a] b γ μ) 0=normalFirstVariation μ a+
      deriv γ 0*normalFirstVariation μ b := by
  have h := normalArea_first_derivative (correctedChainCofactor_smooth [a] b hγ)
      (by intro p _; simp [correctedChain,chainCofactor_append,chainCofactor,coordinateCofactor_eq,hγ0]) μ
  change deriv (correctedChainArea [a] b γ μ) 0 = _ at h
  rw [h]
  simp only [normalEmbedding,correctedSingleCofactor_deriv a b hγ hγ0,inner_add_right,real_inner_smul_right]
  rw [integral_add,integral_const_mul]
  · rfl
  · exact (continuous_normalUnit.inner (𝕜 := ℝ)
      (continuous_coordinateNormalVelocity a.coordinate a.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((continuous_normalUnit.inner (𝕜 := ℝ)
      (continuous_coordinateNormalVelocity b.coordinate b.smooth)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

theorem isMinimizerAt_mixed_stationary {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (a b : Variation) (hB : directionalFlux E b.coordinate b.function≠0) :
    normalFirstVariation μ a*directionalFlux E b.coordinate b.function=
      normalFirstVariation μ b*directionalFlux E a.coordinate a.function := by
  obtain ⟨γ,hγ,hγ0,hvol,hlocal,_⟩ := isMinimizerAt_chain_stability hmin hE hμ [a] b hB
  have hex : (fun t ↦ chainMass (simultaneousChain [a] t) E+
      γ t*chainTransportedFlux (simultaneousChain [a] t) b E) =ᶠ[𝓝 0]
      (fun _ ↦ torusVolume.real E) := by
    filter_upwards [hvol] with t ht
    rw [← chainMass_append]
    change chainMass (correctedChain [a] b γ t) E=torusVolume.real E
    rw [← volume_chainRegion ht.1 hE]
    exact congrArg ENNReal.toReal ht.2
  have hd := hex.deriv_eq
  have hm : (fun t ↦ chainMass (simultaneousChain [a] t) E)=
      (fun t ↦ torusVolume.real E+t*directionalFlux E a.coordinate a.function) :=
    funext (simultaneousMass_single a hE)
  have hm' : deriv (fun t ↦ chainMass (simultaneousChain [a] t) E) 0=
      directionalFlux E a.coordinate a.function := by rw [hm]; simp
  rw [deriv_smooth_add (simultaneousMass_smooth [a] E)
    (hγ.mul (simultaneousFlux_smooth [a] b E))] at hd
  dsimp only at hd
  rw [hm',(show deriv (fun t ↦ γ t*chainTransportedFlux (simultaneousChain [a] t) b E) 0=
      deriv γ 0*directionalFlux E b.coordinate b.function from by
        simpa [hγ0] using ((hγ.differentiable (by simp) 0).hasDerivAt.fun_mul
          ((simultaneousFlux_smooth [a] b E).differentiable (by simp) 0).hasDerivAt).deriv),deriv_const] at hd
  have ha := hlocal.deriv_eq_zero
  rw [correctedSingleArea_deriv a b hγ hγ0 μ] at ha
  nlinarith [congrArg (fun z ↦ z*directionalFlux E b.coordinate b.function) ha,
    congrArg (fun z ↦ z*normalFirstVariation μ b) hd]

 theorem isMinimizerAt_exists_coordinate_multiplier {V : ℝ} {E : Set Torus}
    (hmin : IsMinimizerAt V E) (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (b : Variation) (hB : directionalFlux E b.coordinate b.function≠0) :
    ∃ H : ℝ,∀ a : Variation,normalFirstVariation μ a=H*directionalFlux E a.coordinate a.function := by
  refine ⟨normalFirstVariation μ b/directionalFlux E b.coordinate b.function,fun a ↦ ?_⟩
  apply mul_right_cancel₀ hB
  rw [isMinimizerAt_mixed_stationary hmin hE hμ a b hB]
  field_simp

theorem isMinimizerAt_stable_periodic {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ a : Variation,normalFirstVariation μ a=H*directionalFlux E a.coordinate a.function) ∧
      ∀ l : List Variation,deriv (fun t ↦ chainMass (simultaneousChain l t) E) 0=0 →
        0≤deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
          ∂(μ : Measure NormalBundle))) 0-
          H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 := by
  obtain ⟨i,f,hf,hp,hflux⟩ := exists_positive_directionalFlux
    (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1)
  obtain ⟨b,hbi,hbf⟩ := exists_variation_of_function i hf hp
  have hb : directionalFlux E b.coordinate b.function≠0 := by rw [hbi,hbf]; exact hflux.ne'
  obtain ⟨μ,hμ⟩ := exists_normalMeasure hE hmin.1.2.ne
  obtain ⟨H,hH⟩ := isMinimizerAt_exists_coordinate_multiplier hmin hE hμ b hb
  exact ⟨μ,H,hμ,hH,fun l hl ↦ isMinimizerAt_chain_second_variation hmin hE hμ b hb (hH b) l hl⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem tangent_firstVariation_of_coordinate {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Variation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  rw [integral_tangentialDivergence_eq_sum hF, flux_sum_components E hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF
  have hpc : ∀ m x, (fun y ↦ F y i) (x + latticeVector m) = F x i := by
    intro m x; change (F (x + latticeVector m)) i = (F x) i; rw [hp]
  obtain ⟨D, hi, hf⟩ := exists_variation_of_function i hc hpc
  simpa only [normalFirstVariation, hi, hf] using hH D

theorem weakCMC_identity {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Variation, normalFirstVariation μ D =
      H * directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x, F (x + latticeVector m) = F x) :
    (∫ z, tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle)) =
      H * ∫ z, ⟪(z.2 : Cover), F z.1⟫ ∂(μ : Measure NormalBundle) := by
  rw [tangent_firstVariation_of_coordinate hH hF hp]
  obtain ⟨C, hC, hbound⟩ := periodic_bounded hF.continuous hp
  exact congrArg (fun r : ℝ ↦ H*r) (normalMeasure_flux hμ hF hp
    (by linarith : 0<C+1) (fun x ↦ (hbound x).trans (by linarith : C≤C+1))).symm

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma deriv_id_smul_zero {f : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (fun t : ℝ ↦ t • f t) 0=f 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).fun_smul
    (hf.differentiable (by simp) 0).hasDerivAt).deriv

lemma second_deriv_id_smul_zero {f : ℝ → X} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (deriv (fun t : ℝ ↦ t • f t)) 0=2 • deriv f 0 := by
  have hid : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ t) := contDiff_id
  rw [deriv_smooth_smul hid hf]
  simp only [deriv_id'',one_smul]
  rw [deriv_smooth_add hf (hid.fun_smul (deriv_smooth f hf))]
  dsimp only
  rw [deriv_id_smul_zero (deriv_smooth f hf)]
  simp only [two_smul]

lemma deriv_add_time_smul {g f : ℝ → X} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (fun t : ℝ ↦ g t+t • f t) 0=deriv g 0+f 0 := by
  simpa only [id_eq,one_smul,zero_smul,zero_add,add_zero] using
    ((hg.differentiable (by simp) 0).hasDerivAt.fun_add
      ((hasDerivAt_id (0 : ℝ)).fun_smul (hf.differentiable (by simp) 0).hasDerivAt)).deriv

namespace Periodic

def chainVelocity (l : List Variation) (x : Cover) : Cover :=
  (l.map (fun a ↦ a.function x • EuclideanSpace.single a.coordinate (1 : ℝ))).sum

def chainNormalVelocity (l : List Variation) (x n : Cover) : Cover :=
  (l.map (fun a ↦ coordinateNormalVelocity a.coordinate a.function x n)).sum

def chainFlux (l : List Variation) (E : Set Torus) : ℝ :=
  (l.map (fun a ↦ directionalFlux E a.coordinate a.function)).sum

lemma simultaneousMass_append (l : List Variation) (a : Variation) (E : Set Torus) (t : ℝ) :
    chainMass (simultaneousChain (l++[a]) t) E = chainMass (simultaneousChain l t) E+
      t*chainTransportedFlux (simultaneousChain l t) a E := by
  simpa only [simultaneousChain,List.map_append,List.map_cons,List.map_nil] using
    chainMass_append (simultaneousChain l t) a t E

lemma simultaneousMass_deriv (l : List Variation) (E : Set Torus) :
    deriv (fun t ↦ chainMass (simultaneousChain l t) E) 0=chainFlux l E := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainMass,chainJacobian,chainFlux]
  | append_singleton l a ih =>
    simp_rw [simultaneousMass_append l a E]
    rw [show deriv (fun t ↦ chainMass (simultaneousChain l t) E+
        t*chainTransportedFlux (simultaneousChain l t) a E) 0=
        deriv (fun t ↦ chainMass (simultaneousChain l t) E) 0+directionalFlux E a.coordinate a.function from by
      simpa only [smul_eq_mul,simultaneousFlux_zero] using
        deriv_add_time_smul (simultaneousMass_smooth l E) (simultaneousFlux_smooth l a E),ih]
    simp [chainFlux,List.map_append]

lemma simultaneousMove_deriv (l : List Variation) (x : Cover) :
    deriv (fun t ↦ chainMove (simultaneousChain l t) x) 0=chainVelocity l x := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainMove,chainVelocity]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) := (simultaneousMove_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ x)))
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ a.function (chainMove (simultaneousChain l t) x) • EuclideanSpace.single a.coordinate (1 : ℝ)) := (a.smooth.comp hm).fun_smul (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ (EuclideanSpace.single a.coordinate (1 : ℝ) : Cover)))
    have he : (fun t ↦ chainMove (simultaneousChain (l++[a]) t) x)=
        (fun t ↦ chainMove (simultaneousChain l t) x+
          t • (a.function (chainMove (simultaneousChain l t) x) • EuclideanSpace.single a.coordinate (1 : ℝ))) := by
      funext t
      simp [simultaneousChain,List.map_append,chainMove_append,chainMove,coordinateMove,mul_smul]
    rw [he,deriv_add_time_smul hm hf,ih,simultaneousMove_zero]
    simp [chainVelocity,List.map_append]

lemma simultaneousCofactor_deriv (l : List Variation) (x n : Cover) :
    deriv (fun t ↦ chainCofactor (simultaneousChain l t) x n) 0=chainNormalVelocity l x n := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainCofactor,chainNormalVelocity]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) := (simultaneousMove_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ x)))
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainCofactor (simultaneousChain l t) x n) := (simultaneousCofactor_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ (x,n))))
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateNormalVelocity a.coordinate a.function
      (chainMove (simultaneousChain l t) x) (chainCofactor (simultaneousChain l t) x n)) :=
      (wallVelocity_contDiff a).comp (hm.prodMk hc)
    have he : (fun t ↦ chainCofactor (simultaneousChain (l++[a]) t) x n)=
        (fun t ↦ chainCofactor (simultaneousChain l t) x n+
          t • coordinateNormalVelocity a.coordinate a.function (chainMove (simultaneousChain l t) x)
            (chainCofactor (simultaneousChain l t) x n)) := by
      funext t
      simp [simultaneousChain,List.map_append,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rw [he,deriv_add_time_smul hc hf,ih]
    simp [chainNormalVelocity,List.map_append]

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma second_deriv_add_time_smul {g f : ℝ → X} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    deriv (deriv (fun t : ℝ ↦ g t+t • f t)) 0=
      deriv (deriv g) 0+2 • deriv f 0 := by
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ t • f t) := contDiff_id.fun_smul hf
  rw [deriv_smooth_add hg ht,
    deriv_smooth_add (deriv_smooth g hg) (deriv_smooth _ ht)]
  dsimp only
  rw [second_deriv_id_smul_zero hf]

namespace Periodic

def normalJet (l : List Variation) (x n : Cover) : Cover×Cover×Cover :=
  l.foldl (fun j a ↦
    (j.1+a.function x • EuclideanSpace.single a.coordinate 1,
      j.2.1+coordinateNormalVelocity a.coordinate a.function x n,
      j.2.2+2 • (fderiv ℝ (fun p : Cover×Cover ↦
        coordinateNormalVelocity a.coordinate a.function p.1 p.2) (x,n) (j.1,j.2.1)))) (0,0,0)

lemma normalJet_append (l : List Variation) (a : Variation) (x n : Cover) :
    normalJet (l++[a]) x n =
      ((normalJet l x n).1+a.function x • EuclideanSpace.single a.coordinate 1,
        (normalJet l x n).2.1+coordinateNormalVelocity a.coordinate a.function x n,
        (normalJet l x n).2.2+2 • (fderiv ℝ (fun p : Cover×Cover ↦
          coordinateNormalVelocity a.coordinate a.function p.1 p.2) (x,n)
            ((normalJet l x n).1,(normalJet l x n).2.1))) := by
  simp only [normalJet,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma normalJet_first (l : List Variation) (x n : Cover) :
    (normalJet l x n).1=chainVelocity l x ∧ (normalJet l x n).2.1=chainNormalVelocity l x n := by
  induction l using List.reverseRecOn with
  | nil => simp [normalJet,chainVelocity,chainNormalVelocity]
  | append_singleton l a ih =>
    simp only [normalJet_append]
    constructor
    · simpa [chainVelocity,List.map_append] using congrArg (fun u ↦ u+a.function x • EuclideanSpace.single a.coordinate (1 : ℝ)) ih.1
    · simpa [chainNormalVelocity,List.map_append] using congrArg (fun u ↦ u+coordinateNormalVelocity a.coordinate a.function x n) ih.2

end Periodic
end CubicTorus
end
end
end

end OAI
