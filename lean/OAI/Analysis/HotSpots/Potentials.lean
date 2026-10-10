import OAI.Analysis.HotSpots.Trace

namespace OAI

section ActualVectorSupport

noncomputable section

section HarmonicRadialRegularityBaseLayer
open Set MeasureTheory Metric Complex Function Filter Real
open scoped Topology ContDiff Laplacian
namespace StrictHotSpots.Weyl

def radialBump (R : ℝ) (z : ℂ) : ℝ := expNegInvGlue (R^2-‖z‖^2)

lemma radialBump_contDiff (R : ℝ) : ContDiff ℝ ∞ (radialBump R) :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma radialBump_zero {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : R ≤ ‖z‖) :
    radialBump R z = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  nlinarith [norm_nonneg z]

lemma radialBump_support {R : ℝ} (hR : 0 ≤ R) :
    tsupport (radialBump R) ⊆ closedBall (0:ℂ) R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  rw [mem_closedBall,dist_zero_right]
  by_contra h
  exact hz (radialBump_zero hR (le_of_not_ge h))

lemma radialBump_compact {R : ℝ} (hR : 0 ≤ R) : HasCompactSupport (radialBump R) :=
  (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport _) (radialBump_support hR)

lemma radialBump_integral_pos {R : ℝ} (hR : 0 < R) : 0 < ∫ z, radialBump R z := by
  apply (integral_pos_iff_support_of_nonneg (fun z => expNegInvGlue.nonneg _)
    ((radialBump_contDiff R).continuous.integrable_of_hasCompactSupport (radialBump_compact hR.le))).mpr
  have hb : ball (0:ℂ) R ⊆ support (radialBump R) := by
    intro z hz
    apply ne_of_gt
    apply expNegInvGlue.pos_of_pos
    have hn : ‖z‖ < R := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith [norm_nonneg z]
  exact (measure_ball_pos volume (0:ℂ) hR).trans_le (measure_mono hb)

lemma radialBump_polar (R r θ : ℝ) : radialBump R (Complex.polarCoord.symm (r,θ)) =
    expNegInvGlue (R^2-r^2) := by simp only [radialBump,Complex.norm_polarCoord_symm,sq_abs]

lemma polar_continuous : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
  have he : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) =
      fun p => (p.1:ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) :=
    funext Complex.polarCoord_symm_apply
  rw [he]
  fun_prop

lemma polar_circle (x : ℂ) (r θ : ℝ) : x-Complex.polarCoord.symm (r,θ) = circleMap x (-r) θ := by
  rw [circleMap,Complex.polarCoord_symm_apply,Complex.exp_mul_I]
  push_cast
  ring

lemma angle_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℂ → F) (x : ℂ) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap x r θ)) = (2*Real.pi) • circleAverage f x r := by
  have hp : Periodic (fun θ => f (circleMap x r θ)) (2*Real.pi) :=
    fun θ => congrArg f (periodic_circleMap x r θ)
  have he := hp.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add] at he
  have he' : (∫ θ in -Real.pi..Real.pi, f (circleMap x r θ)) =
      ∫ θ in 0..2*Real.pi, f (circleMap x r θ) := by
    convert he.symm using 1
    ring_nf
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),he',circleAverage_def]
  rw [smul_smul,mul_inv_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero),one_smul]

lemma polar_bump_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} (hR : 0 < R) {f : ℂ → F} (hf : Continuous f) (x : ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • (radialBump R (Complex.polarCoord.symm p) •
      f (x-Complex.polarCoord.symm p))) (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
  apply IntegrableOn.of_inter_support (measurableSet_Ioi.prod measurableSet_Ioo)
  have hc : Continuous (fun p : ℝ × ℝ => p.1 • (radialBump R (Complex.polarCoord.symm p) •
      f (x-Complex.polarCoord.symm p))) :=
    continuous_fst.smul (((radialBump_contDiff R).continuous.comp polar_continuous).smul
      (hf.comp (continuous_const.sub polar_continuous)))
  apply (hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro p hp
  refine ⟨⟨hp.1.1.le,?_⟩,⟨hp.1.2.1.le,hp.1.2.2.le⟩⟩
  by_contra hh
  have hz : radialBump R (Complex.polarCoord.symm p) = 0 := by
    apply radialBump_zero hR.le
    rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1.1]
    exact (lt_of_not_ge hh).le
  exact hp.2 (by simp only [hz,zero_smul,smul_zero])


theorem radial_average {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {R : ℝ} (hR : 0 < R) {f : ℂ → F} (hf : Continuous f) (x : ℂ)
    (hh : InnerProductSpace.HarmonicOnNhd f (ball x R)) :
    (∫ z, radialBump R z • f (x-z)) = (∫ z, radialBump R z) • f x := by
  rw [← integral_smul_const]
  rw [← Complex.integral_comp_polarCoord_symm, ← Complex.integral_comp_polarCoord_symm]
  change (∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (radialBump R (Complex.polarCoord.symm p) • f (x-Complex.polarCoord.symm p))) =
    ∫ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
    p.1 • (radialBump R (Complex.polarCoord.symm p) • f x)
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using polar_bump_integrable hR hf x),
    setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using polar_bump_integrable hR (f := fun _ => f x) continuous_const (0:ℂ))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp_rw [radialBump_polar,polar_circle,integral_smul]
  by_cases hrR : r < R
  · have hh' : InnerProductSpace.HarmonicOnNhd f (closedBall x |(-r)|) := by
      rw [abs_neg,abs_of_pos hr]
      exact hh.mono (closedBall_subset_ball hrR)
    rw [angle_integral,hh'.circleAverage_eq]
    simp only [integral_const]
    rw [Measure.real,Measure.restrict_apply_univ,volume_Ioo,ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi- -Real.pi)]
    congr 2
    ring_nf
  · have hzero : expNegInvGlue (R^2-r^2) = 0 := by
      apply expNegInvGlue.zero_of_nonpos
      have hr' : R ≤ r := le_of_not_gt hrR
      nlinarith
    simp only [hzero,zero_smul,smul_zero]

end StrictHotSpots.Weyl
end HarmonicRadialRegularityBaseLayer

section ConvolutionShuffleRegularityBaseLayer
open Set MeasureTheory Metric Complex Function Filter ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Weyl
open Helmholtz

lemma convolution_assoc_scalar {u : ℂ → ℂ} {g k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hk : Continuous k) (hck : HasCompactSupport k) :
    (u ⋆[smulFlip] g) ⋆[smulFlip] k = u ⋆[smulFlip] (g ⋆[mul ℝ ℝ] k) := by
  funext x
  apply convolution_assoc smulFlip smulFlip smulFlip (mul ℝ ℝ)
    (fun z a b => by simp only [smulFlip,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply,ContinuousLinearMap.mul_apply',smul_smul]; rw [mul_comm])
    hu.aestronglyMeasurable hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Eventually.of_forall (hcg.convolutionExists_right _ hu hg)
  · exact Eventually.of_forall (hck.norm.convolutionExists_right _ hg.norm.locallyIntegrable hk.norm)
  · exact (hcg.norm.convolution (mul ℝ ℝ) hck.norm).convolutionExists_right _ (fun x => (hu x).norm)
      (hck.norm.continuous_convolution_right _ hg.norm.locallyIntegrable hk.norm) x

lemma convolution_shuffle {u : ℂ → ℂ} {g k : ℂ → ℝ}
    (hu : LocallyIntegrable u volume) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hk : Continuous k) (hck : HasCompactSupport k) :
    (u ⋆[smulFlip] g) ⋆[smulFlip] k = (u ⋆[smulFlip] k) ⋆[smulFlip] g := by
  rw [convolution_assoc_scalar hu hg hcg hk hck,convolution_assoc_scalar hu hk hck hg hcg]
  have hh : (mul ℝ ℝ).flip = mul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply']
    exact mul_comm y x
  rw [← convolution_flip (L := mul ℝ ℝ),hh]

end StrictHotSpots.Weyl
end ConvolutionShuffleRegularityBaseLayer

section WeakWeylRegularityBaseLayer
open Set MeasureTheory Metric Complex Function Filter ContinuousLinearMap
open scoped Topology ContDiff Laplacian Convolution
namespace StrictHotSpots.Weyl
open Helmholtz



theorem local_representative {u : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hu : LocallyIntegrable u volume) (hR : 0 < R) (hpde : WeakEquation (ball a R) 0 u) :
    ∃ f : ℂ → ℂ, ContDiff ℝ ∞ f ∧
      ∀ᵐ x ∂volume, x ∈ ball a (R/4) → f x = u x := by
  let φ := radialBump (R/4)
  let c : ℝ := ∫ z, φ z
  have hc : 0 < c := radialBump_integral_pos (by positivity)
  have hφ : ContDiff ℝ ∞ φ := radialBump_contDiff _
  have hcφ : HasCompactSupport φ := radialBump_compact (by positivity)
  let v := u ⋆[smulFlip] φ
  have hv : ContDiff ℝ ∞ v := hcφ.contDiff_convolution_right _ hu hφ
  refine ⟨fun x => c⁻¹ • v x,?_,?_⟩
  · simpa only [Pi.smul_apply] using! (contDiff_const (c := c⁻¹)).smul hv
  filter_upwards [smoothen_tendsto hu,smoothen_tendsto hv.continuous.locallyIntegrable] with x hx hxv
  intro hxa
  have he : ∀ᶠ n in atTop, smoothen v n x = c • smoothen u n x := by
    filter_upwards [(tendsto_order.1 mollifier_radius_tendsto).2 (R/2) (by positivity)] with n hn
    have hh : InnerProductSpace.HarmonicOnNhd (smoothen u n) (ball x (R/4)) := by
      intro y hy
      have hym : y ∈ ball a (R-(mollifier n).rOut) := by
        rw [mem_ball] at hy hxa ⊢
        have ht := dist_triangle y x a
        linarith
      refine ⟨((smoothen_contDiff hu n).of_le (show (2:ℕ∞ω) ≤ ∞ by decide)).contDiffAt,?_⟩
      filter_upwards [isOpen_ball.mem_nhds hym] with z hz
      simpa only [neg_zero,zero_smul,Pi.zero_apply] using smoothen_PDE hu hpde n hz
    calc
      smoothen v n x = (smoothen u n ⋆[smulFlip] φ) x :=
        (congrFun (convolution_shuffle hu (mollifier n).continuous_normed
          (mollifier n).hasCompactSupport_normed hφ.continuous hcφ) x).symm
      _ = c • smoothen u n x := by
        rw [← convolution_flip]
        exact radial_average (by positivity) (smoothen_contDiff hu n).continuous x hh
  have ht : Tendsto (fun n => smoothen v n x) atTop (𝓝 (c • u x)) :=
    (hx.const_smul c).congr' (he.mono (fun _ h => h.symm))
  have hvx : v x = c • u x := tendsto_nhds_unique hxv ht
  rw [hvx,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]



theorem representative {u : ℂ → ℂ} {Ω : Set ℂ} (ho : IsOpen Ω)
    (hu : LocallyIntegrable u volume) (hpde : WeakEquation Ω 0 u) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume, x ∈ Ω → f x = u x := by
  classical
  have hball (x : Ω) : ∃ R : ℝ, 0 < R ∧ ball (x:ℂ) R ⊆ Ω :=
    Metric.isOpen_iff.mp ho x x.property
  choose R hR hRΩ using hball
  choose f hf hfu using fun x : Ω => local_representative hu (hR x) (hpde.mono (hRΩ x))
  have hsmall (x : Ω) : ball (x:ℂ) (R x/4) ⊆ Ω :=
    (ball_subset_ball (by linarith [hR x])).trans (hRΩ x)
  have heq (x y : Ω) : EqOn (f x) (f y) (ball (x:ℂ) (R x/4) ∩ ball (y:ℂ) (R y/4)) := by
    apply MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) _ (isOpen_ball.inter isOpen_ball)
      (hf x).continuous.continuousOn (hf y).continuous.continuousOn
    apply (ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).mpr
    filter_upwards [hfu x,hfu y] with z hx hy
    intro hz
    exact (hx hz.1).trans (hy hz.2).symm
  let g : ℂ → ℂ := fun x => if hx : x ∈ Ω then f ⟨x,hx⟩ x else 0
  have hgf (x : Ω) {z : ℂ} (hz : z ∈ ball (x:ℂ) (R x/4)) : g z = f x z := by
    have hzΩ := hsmall x hz
    dsimp only [g]
    rw [dite_eq_left hzΩ]
    exact heq ⟨z,hzΩ⟩ x ⟨mem_ball_self (by linarith [hR ⟨z,hzΩ⟩]),hz⟩
  refine ⟨g,?_,?_⟩
  · intro x hx
    let x' : Ω := ⟨x,hx⟩
    have he : g =ᶠ[𝓝 x] f x' := by
      filter_upwards [ball_mem_nhds x (by linarith [hR x'] : 0 < R x'/4)] with z hz
      exact hgf x' hz
    exact ((hf x').contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
  · obtain ⟨T,hT,hcover⟩ := (IsLindelof.of_coe (s := Ω)).elim_nhds_subcover'
      (fun x hx => ball x (R ⟨x,hx⟩/4)) (fun x hx => ball_mem_nhds x (by linarith [hR ⟨x,hx⟩]))
    have ha : ∀ᵐ z ∂volume, ∀ x ∈ T, z ∈ ball (x:ℂ) (R x/4) → f x z = u z :=
      (eventually_countable_ball hT).mpr (fun x _ => hfu x)
    filter_upwards [ha] with z hz
    intro hzΩ
    obtain ⟨x,hx,hzB⟩ := mem_iUnion₂.mp (hcover hzΩ)
    exact (hgf x hzB).trans (hz x hx hzB)

end StrictHotSpots.Weyl
end WeakWeylRegularityBaseLayer




section PlaneDifferentialInteriorSupportLayer

open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge
abbrev e (i : Fin 2) : Plane := planeBasis i
abbrev c (i : Fin 2) (x : Plane) : ℝ := inner ℝ x (e i)

lemma expand (x : Plane) : c 0 x • e 0 + c 1 x • e 1 = x := by
  simpa only [Fin.sum_univ_two, OrthonormalBasis.repr_apply_apply, real_inner_comm] using planeBasis.sum_repr x
lemma basis_inner (i j : Fin 2) : inner ℝ (e i) (e j) = if i=j then 1 else 0 :=
  planeBasis.inner_eq_ite i j
lemma inner_two (x y : Plane) : inner ℝ x y = c 0 x*c 0 y+c 1 x*c 1 y := by
  simpa only [Fin.sum_univ_two,real_inner_comm (e 0) y,real_inner_comm (e 1) y] using
    (planeBasis.sum_inner_mul_inner x y).symm

def rot : Plane →L[ℝ] Plane :=
  (innerSL ℝ (e 0)).smulRight (e 1) - (innerSL ℝ (e 1)).smulRight (e 0)
lemma rot_apply (x : Plane) : rot x = c 0 x • e 1-c 1 x • e 0 := by
  simp only [rot,sub_apply,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,real_inner_comm]
lemma c_rot (x : Plane) : c 0 (rot x) = -c 1 x ∧ c 1 (rot x) = c 0 x := by
  rw [rot_apply]
  simp only [c,inner_sub_left,inner_smul_left,conj_trivial,basis_inner]
  norm_num
lemma rot_rot (x : Plane) : rot (rot x) = -x := by
  rw [rot_apply,(c_rot x).1,(c_rot x).2]
  calc
    _ = -(c 0 x • e 0+c 1 x • e 1) := by module
    _ = -x := by rw [expand]
lemma rot_inner (x y : Plane) : inner ℝ (rot x) (rot y) = inner ℝ x y := by
  rw [inner_two,inner_two,(c_rot x).1,(c_rot x).2,(c_rot y).1,(c_rot y).2]
  ring
lemma rot_skew (x y : Plane) : inner ℝ (rot x) y = -inner ℝ x (rot y) := by
  rw [inner_two,inner_two,(c_rot x).1,(c_rot x).2,(c_rot y).1,(c_rot y).2]
  ring
lemma rot_norm (x : Plane) : ‖rot x‖ = ‖x‖ := by
  have hh := rot_inner x x
  simp only [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (rot x),norm_nonneg x]

abbrev D (i : Fin 2) (φ : Plane → ℝ) := directionalDerivative φ (e i)
lemma D_smooth {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin 2) : ContDiff ℝ ∞ (D i φ) :=
  (hφ.fderiv_right (by simp)).clm_apply contDiff_const
lemma D_compact {φ : Plane → ℝ} (hc : HasCompactSupport φ) (i : Fin 2) : HasCompactSupport (D i φ) :=
  hc.fderiv_apply ℝ (e i)
lemma D_support (φ : Plane → ℝ) (i : Fin 2) : tsupport (D i φ) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ (e i)
lemma gradient_c (φ : Plane → ℝ) (i : Fin 2) (x : Plane) : c i (gradient φ x) = D i φ x :=
  inner_gradient_left
lemma D_D {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (i j : Fin 2) (x : Plane) :
    D i (D j φ) x = D j (D i φ) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ φ)).differentiable (by simp) x
  change fderiv ℝ (fun y => fderiv ℝ φ y (e j)) x (e i) =
    fderiv ℝ (fun y => fderiv ℝ φ y (e i)) x (e j)
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const,Pi.zero_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) _ _

lemma laplace_two {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Plane) :
    Δ φ x = D 0 (D 0 φ) x + D 1 (D 1 φ) x := by
  simpa only [Fin.sum_univ_two] using
    laplacian_eq_sum_directional isOpen_univ hφ.contDiffOn (mem_univ x)

lemma inner_gradient (Z : Plane) (φ : Plane → ℝ) (x : Plane) :
    inner ℝ Z (gradient φ x) = c 0 Z*D 0 φ x+c 1 Z*D 1 φ x := by
  rw [inner_two,gradient_c,gradient_c]
lemma inner_rot_gradient (Z : Plane) (φ : Plane → ℝ) (x : Plane) :
    inner ℝ Z (rot (gradient φ x)) = c 1 Z*D 0 φ x-c 0 Z*D 1 φ x := by
  rw [inner_two,(c_rot _).1,(c_rot _).2,gradient_c,gradient_c]
  ring
end StrictHotSpots.Hodge


end PlaneDifferentialInteriorSupportLayer


section PlaneWeakWeylInteriorSupportLayer


open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology
namespace StrictHotSpots.Weyl

private def coord : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

private def complexExtension (Ω : Set Plane) (u : Plane → ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal (Ω.indicator u (coord z))

private lemma complexExtension_integral (Ω : Set Plane) (hΩ : MeasurableSet Ω)
    (u : Plane → ℝ) (ψ : ℂ → ℝ) :
    (∫ z, ψ z • complexExtension Ω u z) =
      Complex.ofReal (∫ x in Ω, u x * ψ (coord.symm x)) := by
  have he : (fun z => ψ z • complexExtension Ω u z) =
      (fun z => ((Ω.indicator (fun x => u x * ψ (coord.symm x))) (coord z) : ℂ)) := by
    funext z
    by_cases hz : coord z ∈ Ω
    · simp [complexExtension,indicator_of_mem hz,Complex.real_smul,mul_comm]
    · simp [complexExtension,indicator_of_notMem hz]
  rw [he,integral_complex_ofReal,
    coord.measurePreserving.integral_comp coord.toHomeomorph.measurableEmbedding,
    integral_indicator hΩ]

private lemma complexExtension_integrable {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : MeasurableSet Ω) (hu : IntegrableOn u Ω) :
    Integrable (complexExtension Ω u) volume := by
  have hi := (integrable_indicator_iff hΩ).mpr hu
  have hj := coord.measurePreserving.integrable_comp_of_integrable hi
  exact Complex.ofRealCLM.integrable_comp hj

private lemma complexExtension_weak {Ω : Set Plane} {μ : ℝ} {u : Plane → ℝ}
    (hΩ : MeasurableSet Ω) (hp : PlaneWeakEquation Ω μ u) :
    Helmholtz.WeakEquation (coord ⁻¹' Ω) μ (complexExtension Ω u) := by
  intro φ hφ hc hs
  have ht : ContDiff ℝ ∞ (φ ∘ coord.symm) :=
    hφ.comp coord.symm.toContinuousLinearEquiv.contDiff
  have htc : HasCompactSupport (φ ∘ coord.symm) := hc.comp_homeomorph coord.symm.toHomeomorph
  have hts : tsupport (φ ∘ coord.symm) ⊆ Ω := by
    change tsupport (φ ∘ coord.symm.toHomeomorph) ⊆ Ω
    rw [tsupport_comp_eq_preimage φ coord.symm.toHomeomorph]
    intro x hx
    have h : coord (coord.symm x) ∈ Ω := hs hx
    simpa only [coord.apply_symm_apply] using h
  have h := hp _ ht htc hts
  simp only [laplacian_comp_linearIsometryEquiv,Function.comp_apply] at h
  rw [complexExtension_integral Ω hΩ u (Δ φ),complexExtension_integral Ω hΩ u φ,h]
  simp



theorem plane_representative {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hu : IntegrableOn u Ω) (hp : PlaneWeakEquation Ω 0 u) :
    ∃ f : Plane → ℝ, ContDiffOn ℝ ∞ f Ω ∧ ∀ᵐ x ∂volume.restrict Ω, f x = u x := by
  obtain ⟨f,hf,hfu⟩ := representative (ho.preimage coord.continuous)
    (complexExtension_integrable ho.measurableSet hu).locallyIntegrable
    (complexExtension_weak ho.measurableSet hp)
  refine ⟨fun x => (f (coord.symm x)).re,?_,?_⟩
  · exact Complex.reCLM.contDiff.comp_contDiffOn (hf.comp
      coord.symm.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun x hx => by simpa only [mem_preimage,coord.apply_symm_apply] using hx))
  · apply (ae_restrict_iff' ho.measurableSet).mpr
    filter_upwards [coord.symm.measurePreserving.quasiMeasurePreserving.ae hfu] with x hx
    intro hxm
    have he := hx (show coord.symm x ∈ coord ⁻¹' Ω by simpa using hxm)
    simpa only [complexExtension,coord.apply_symm_apply,indicator_of_mem hxm,Complex.ofReal_re] using congrArg Complex.re he

end StrictHotSpots.Weyl

end PlaneWeakWeylInteriorSupportLayer


section PrimitiveAtlasInteriorSupportLayer




open Set Filter Bundle
open scoped Topology
namespace StrictHotSpots.Primitives

structure DiscreteReal where
  val : ℝ

instance : TopologicalSpace DiscreteReal := ⊥
instance : DiscreteTopology DiscreteReal := ⟨rfl⟩

@[ext] lemma DiscreteReal.ext {x y : DiscreteReal} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

structure Atlas (X ι : Type*) [TopologicalSpace X] where
  U : ι → Set X
  isOpen_U : ∀ i, IsOpen (U i)
  idx : X → ι
  mem_U : ∀ x, x ∈ U (idx x)
  potential : ι → X → ℝ
  constant_overlap : ∀ i j x y, x ∈ U i ∩ U j → y ∈ U i ∩ U j →
    potential i x-potential j x = potential i y-potential j y

namespace Atlas
variable {X ι : Type*} [TopologicalSpace X] (A : Atlas X ι)

def core : FiberBundleCore ι X DiscreteReal where
  baseSet := A.U
  isOpen_baseSet := A.isOpen_U
  indexAt := A.idx
  mem_baseSet_at := A.mem_U
  coordChange i j x d := ⟨d.val+A.potential i x-A.potential j x⟩
  coordChange_self := by
    intro i x _ d
    ext
    dsimp
    ring
  continuousOn_coordChange := by
    intro i j
    by_cases hn : (A.U i ∩ A.U j).Nonempty
    · obtain ⟨z,hz⟩ := hn
      have hc : Continuous (fun d : DiscreteReal =>
          (⟨d.val+(A.potential i z-A.potential j z)⟩ : DiscreteReal)) := continuous_of_discreteTopology
      apply (hc.comp continuous_snd).continuousOn.congr
      intro p hp
      ext
      dsimp
      have he := A.constant_overlap i j p.1 z hp.1 hz
      linarith
    · have he : (A.U i ∩ A.U j) ×ˢ (univ : Set DiscreteReal) = ∅ := by
        rw [not_nonempty_iff_eq_empty.mp hn,empty_prod]
      rw [he]
      exact continuousOn_empty _
  coordChange_comp := by
    intro i j k x _ d
    ext
    dsimp
    ring



theorem exists_locally_potential [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) : ∃ g : X → ℝ, ∀ x : X, ∃ c : ℝ,
      ∀ᶠ y in 𝓝 x, g y = A.potential (A.idx x) y+c := by
  let Z := A.core
  have hcov : IsCoveringMap Z.proj := IsFiberBundle.isCoveringMap (fun x =>
    ⟨Z.localTriv (Z.indexAt x),Z.mem_baseSet_at x⟩)
  let e₀ : Z.TotalSpace := ⟨x₀,⟨0⟩⟩
  obtain ⟨F,⟨_,hF⟩,_⟩ := hcov.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ e₀ rfl
  have hproj (x : X) : (F x).1 = x := congrFun hF x
  let g : X → ℝ := fun x => (F x).2.val+A.potential (A.idx (F x).1) (F x).1
  refine ⟨g,fun x => ?_⟩
  let i := A.idx x
  let c : X → DiscreteReal := fun y => (Z.localTriv i (F y)).2
  have hc : ContinuousAt c x := by
    apply ContinuousAt.snd
    have hm : F x ∈ (Z.localTriv i).source := by
      change Z.proj (F x) ∈ Z.baseSet i
      rw [show Z.proj (F x) = x from hproj x]
      exact A.mem_U x
    exact ((Z.localTriv i).continuousAt hm).comp F.continuous.continuousAt
  have he (y : X) : g y = A.potential i y+(c y).val := by
    dsimp only [g,c]
    rw [Z.localTriv_apply]
    change (F y).2.val+A.potential (A.idx (F y).1) (F y).1 =
      A.potential i y+((F y).2.val+A.potential (A.idx (F y).1) (F y).1-A.potential i (F y).1)
    rw [hproj y]
    ring
  have hn : ∀ᶠ y in 𝓝 x, c y = c x := by
    have hh : {c x} ∈ 𝓝 (c x) := by simp
    exact hc hh
  refine ⟨(c x).val,?_⟩
  filter_upwards [hn] with y hy
  rw [he y,hy]

end Atlas
end StrictHotSpots.Primitives

end PrimitiveAtlasInteriorSupportLayer


section SimplyConnectedPoincareInteriorSupportLayer

open Set Filter Metric
open scoped Topology
namespace StrictHotSpots.Primitives



theorem exists_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (ho : IsOpen Ω) (hs : IsSimplyConnected Ω)
    {ω : E → E →L[ℝ] ℝ} (hω : DifferentiableOn ℝ ω Ω)
    (hd : ∀ a ∈ Ω, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x) :
    ∃ f : E → ℝ, ∀ a ∈ Ω, HasFDerivAt f (ω a) a := by
  classical
  let : SimplyConnectedSpace Ω := hs
  let : LocallyPathConnectedSpace Ω := ho.locallyPathConnectedSpace
  have hb (p : Ω) : ∃ r : ℝ, 0 < r ∧ ball (p : E) r ⊆ Ω :=
    Metric.isOpen_iff.mp ho p p.property
  choose r hr hrΩ using hb
  have hprim (p : Ω) : ∃ F : E → ℝ, ∀ a ∈ ball (p : E) (r p), HasFDerivAt F (ω a) a :=
    (convex_ball (p : E) (r p)).exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_ball
      (hω.mono (hrΩ p)) (fun a ha => hd a (hrΩ p ha))
  choose F hF using hprim
  let A : Atlas Ω Ω := {
    U := fun p => Subtype.val ⁻¹' ball (p : E) (r p)
    isOpen_U := fun p => isOpen_ball.preimage continuous_subtype_val
    idx := id
    mem_U := fun p => mem_ball_self (hr p)
    potential := fun p x => F p x
    constant_overlap := by
      intro p q x y hx hy
      let U := ball (p : E) (r p) ∩ ball (q : E) (r q)
      have hu : IsOpen U := isOpen_ball.inter isOpen_ball
      have hh (z : E) (hz : z ∈ U) : HasFDerivAt (fun z => F p z-F q z) (0 : E →L[ℝ] ℝ) z := by
        simpa only [sub_self,Pi.sub_apply] using! (hF p z hz.1).sub (hF q z hz.2)
      apply ((convex_ball (p : E) (r p)).inter (convex_ball (q : E) (r q))).is_const_of_fderivWithin_eq_zero
          (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
          (fun z hz => (hh z hz).hasFDerivWithinAt.fderivWithin (hu.uniqueDiffOn z hz)) hx hy }
  obtain ⟨x₀⟩ := (inferInstance : Nonempty Ω)
  obtain ⟨g,hg⟩ := A.exists_locally_potential x₀
  let f : E → ℝ := fun x => if hx : x ∈ Ω then g ⟨x,hx⟩ else 0
  refine ⟨f,fun a ha => ?_⟩
  let a' : Ω := ⟨a,ha⟩
  obtain ⟨c,hc⟩ := hg a'
  have he : ∀ᶠ x in 𝓝 a, f x = F a' x+c := by
    have hsub : ∀ᶠ x : Ω in 𝓝 a', g x = F a' x+c := hc
    rw [nhds_subtype_eq_comap] at hsub
    obtain ⟨s,hsn,hss⟩ := Filter.mem_comap.mp hsub
    filter_upwards [hsn,ho.mem_nhds ha] with x hx hxΩ
    have hm := hss (show (⟨x,hxΩ⟩ : Ω) ∈ Subtype.val ⁻¹' s from hx)
    change g ⟨x,hxΩ⟩ = F a' x+c at hm
    simpa only [f,dite_eq_left hxΩ] using hm
  exact ((hF a' a (mem_ball_self (hr a'))).add_const c).congr_of_eventuallyEq he

end StrictHotSpots.Primitives

end SimplyConnectedPoincareInteriorSupportLayer


section SmoothTruncationInteriorSupportLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace StrictHotSpots.Truncation

def trunc (n : ℕ) (t : ℝ) : ℝ := ((n:ℝ)+1) * Real.arctan (t/((n:ℝ)+1))
lemma smooth (n : ℕ) : ContDiff ℝ ∞ (trunc n) := by
  exact contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_id.div_const _))
lemma derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (trunc n) (1 / (1 + (t/((n:ℝ)+1))^2)) t := by
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  convert (((hasDerivAt_id t).div_const ((n:ℝ)+1)).arctan.const_mul ((n:ℝ)+1)) using 1 <;> try rfl
  simp only [id_eq]
  field_simp
lemma deriv_bound (n : ℕ) (t : ℝ) : ‖deriv (trunc n) t‖ ≤ 1 := by
  rw [(derivative n t).deriv, Real.norm_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (t/((n:ℝ)+1))])
lemma norm_le (n : ℕ) (t : ℝ) : ‖trunc n t‖ ≤ ‖t‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := trunc n) (s := univ)
    (fun x _ => (derivative n x).differentiableAt)
    (fun x _ => deriv_bound n x) convex_univ (mem_univ t) (mem_univ (0:ℝ))
  simpa [trunc] using h
lemma bounded (n : ℕ) (t : ℝ) : ‖trunc n t‖ ≤ ((n:ℝ)+1)*(Real.pi/2) := by
  rw [trunc,norm_mul,Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨(Real.neg_pi_div_two_lt_arctan _).le,(Real.arctan_lt_pi_div_two _).le⟩
lemma tends (t : ℝ) : Tendsto (fun n => trunc n t) atTop (𝓝 t) := by
  by_cases ht : t = 0
  · subst t
    simp [trunc]
  have ht0 : Tendsto (fun n : ℕ => t/((n:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (by simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1) : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop))
  have htne : Tendsto (fun n : ℕ => t/((n:ℝ)+1)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht0,Eventually.of_forall (fun n => by simpa using div_ne_zero ht (by positivity : (n:ℝ)+1 ≠ 0))⟩
  have hh := ((Real.hasDerivAt_arctan 0).tendsto_slope_zero.comp htne).const_mul t
  convert hh using 1
  · ext n
    simp only [Function.comp_apply,zero_add, Real.arctan_zero,sub_zero,smul_eq_mul,trunc]
    field_simp
  · simp
end StrictHotSpots.Truncation

end SmoothTruncationInteriorSupportLayer


section AnchoredEstimateInteriorSupportLayer

open Set MeasureTheory Filter
namespace StrictHotSpots


lemma anchored_l2_bound {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {B : Set α} (_hB : MeasurableSet B) (hβ : 0 < (μ B).toReal)
    {f : α → ℝ} (hf : MemLp f 2 μ) {m M D : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict B, ‖f x‖ ≤ M)
    (hv : (∫ x, (f x-m)^2 ∂μ) ≤ D) :
    (∫ x, (f x)^2 ∂μ) ≤ 2*D + 2*((2*D + 2*M^2*(μ B).toReal)/(μ B).toReal)*(μ univ).toReal := by
  have hfi : Integrable (fun x => (f x)^2) μ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hfm : MemLp (fun x => f x-m) 2 μ := hf.sub (memLp_const m)
  have hvI : Integrable (fun x => (f x-m)^2) μ := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hfm
  have hvB : (∫ x in B, (f x-m)^2 ∂μ) ≤ D :=
    (setIntegral_le_integral hvI (Eventually.of_forall (fun x => sq_nonneg _))).trans hv
  have hmB : m^2*(μ B).toReal ≤ 2*D + 2*M^2*(μ B).toReal := by
    have he : (∫ _ in B, m^2 ∂μ) ≤ ∫ x in B, 2*(f x-m)^2 + 2*M^2 ∂μ := by
      apply integral_mono_ae (integrable_const _) ((hvI.restrict.const_mul 2).add (integrable_const _))
      filter_upwards [ha] with x hx
      have hM := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hx)).mpr hx
      simp only [Real.norm_eq_abs,sq_abs] at hM
      change m^2 ≤ 2*(f x-m)^2+2*M^2
      nlinarith [sq_nonneg (2*f x-m)]
    rw [integral_add (hvI.restrict.const_mul 2) (integrable_const _),integral_const_mul] at he
    simp only [integral_const,smul_eq_mul,measureReal_def,Measure.restrict_apply_univ] at he
    nlinarith
  have hm : m^2 ≤ (2*D + 2*M^2*(μ B).toReal)/(μ B).toReal :=
    (le_div_iff₀ hβ).mpr hmB
  have he : (∫ x, (f x)^2 ∂μ) ≤ ∫ x, 2*(f x-m)^2+2*m^2 ∂μ := by
    apply integral_mono_ae hfi ((hvI.const_mul 2).add (integrable_const _))
    exact Eventually.of_forall fun x => by
      change (f x)^2 ≤ 2*(f x-m)^2+2*m^2
      nlinarith [sq_nonneg (f x-2*m)]
  rw [integral_add (hvI.const_mul 2) (integrable_const _),integral_const_mul] at he
  simp only [integral_const,smul_eq_mul,measureReal_def] at he
  exact he.trans (add_le_add (mul_le_mul_of_nonneg_left hv (by norm_num))
    (by nlinarith [mul_le_mul_of_nonneg_right hm (ENNReal.toReal_nonneg (a := μ univ))]))
end StrictHotSpots

end AnchoredEstimateInteriorSupportLayer


section FiniteEnergyPrimitiveInteriorSupportLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots



theorem finiteEnergy_hasH1Gradient {Ω : Set Plane} (ho : IsOpen Ω)
    (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {r : Plane → ℝ}
    (hr : ContDiffOn ℝ ∞ r Ω) (hg : MemLp (gradient r) 2 (volume.restrict Ω)) :
    HasH1Gradient Ω r (gradient r) := by
  let : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using hb.measure_lt_top⟩
  have hvol : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (ne_of_gt (ho.measure_pos volume hne)) hb.measure_lt_top.ne
  have hrm : AEStronglyMeasurable r (volume.restrict Ω) := hr.continuousOn.aestronglyMeasurable ho.measurableSet
  let F (n : ℕ) (x : Plane) := Truncation.trunc n (r x)
  have hF (n : ℕ) : ContDiffOn ℝ ∞ (F n) Ω := (Truncation.smooth n).comp_contDiffOn hr
  have hmF (n : ℕ) : MemLp (F n) 2 (volume.restrict Ω) := by
    apply (memLp_const (((n:ℝ)+1)*(Real.pi/2))).mono
      ((hF n).continuousOn.aestronglyMeasurable ho.measurableSet)
    exact Eventually.of_forall fun x => (Truncation.bounded n (r x)).trans (le_abs_self _)
  have hgrad (n : ℕ) {x : Plane} (hx : x ∈ Ω) :
      gradient (F n) x = deriv (Truncation.trunc n) (r x) • gradient r x := by
    apply (InnerProductSpace.toDual ℝ Plane).injective
    simp only [gradient,map_smul,LinearIsometryEquiv.apply_symm_apply]
    have hdx := ((hr.contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact (((Truncation.smooth n).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x hdx).fderiv
  have hgradle (n : ℕ) : ∀ᵐ x ∂volume.restrict Ω, ‖gradient (F n) x‖ ≤ ‖gradient r x‖ := by
    filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    rw [hgrad n hx,norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (Truncation.deriv_bound n (r x))
  have hmG (n : ℕ) : MemLp (gradient (F n)) 2 (volume.restrict Ω) := by
    apply hg.mono _ (hgradle n)
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ (F n)) Ω := (hF n).fderiv_of_isOpen ho (by simp)
    have hc : ContinuousOn (gradient (F n)) Ω :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
        hd.continuousOn
    exact hc.aestronglyMeasurable ho.measurableSet
  have hH (n : ℕ) : HasH1Gradient Ω (F n) (gradient (F n)) :=
    HasH1Gradient.of_contDiffOn ho (hF n) (hmF n) (hmG n)
  let m (n : ℕ) := (∫ x in Ω, F n x)/(volume Ω).toReal
  let G := ∫ x in Ω, ‖gradient r x‖^2
  have hm (n : ℕ) : (∫ x in Ω, F n x-m n) = 0 := by
    rw [integral_sub ((hmF n).integrable (by norm_num)) (integrable_const _)]
    simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
    change (∫ x in Ω, F n x)-(volume Ω).toReal*m n = 0
    dsimp [m]
    field_simp
    ring
  have hvar (n : ℕ) : (∫ x in Ω, (F n x-m n)^2) ≤ G/firstPositiveNeumannValue Ω := by
    have hH' : HasH1Gradient Ω (fun x => F n x-m n) (gradient (F n)) := by
      simpa only [sub_zero] using! (hH n).sub (HasH1Gradient.const hb (m n))
    have he := rayleigh_inequality_all hH' (hm n)
    have he' : (∫ x in Ω, ‖gradient (F n) x‖^2) ≤ G := by
      apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm (hmG n).aestronglyMeasurable).mp (hmG n))
        ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
      exact (hgradle n).mono fun x hx => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx
    exact (le_div_iff₀ hμ).mpr (by nlinarith)
  obtain ⟨a,ha⟩ := hne
  have heΩ : ∀ᶠ x in 𝓝 a, x ∈ Ω := ho.mem_nhds ha
  have he : ∀ᶠ x in 𝓝 a, x ∈ Ω ∧ ‖r x‖ < ‖r a‖+1 :=
    heΩ.and (((hr.continuousOn a ha).continuousAt (ho.mem_nhds ha)).norm.eventually
      (gt_mem_nhds (by linarith : ‖r a‖ < ‖r a‖+1)))
  obtain ⟨ε,hε,hεs⟩ := Metric.mem_nhds_iff.mp he
  have hBΩ : ball a ε ⊆ Ω := fun x hx => (hεs hx).1
  have hβ : 0 < ((volume.restrict Ω) (ball a ε)).toReal := by
    rw [Measure.restrict_apply measurableSet_ball,inter_eq_left.mpr hBΩ]
    exact ENNReal.toReal_pos (ne_of_gt (isOpen_ball.measure_pos volume (nonempty_ball.mpr hε)))
      (measure_ball_lt_top.ne)
  let C := 2*(G/firstPositiveNeumannValue Ω) +
    2*((2*(G/firstPositiveNeumannValue Ω)+2*(‖r a‖+1)^2*((volume.restrict Ω) (ball a ε)).toReal)/
      ((volume.restrict Ω) (ball a ε)).toReal)*((volume.restrict Ω) univ).toReal
  have hbound (n : ℕ) : (∫ x in Ω, (F n x)^2) ≤ C := by
    apply anchored_l2_bound measurableSet_ball hβ (hmF n) (m := m n)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (Truncation.norm_le n (r x)).trans (hεs hx).2.le
    · exact hvar n
  have hLP (n : ℕ) : eLpNorm (F n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal (Real.sqrt (max C 0)) := by
    rw [(hmF n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
    rw [← Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ((hbound n).trans (le_max_left C 0)))
  have hrL : MemLp r 2 (volume.restrict Ω) := by
    exact (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hLP)
      (fun n => (hmF n).aestronglyMeasurable) hrm
      (Eventually.of_forall (fun x => Truncation.tends (r x)))).trans_lt
      ENNReal.ofReal_lt_top
  exact HasH1Gradient.of_contDiffOn ho hr hrL hg
end StrictHotSpots

end FiniteEnergyPrimitiveInteriorSupportLayer


section SmoothClosedPotentialInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots



theorem closed_finiteEnergy_potential {Ω : Set Plane} (ho : IsOpen Ω)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω)
    {Z : Plane → Plane} (hZ : ContDiffOn ℝ ∞ Z Ω)
    (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : ∀ a ∈ Ω, ∀ x y,
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a x y =
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a y x) :
    ∃ r : Plane → ℝ, ContDiffOn ℝ ∞ r Ω ∧ HasH1Gradient Ω r Z := by
  have hw : ContDiffOn ℝ ∞ (fun a => innerSL ℝ (Z a)) Ω :=
    (innerSL ℝ (E := Plane)).contDiff.comp_contDiffOn hZ
  obtain ⟨r,hr⟩ := Primitives.exists_primitive ho hs (hw.differentiableOn (by simp)) hd
  have he : EqOn (fderiv ℝ r) (fun a => innerSL ℝ (Z a)) Ω := fun a ha => (hr a ha).fderiv
  have hrs : ContDiffOn ℝ ∞ r Ω := by
    rw [contDiffOn_infty_iff_fderiv_of_isOpen ho]
    exact ⟨fun a ha => (hr a ha).differentiableAt.differentiableWithinAt, hw.congr he⟩
  have heg : ∀ a ∈ Ω, gradient r a = Z a := by
    intro a ha
    apply (InnerProductSpace.toDual ℝ Plane).injective
    change (InnerProductSpace.toDual ℝ Plane) ((InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ r a)) = _
    rw [LinearIsometryEquiv.apply_symm_apply,he ha]
    ext y
    rfl
  have hae : gradient r =ᵐ[volume.restrict Ω] Z :=
    (ae_restrict_mem ho.measurableSet).mono fun a ha => heg a ha
  have hgr : MemLp (gradient r) 2 (volume.restrict Ω) := (memLp_congr_ae hae).mpr hm
  have hne : Ω.Nonempty := by
    let : SimplyConnectedSpace Ω := hs
    obtain ⟨x⟩ := (inferInstance : Nonempty Ω)
    exact ⟨x,x.property⟩
  refine ⟨r,hrs,?_⟩
  exact (finiteEnergy_hasH1Gradient ho hne hb hμ hrs hgr).congr (Filter.Eventually.of_forall (fun _ => rfl)) hae



theorem closed_orthogonal_gradient_zero {Ω : Set Plane} (ho : IsOpen Ω)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω)
    {Z : Plane → Plane} (hZ : ContDiffOn ℝ ∞ Z Ω)
    (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : ∀ a ∈ Ω, ∀ x y,
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a x y =
      fderiv ℝ (fun a => innerSL ℝ (Z a)) a y x)
    (hz : ∀ v g, HasH1Gradient Ω v g → (∫ x in Ω, inner ℝ (Z x) (g x)) = 0) :
    ∀ x ∈ Ω, Z x = 0 := by
  obtain ⟨r,_,hr⟩ := closed_finiteEnergy_potential ho hs hb hμ hZ hm hd
  have he := hz r Z hr
  simp only [real_inner_self_eq_norm_sq] at he
  have hI := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hae : ∀ᵐ x ∂volume.restrict Ω, ‖Z x‖^2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg ‖Z x‖)) hI).mp he
  have hae' : Z =ᵐ[volume.restrict Ω] 0 := hae.mono fun x hx => by simpa using hx
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae' ho hZ.continuousOn continuousOn_const
end StrictHotSpots

end SmoothClosedPotentialInteriorSupportLayer


section WeakHodgeRegularityInteriorSupportLayer

open Set MeasureTheory
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge

def WeakDivZero (Ω : Set Plane) (Z : Plane → Plane) : Prop :=
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x in Ω, inner ℝ (Z x) (gradient φ x)) = 0

def WeakCurlZero (Ω : Set Plane) (Z : Plane → Plane) : Prop :=
  ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ x in Ω, inner ℝ (Z x) (rot (gradient φ x))) = 0

lemma weak_harmonic_coordinates {Ω : Set Plane} (ho : IsOpen Ω)
    {Z : Plane → Plane} (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : WeakDivZero Ω Z) (hc : WeakCurlZero Ω Z) (i : Fin 2) :
    PlaneWeakEquation Ω 0 (fun x => c i (Z x)) := by
  intro φ hφ hk hs
  have hI (j : Fin 2) : IntegrableOn (fun x => inner ℝ (Z x) (gradient (D j φ) x)) Ω :=
    integrable_inner_of_memLp hm (HasH1Gradient.test ho (D_smooth hφ j) (D_compact hk j)).2.1
  have hJ (j : Fin 2) : IntegrableOn (fun x => inner ℝ (Z x) (rot (gradient (D j φ) x))) Ω :=
    integrable_inner_of_memLp hm (rot.comp_memLp' (HasH1Gradient.test ho (D_smooth hφ j) (D_compact hk j)).2.1)
  have hD (j : Fin 2) := hd _ (D_smooth hφ j) (D_compact hk j) ((D_support φ j).trans hs)
  have hC (j : Fin 2) := hc _ (D_smooth hφ j) (D_compact hk j) ((D_support φ j).trans hs)
  have he0 (x : Plane) : c 0 (Z x)*Δ φ x =
      inner ℝ (Z x) (gradient (D 0 φ) x) - inner ℝ (Z x) (rot (gradient (D 1 φ) x)) := by
    rw [laplace_two hφ,inner_gradient,inner_rot_gradient,D_D hφ 1 0]
    ring
  have he1 (x : Plane) : c 1 (Z x)*Δ φ x =
      inner ℝ (Z x) (gradient (D 1 φ) x) + inner ℝ (Z x) (rot (gradient (D 0 φ) x)) := by
    rw [laplace_two hφ,inner_gradient,inner_rot_gradient,D_D hφ 1 0]
    ring
  fin_cases i
  · change (∫ x in Ω, c 0 (Z x) * Δ φ x) = _
    simp_rw [he0]
    rw [integral_sub (hI 0) (hJ 1),hD 0,hC 1]
    simp
  · change (∫ x in Ω, c 1 (Z x) * Δ φ x) = _
    simp_rw [he1]
    rw [integral_add (hI 1) (hJ 0),hD 1,hC 0]
    simp



theorem weak_divCurl_smooth {Ω : Set Plane} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) {Z : Plane → Plane} (hm : MemLp Z 2 (volume.restrict Ω))
    (hd : WeakDivZero Ω Z) (hc : WeakCurlZero Ω Z) :
    ∃ W : Plane → Plane, ContDiffOn ℝ ∞ W Ω ∧ W =ᵐ[volume.restrict Ω] Z := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hh (i : Fin 2) := Weyl.plane_representative ho
    ((hm.inner_const (e i)).integrable (by norm_num)) (weak_harmonic_coordinates ho hm hd hc i)
  choose f hf he using hh
  refine ⟨fun x => f 0 x • e 0+f 1 x • e 1,(hf 0).smul contDiffOn_const |>.add ((hf 1).smul contDiffOn_const),?_⟩
  filter_upwards [he 0,he 1] with x hx0 hx1
  rw [hx0,hx1,expand]

lemma smooth_curl_zero {Ω : Set Plane} (ho : IsOpen Ω)
    {W : Plane → Plane} (hW : ContDiffOn ℝ ∞ W Ω) (hc : WeakCurlZero Ω W) :
    ∀ x ∈ Ω, D 0 (fun y => c 1 (W y)) x = D 1 (fun y => c 0 (W y)) x := by
  let a : Plane → ℝ := fun x => c 0 (W x)
  let b : Plane → ℝ := fun x => c 1 (W x)
  have ha : ContDiffOn ℝ ∞ a Ω := hW.inner ℝ contDiffOn_const
  have hb : ContDiffOn ℝ ∞ b Ω := hW.inner ℝ contDiffOn_const
  have hda := directionalDerivative_contDiffOn ho ha (e 1)
  have hdb := directionalDerivative_contDiffOn ho hb (e 0)
  have hcont : ContinuousOn (fun x => D 0 b x-D 1 a x) Ω := hdb.continuousOn.sub hda.continuousOn
  have hz := ho.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn ho.measurableSet (μ := volume)) ?_
  · have he : (fun x => D 0 b x-D 1 a x) =ᵐ[volume.restrict Ω] 0 := (ae_restrict_iff' ho.measurableSet).mpr hz
    have hh := MeasureTheory.Measure.eqOn_open_of_ae_eq he ho hcont continuousOn_const
    intro x hx
    exact sub_eq_zero.mp (hh hx)
  · intro φ hφ hk hs
    have hi : IntegrableOn (fun x => D 0 b x*φ x) Ω := (integrable_mul_test ho hdb.continuousOn hφ.continuous hk hs).integrableOn
    have hj : IntegrableOn (fun x => D 1 a x*φ x) Ω := (integrable_mul_test ho hda.continuousOn hφ.continuous hk hs).integrableOn
    have hi' : IntegrableOn (fun x => b x*D 0 φ x) Ω := (integrable_mul_test ho hb.continuousOn (D_smooth hφ 0).continuous
      (D_compact hk 0) ((D_support φ 0).trans hs)).integrableOn
    have hj' : IntegrableOn (fun x => a x*D 1 φ x) Ω := (integrable_mul_test ho ha.continuousOn (D_smooth hφ 1).continuous
      (D_compact hk 1) ((D_support φ 1).trans hs)).integrableOn
    have h0 := integral_mul_test_fderiv ho hb hφ hk hs (e 0)
    have h1 := integral_mul_test_fderiv ho ha hφ hk hs (e 1)
    have h := hc φ hφ hk hs
    simp_rw [inner_rot_gradient] at h
    rw [integral_sub hi' hj'] at h
    change (∫ x in Ω, b x * D 0 φ x) = -(∫ x in Ω, D 0 b x * φ x) at h0
    change (∫ x in Ω, a x * D 1 φ x) = -(∫ x in Ω, D 1 a x * φ x) at h1
    rw [h0,h1] at h
    simp only [smul_eq_mul]
    simp_rw [mul_comm (φ _) _]
    rw [← setIntegral_mul_test hs]
    simp_rw [sub_mul]
    rw [integral_sub hi hj]
    linarith

lemma smooth_closed {Ω : Set Plane} (ho : IsOpen Ω)
    {W : Plane → Plane} (hW : ContDiffOn ℝ ∞ W Ω) (hc : WeakCurlZero Ω W) :
    ∀ a ∈ Ω, ∀ x y,
      fderiv ℝ (fun a => innerSL ℝ (W a)) a x y =
      fderiv ℝ (fun a => innerSL ℝ (W a)) a y x := by
  intro a ha x y
  have hw : DifferentiableAt ℝ W a :=
    (hW.differentiableOn (by simp) a ha).differentiableAt (ho.mem_nhds ha)
  have hform (x y : Plane) :
      fderiv ℝ (fun a => innerSL ℝ (W a)) a x y = inner ℝ (fderiv ℝ W a x) y := by
    have hh : HasFDerivAt (fun a => innerSL ℝ (W a))
        ((innerSL ℝ (E := Plane)).comp (fderiv ℝ W a)) a :=
      (innerSL ℝ (E := Plane)).hasFDerivAt.comp a hw.hasFDerivAt
    rw [hh.fderiv]
    rfl
  have hcoord (i j : Fin 2) : D i (fun y => c j (W y)) a =
      inner ℝ (fderiv ℝ W a (e i)) (e j) := by
    change fderiv ℝ (fun y => inner ℝ (W y) (e j)) a (e i) = _
    rw [fderiv_inner_apply ℝ hw (differentiableAt_const _)]
    simp only [fderiv_fun_const,Pi.zero_apply,zero_apply,inner_zero_right,zero_add]
  have hc' := smooth_curl_zero ho hW hc a ha
  rw [hcoord,hcoord] at hc'
  simp_rw [hform]
  conv_lhs => rw [← expand x,← expand y]
  conv_rhs => rw [← expand y,← expand x]
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
    inner_smul_right,conj_trivial]
  rw [hc']
  ring




theorem weak_divCurl_zero {Ω : Set Plane} (ho : IsOpen Ω)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω)
    {Z : Plane → Plane} (hm : MemLp Z 2 (volume.restrict Ω))
    (hc : WeakCurlZero Ω Z)
    (hz : ∀ v g, HasH1Gradient Ω v g → (∫ x in Ω, inner ℝ (Z x) (g x)) = 0) :
    Z =ᵐ[volume.restrict Ω] 0 := by
  have hd : WeakDivZero Ω Z := fun φ hφ hk _ => hz φ _ (HasH1Gradient.test ho hφ hk)
  obtain ⟨W,hW,he⟩ := weak_divCurl_smooth ho hb hm hd hc
  have hwm : MemLp W 2 (volume.restrict Ω) := (memLp_congr_ae he).mpr hm
  have heI (f : Plane → Plane) : (∫ x in Ω, inner ℝ (W x) (f x)) =
      ∫ x in Ω, inner ℝ (Z x) (f x) :=
    integral_congr_ae (he.mono fun x hx => congrArg (fun t => inner ℝ t (f x)) hx)
  have hwc : WeakCurlZero Ω W := fun φ hφ hk ht => (heI _).trans (hc φ hφ hk ht)
  have hwz : ∀ v g, HasH1Gradient Ω v g → (∫ x in Ω, inner ℝ (W x) (g x)) = 0 :=
    fun v g hv => (heI g).trans (hz v g hv)
  have hw0 := closed_orthogonal_gradient_zero ho hs hb hμ hW hwm (smooth_closed ho hW hwc) hwz
  exact he.symm.trans ((ae_restrict_mem ho.measurableSet).mono fun x hx => hw0 x hx)

end StrictHotSpots.Hodge

end WeakHodgeRegularityInteriorSupportLayer



end

end ActualVectorSupport

end OAI
