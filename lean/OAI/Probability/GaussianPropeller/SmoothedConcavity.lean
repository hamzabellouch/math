import OAI.Probability.GaussianPropeller.HeatMaximum

namespace OAI

universe uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace

open scoped NNReal
namespace GaussianPropeller.EhrhardSmooth
open GaussianPropeller.Quantile GaussianPropeller.QuantilePDE GaussianPropeller.HeatConvolution
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

noncomputable def qheat (f : E → ℝ) (t : ℝ) (x : E) : ℝ := q (heat (fun y => Φ (f y)) t x)

lemma heat_mem {f : E → ℝ} (hf : Continuous f) (t : ℝ) (x : E) :
    heat (fun y => Φ (f y)) t x ∈ Ioo (0:ℝ) 1 := integral_Φ_mem (by fun_prop)

lemma continuous_qheat {f : E → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × E => qheat f p.1 p.2) := by
  have hh := continuous_heat (continuous_Φ.comp hf) (SmoothCDF.cdf_bound f)
  exact continuous_iff_continuousAt.mpr fun p =>
    (continuousAt_q (heat_mem hf p.1 p.2)).comp (f := fun p : ℝ × E => heat (fun y => Φ (f y)) p.1 p.2) hh.continuousAt

lemma qheat_zero (f : E → ℝ) (x : E) : qheat f 0 x = f x := by
  simp [qheat, heat, q_Φ]

lemma qheat_le {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) (x y : E) :
    qheat f t x ≤ qheat f t y + L*‖x-y‖ := by
  have hc := hf.continuous
  have hfm : AEStronglyMeasurable (fun z : E => f (y+Real.sqrt t • z)) γ := by fun_prop
  have hxm : AEStronglyMeasurable (fun z : E => f (x+Real.sqrt t • z)) γ := by fun_prop
  have hxy (z : E) : f (x+Real.sqrt t • z) ≤ f (y+Real.sqrt t • z)+L*‖x-y‖ := by
    have hh := hf.dist_le_mul (x+Real.sqrt t • z) (y+Real.sqrt t • z)
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_right_eq_sub] at hh
    linarith only [le_abs_self (f (x+Real.sqrt t • z)-f (y+Real.sqrt t • z)), hh]
  have hint : (∫ z : E, Φ (f (x+Real.sqrt t • z)) ∂γ) ≤
      ∫ z : E, Φ (f (y+Real.sqrt t • z)+L*‖x-y‖) ∂γ :=
    integral_mono (integrable_Φ_comp hxm) (integrable_Φ_comp (hfm.add_const _))
      (fun z => strictMono_Φ.monotone (hxy z))
  exact (strictMonoOn_q.monotoneOn (integral_Φ_mem hxm)
    (integral_Φ_mem (hfm.add_const _)) hint).trans (quantile_shift_le hfm (by positivity))

lemma qheat_lipschitz {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (t : ℝ) :
    LipschitzWith L (qheat f t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm, abs_le]
  have hxy := qheat_le hf t x y
  have hyx := qheat_le hf t y x
  rw [norm_sub_rev y x] at hyx
  constructor <;> linarith only [hxy,hyx]

lemma growth_bound {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, ∀ x, |qheat f t x| ≤ M+L*‖x‖ := by
  have hc : Continuous (fun t : ℝ => |qheat f t 0|) :=
    ((continuous_qheat hf.continuous).comp (continuous_id.prodMk continuous_const)).abs
  obtain ⟨M,hM⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨max M 0, le_max_right _ _,?_⟩
  intro t ht x
  have hm : |qheat f t 0| ≤ max M 0 := (hM (mem_image_of_mem _ ht)).trans (le_max_left _ _)
  have hd := (qheat_lipschitz hf t).dist_le_mul x 0
  simp only [Real.dist_eq, dist_zero_right] at hd
  have hh := abs_sub_le (qheat f t x) (qheat f t 0) 0
  simp only [sub_zero] at hh
  linarith only [hh,hm,hd]

lemma qheat_concave {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hK : Continuous K)
    {L : ℝ≥0} {D : ℝ} (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D)
    (hconc : ConcaveOn ℝ univ f) {T : ℝ} (hT : 0 ≤ T) :
    ConcaveOn ℝ univ (qheat f T) := by
  have hcf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hcg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hlip : LipschitzWith L f := lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hf x).differentiableAt) (fun x => by
      rw [(hf x).fderiv]
      exact_mod_cast (show ‖innerSL ℝ (g x)‖ ≤ L by rw [innerSL_apply_norm]; exact hL x))
  let F : E → ℝ := fun x => Φ (f x)
  let G : E → E := SmoothCDF.grad f g
  let J : E → E →L[ℝ] E := SmoothCDF.hess f g K
  have hF (x : E) : HasFDerivAt F (innerSL ℝ (G x)) x := SmoothCDF.fderiv hf x
  have hG (x : E) : HasFDerivAt G (J x) x := SmoothCDF.grad_fderiv hf hg x
  have hcG : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
  have hcJ : Continuous J := SmoothCDF.continuous_hess hcf hcg hK
  have hFB (x : E) : ‖F x‖ ≤ 1 := SmoothCDF.cdf_bound f x
  have hGB (x : E) : ‖G x‖ ≤ φ 0*L := SmoothCDF.grad_bound hL x
  have hJB (x : E) : ‖J x‖ ≤ φ 0*(D+(L:ℝ)^2) := SmoothCDF.hess_bound L.coe_nonneg hL hD x
  let u : ℝ → E → ℝ := heat F
  let v : ℝ → E → ℝ := qheat f
  let p : ℝ → E → E := fun t x => (φ (v t x))⁻¹ • heat G t x
  let H : ℝ → E → E → ℝ := fun t x e =>
    (φ (v t x))⁻¹*⟪heat J t x e,e⟫ + v t x*(φ (v t x))⁻¹^2*⟪heat G t x,e⟫^2
  have hu (t : ℝ) (x : E) : u t x ∈ Ioo (0:ℝ) 1 := heat_mem hcf t x
  have hdu (t : ℝ) (x : E) : HasFDerivAt (u t) (innerSL ℝ (heat G t x)) x :=
    heat_gradient hF hcG hFB hGB t x
  have hdg (t : ℝ) (x : E) : HasFDerivAt (heat G t) (heat J t x) x :=
    fderiv_heat hG hcJ hGB hJB t x
  have hdv (t : ℝ) (x : E) : HasFDerivAt (v t) (innerSL ℝ (p t x)) x :=
    quantile_fderiv (hu t x) (hdu t x)
  obtain ⟨M,hM,hgrowth⟩ := growth_bound hlip T
  apply HeatMaximum.heat_concave (EuclideanSpace.basisFun ι ℝ)
    (fun i => (EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one i)
    (p := p) (H := H) hT L.coe_nonneg hM (continuous_qheat hcf)
  · change ConcaveOn ℝ univ (qheat f 0)
    rw [show qheat f 0 = f from funext (qheat_zero f)]
    exact hconc
  · intro t _ x; exact hdv t x
  · intro t _ x e
    exact quantile_gradient_line_derivative (hu t) (hdu t) (hdg t) x e
  · intro t ht x
    have hh := (hasDerivAt_q (hu t x)).comp t (heat_equation hF hG hcJ hFB hGB hJB ht.1 x)
    have heq := trace_quantile_hessian (EuclideanSpace.basisFun ι ℝ)
      (v t x) ((φ (v t x))⁻¹) (heat G t x) (heat J t x)
    change HasDerivAt (fun s => q (u s x))
      (((∑ i : ι, H t x (EuclideanSpace.basisFun ι ℝ i))-v t x*‖p t x‖^2)/2) t
    convert hh using 1 <;> try rfl
    change ((∑ i : ι, ((φ (v t x))⁻¹*⟪heat J t x (EuclideanSpace.basisFun ι ℝ i),
      EuclideanSpace.basisFun ι ℝ i⟫ + v t x*(φ (v t x))⁻¹^2*⟪heat G t x,
      EuclideanSpace.basisFun ι ℝ i⟫^2))-v t x*‖(φ (v t x))⁻¹ • heat G t x‖^2)/2 = _
    rw [heq]
    change (φ (q (u t x)))⁻¹*(∑ i : ι, ⟪heat J t x (EuclideanSpace.basisFun ι ℝ i),
      EuclideanSpace.basisFun ι ℝ i⟫)/2 = _
    ring
  · intro t _ x
    have hh := (hdv t x).le_of_lipschitz (qheat_lipschitz hlip t)
    simpa only [innerSL_apply_norm] using hh
  · exact hgrowth

end GaussianPropeller.EhrhardSmooth

end OAI
