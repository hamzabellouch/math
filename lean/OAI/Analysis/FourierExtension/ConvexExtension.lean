import Mathlib
import OAI.Analysis.FourierExtension.SmoothCharts
import OAI.Analysis.FourierExtension.LocalizedFourier

namespace OAI

/-! Smooth cutoffs and convex continuation. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section
open Filter
open scoped Topology ContDiff
open MeasureTheory Set
open scoped ContDiff FourierTransform InnerProductSpace ENNReal
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace DiagonalExtension.CutoffHessian
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma iteratedFDeriv_section {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    (p : ℝ) (z : E) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => F (p,y)) z =
      (iteratedFDeriv ℝ j F (p,z)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℝ E) := by
  let g : ℝ × E → ℝ := fun q => F ((p,0) + q)
  have hg : ContDiff ℝ ∞ g := hF.comp (contDiff_const.add contDiff_id)
  have heq := (ContinuousLinearMap.inr ℝ ℝ E).iteratedFDeriv_comp_right hg z
    (i := j) (by exact WithTop.coe_le_coe.mpr le_top)
  have ht := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := F) (s := Set.univ)
    j (p, (0:E)) ((0:ℝ),z)
  simp only [Set.vadd_set_univ, iteratedFDerivWithin_univ, Prod.mk_add_mk,
    add_zero, zero_add] at ht
  simp only [Function.comp_def, g, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] at heq
  rw [show iteratedFDeriv ℝ j (fun q : ℝ × E => F ((p,0) + q)) (0,z) =
    iteratedFDeriv ℝ j F (p,z) from ht] at heq
  exact heq

lemma continuous_section_derivative {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F) (j : ℕ) :
    Continuous (fun q : ℝ × E => iteratedFDeriv ℝ j (fun y => F (q.1,y)) q.2) := by
  simp_rw [iteratedFDeriv_section hF]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ ℝ E)).continuous.comp
    (hF.continuous_iteratedFDeriv (by exact WithTop.coe_le_coe.mpr le_top))

lemma uniform_derivative_small {F : ℝ × E → ℝ} (hF : ContDiff ℝ ∞ F)
    {K : Set E} (hK : IsCompact K) (hzero : ∀ x, F (0,x) = 0)
    (hsupp : ∀ δ, tsupport (fun x => F (δ,x)) ⊆ K) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ x, ‖iteratedFDeriv ℝ j (fun z => F (δ,z)) x‖ < ε := by
  have hz (x : E) : iteratedFDeriv ℝ j (fun z => F (0,z)) x = 0 := by
    simp only [show (fun z => F (0,z)) = (fun _ => 0) from funext hzero]
    simp
  have hlocal := hK.eventually_forall_of_forall_eventually (x₀ := (0 : ℝ))
    (P := fun δ x => ‖iteratedFDeriv ℝ j (fun z => F (δ,z)) x‖ < ε)
    (fun x hx => ((continuous_section_derivative hF j).norm.continuousAt.eventually (gt_mem_nhds (by simpa [hz] using hε))))
  filter_upwards [hlocal] with δ hδ x
  by_cases hx : x ∈ K
  · exact hδ x hx
  · have hd : iteratedFDeriv ℝ j (fun z => F (δ,z)) x = 0 := by
      apply Function.notMem_support.mp
      exact fun h => hx (hsupp δ (support_iteratedFDeriv_subset j h))
    simpa [hd] using hε

def profile (φ χ : E → ℝ) (a : E) (q : ℝ × E) : ℝ :=
  χ q.2 * PacketTaylor.remainder φ ((a,q.1),q.2)

variable [FiniteDimensional ℝ E]

lemma smooth_profile {φ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (a : E) : ContDiff ℝ ∞ (profile φ χ a) :=
  (hχ.comp contDiff_snd).mul ((PacketTaylor.smooth_remainder hφ).comp (by fun_prop))

omit [FiniteDimensional ℝ E] in
lemma profile_zero {φ χ : E → ℝ} {a : E} (h0 : fderiv ℝ (fderiv ℝ φ) a = 0) (x : E) :
    profile φ χ a (0,x) = 0 := by
  simp [profile,PacketTaylor.remainder,h0]

theorem profile_hessian_small {φ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {a : E}
    (h0 : fderiv ℝ (fderiv ℝ φ) a = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ x,
      ‖iteratedFDeriv ℝ 2 (fun z => profile φ χ a (δ,z)) x‖ < ε := by
  apply uniform_derivative_small (smooth_profile hφ hχ a) hχc
    (profile_zero h0) _ 2 hε
  intro δ
  apply closure_mono
  intro x hx
  simp only [Function.mem_support,profile] at *
  exact fun h => hx (by simp [h])

omit [FiniteDimensional ℝ E] in
lemma scaled_hessian_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {δ : ℝ} (hδ : δ ≠ 0) (x v : E) :
    (fderiv ℝ (fderiv ℝ (fun y => δ^2 * f (δ⁻¹ • y))) x v) v =
      (fderiv ℝ (fderiv ℝ f) (δ⁻¹ • x) v) v := by
  let L : E →L[ℝ] E := δ⁻¹ • ContinuousLinearMap.id ℝ E
  have hfL : ContDiff ℝ ∞ (f ∘ L) := hf.comp L.contDiff
  have hh := iteratedFDeriv_const_smul_apply' (a := δ^2)
    ((hfL.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt (x := x))
  have hL := L.iteratedFDeriv_comp_right hf x (i := 2) (by exact WithTop.coe_le_coe.mpr le_top)
  have hv := congrArg (fun B => B ![v,v]) hh
  rw [hL] at hv
  simp only [iteratedFDeriv_two_apply, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_smul,
    ContinuousLinearMap.id_apply,smul_eq_mul,L] at hv
  convert hv using 1
  · congr 1
  · field_simp

omit [FiniteDimensional ℝ E] in
lemma hessian_add {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x v : E) :
    (fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x v) v =
      (fderiv ℝ (fderiv ℝ f) x v) v + (fderiv ℝ (fderiv ℝ g) x v) v := by
  have hd := iteratedFDeriv_add_apply (i := 2)
    ((hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt (x := x))
    ((hg.of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt (x := x))
  have hv := congrArg (fun B => B ![v,v]) hd
  simpa only [iteratedFDeriv_two_apply, add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,Pi.add_apply] using
    (show (iteratedFDeriv ℝ 2 (fun y => f y + g y) x) ![v,v] = _ from hv)

def patch (φ χ : E → ℝ) (δ : ℝ) (x : E) : ℝ := χ (δ⁻¹ • x) * φ x

omit [FiniteDimensional ℝ E] in
lemma patch_scaled {φ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hval : φ 0 = 0) (hder : fderiv ℝ φ 0 = 0) {δ : ℝ} (hδ : δ ≠ 0) :
    patch φ χ δ = fun x => δ^2 * profile φ χ 0 (δ,δ⁻¹ • x) := by
  ext x
  have ht := PacketTaylor.taylor_identity hφ 0 (δ⁻¹ • x) δ
  simp only [zero_add,smul_smul,mul_inv_cancel₀ hδ,one_smul,hval,hder,
    zero_apply,mul_zero,add_zero] at ht
  dsimp [patch,profile]
  rw [ht]
  ring

lemma patch_hessian_small {φ χ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hval : φ 0 = 0) (hder : fderiv ℝ φ 0 = 0)
    (hder2 : fderiv ℝ (fderiv ℝ φ) 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), δ ≠ 0 → ∀ x v,
      ‖(fderiv ℝ (fderiv ℝ (patch φ χ δ)) x v) v‖ ≤ ε * ‖v‖ ^ 2 := by
  filter_upwards [profile_hessian_small hφ hχ hχc hder2 hε] with δ hδ hn x v
  have hsec : ContDiff ℝ ∞ (fun z => profile φ χ 0 (δ,z)) :=
    (smooth_profile hφ hχ 0).comp (by fun_prop)
  rw [patch_scaled hφ hval hder hn, scaled_hessian_apply hsec hn]
  have hb := (iteratedFDeriv ℝ 2 (fun z => profile φ χ 0 (δ,z)) (δ⁻¹ • x)).le_opNorm ![v,v]
  have hb' : ‖(fderiv ℝ (fderiv ℝ (fun z => profile φ χ 0 (δ,z))) (δ⁻¹ • x) v) v‖ ≤
      ‖iteratedFDeriv ℝ 2 (fun z => profile φ χ 0 (δ,z)) (δ⁻¹ • x)‖ * ‖v‖ ^ 2 := by
    simpa only [iteratedFDeriv_two_apply,Fin.prod_univ_two,Matrix.cons_val_zero,
      Matrix.cons_val_one,pow_two] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_right (hδ _).le (sq_nonneg _))

theorem exists_small_patch {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hval : φ 0 = 0) (hder : fderiv ℝ φ 0 = 0)
    (hder2 : fderiv ℝ (fderiv ℝ φ) 0 = 0) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      P =ᶠ[𝓝 0] φ ∧ tsupport P ⊆ Metric.ball 0 R ∧
      ∀ x v, ‖(fderiv ℝ (fderiv ℝ P) x v) v‖ ≤ ε * ‖v‖^2 := by
  let b : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
    (patch_hessian_small hφ b.contDiff b.hasCompactSupport hval hder hder2 hε)
  let δ := min r (R/2) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by dsimp [δ]; linarith [min_le_left r (R/2)]
  have hδR : 2 * δ < R := by dsimp [δ]; linarith [min_le_right r (R/2)]
  have hsmall := hrU (show δ ∈ Metric.ball (0 : ℝ) r by simpa [Real.dist_eq,abs_of_pos hδ] using hδr)
  let P := patch φ b δ
  have hb : ContDiff ℝ ∞ (fun x : E => b (δ⁻¹ • x)) := b.contDiff.comp (contDiff_const.smul contDiff_id)
  have hPc : HasCompactSupport P :=
    (b.hasCompactSupport.comp_homeomorph (Homeomorph.smulOfNeZero δ⁻¹ (inv_ne_zero hδ.ne'))).mul_right
  refine ⟨P,hb.mul hφ,hPc,?_,?_,hsmall hδ.ne'⟩
  · have hlim : Tendsto (fun x : E => δ⁻¹ • x) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun x : E => δ⁻¹ • x) :=
        ((continuous_const : Continuous (fun _ : E => (δ⁻¹ : ℝ))).smul continuous_id)
      simpa only [smul_zero] using hc.tendsto (0 : E)
    filter_upwards [hlim.eventually b.eventuallyEq_one] with x hx
    simp [P,patch,hx]
  · have hs : tsupport P ⊆ tsupport (fun x : E => b (δ⁻¹ • x)) := by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support,P,patch] at *
      exact fun h => hx (by simp [h])
    intro x hx
    have hh : δ⁻¹ • x ∈ Metric.closedBall (0 : E) 2 := by
      have hm : δ⁻¹ • x ∈ tsupport (b : E → ℝ) :=
        tsupport_comp_subset_preimage (b : E → ℝ)
          (by fun_prop : Continuous (fun y : E => δ⁻¹ • y)) (hs hx)
      simpa [b.tsupport_eq,b] using hm
    have hn : δ⁻¹ * ‖x‖ ≤ 2 := by simpa [norm_smul,abs_of_pos hδ] using hh
    have hn' : ‖x‖ ≤ 2 * δ := by nlinarith [mul_le_mul_of_nonneg_left hn hδ.le,inv_mul_cancel₀ hδ.ne']
    simpa using hn'.trans_lt hδR

end DiagonalExtension.CutoffHessian

namespace DiagonalExtension.CutoffHessian
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hessian_sub_map {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) x =
      fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ g) x := by
  have he : fderiv ℝ (fun y => f y - g y) = fun y => fderiv ℝ f y - fderiv ℝ g y := by
    ext y v
    exact congrArg (fun A : E →L[ℝ] ℝ => A v)
      (fderiv_sub (hf.differentiable (by simp) y) (hg.differentiable (by simp) y))
  rw [he]
  exact fderiv_sub ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)

variable [FiniteDimensional ℝ E]

theorem glue_convex {q ψ : E → ℝ} (hq : ContDiff ℝ ∞ q) (hψ : ContDiff ℝ ∞ ψ)
    (hj0 : ψ 0 = q 0) (hj1 : fderiv ℝ ψ 0 = fderiv ℝ q 0)
    (hj2 : fderiv ℝ (fderiv ℝ ψ) 0 = fderiv ℝ (fderiv ℝ q) 0)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R)
    (hconv : ∀ x v, c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ q) x v) v) :
    ∃ Φ : E → ℝ, ContDiff ℝ ∞ Φ ∧ Φ =ᶠ[𝓝 0] ψ ∧
      (∀ x ∉ Metric.ball 0 R, Φ x = q x) ∧
      HasCompactSupport (fun x => Φ x - q x) ∧
      ∀ x v, (c/2) * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ Φ) x v) v := by
  let φ : E → ℝ := fun x => ψ x - q x
  have hφ : ContDiff ℝ ∞ φ := hψ.sub hq
  have h0 : φ 0 = 0 := by simp [φ,hj0]
  have h1 : fderiv ℝ φ 0 = 0 := by
    have hd : fderiv ℝ φ 0 = fderiv ℝ ψ 0 - fderiv ℝ q 0 :=
      fderiv_sub (hψ.differentiable (by simp) 0) (hq.differentiable (by simp) 0)
    rw [hd,hj1,sub_self]
  have h2 : fderiv ℝ (fderiv ℝ φ) 0 = 0 := by
    rw [show φ = fun x => ψ x - q x from rfl,hessian_sub_map hψ hq,hj2,sub_self]
  obtain ⟨P,hP,hPc,hPe,hPs,hPb⟩ := exists_small_patch hφ h0 h1 h2 (half_pos hc) hR
  let Φ : E → ℝ := fun x => q x + P x
  refine ⟨Φ,hq.add hP,?_,?_,?_,?_⟩
  · filter_upwards [hPe] with x hx
    dsimp [Φ]
    rw [hx]
    dsimp [φ]
    ring
  · intro x hx
    have hp : P x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hPs hh))
    simp [Φ,hp]
  · simpa only [Φ,add_sub_cancel_left] using hPc
  · intro x v
    rw [show Φ = fun y => q y + P y from rfl,hessian_add hq hP]
    have hp := (neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using hPb x v))
    linarith [hconv x v]

end DiagonalExtension.CutoffHessian

open Set Filter
open scoped Topology ContDiff
namespace DiagonalExtension.SmoothExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem extend_local {f : E → ℝ} {U : Set E} {a : E}
    (hU : IsOpen U) (ha : a ∈ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨r,hr,hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let b : ContDiffBump a := ⟨r/2,r,by positivity,by linarith⟩
  let g : E → ℝ := fun x => b x * f x
  have hs : tsupport g ⊆ tsupport b := by
    apply closure_mono
    intro x hx
    simp only [Function.mem_support,g] at *
    exact fun hb => hx (by simp [hb])
  refine ⟨g,?_,b.hasCompactSupport.of_isClosed_subset isClosed_closure hs,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport b
    · have hxU : x ∈ U := hrU (by simpa [b.tsupport_eq,b] using hx)
      exact b.contDiff.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hxU))
    · have he : b =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
      have he' : g =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [he] with y hy
        simp [g,hy]
      exact contDiffAt_const.congr_of_eventuallyEq he'
  · filter_upwards [b.eventuallyEq_one] with x hx
    simp [g,hx]
end DiagonalExtension.SmoothExtension

open Filter
open scoped Topology ContDiff
namespace DiagonalExtension.QuadraticTaylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 def polynomial (a : ℝ) (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) : ℝ :=
  a + ℓ x + (1/2 : ℝ) * B x x

lemma smooth (a : ℝ) (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (polynomial a ℓ B) := by
  unfold polynomial
  fun_prop

lemma derivative (a : ℝ) (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (x : E) :
    HasFDerivAt (polynomial a ℓ B) (ℓ + B x) x := by
  have hq : HasFDerivAt (fun y => (1/2 : ℝ) * B y y) (B x) x := by
    convert! ((B.hasFDerivAt).clm_apply (hasFDerivAt_id x)).const_mul (1/2 : ℝ) using 1
    ext v
    simp [hB x v]
    ring
  exact (ℓ.hasFDerivAt.const_add a).add hq

lemma fderiv_polynomial (a : ℝ) (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) :
    fderiv ℝ (polynomial a ℓ B) = fun x => ℓ + B x := by
  funext x
  exact (derivative a ℓ B hB x).fderiv

lemma hessian_polynomial (a : ℝ) (ℓ : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (x : E) :
    fderiv ℝ (fderiv ℝ (polynomial a ℓ B)) x = B := by
  rw [fderiv_polynomial a ℓ B hB]
  exact (B.hasFDerivAt.const_add ℓ).fderiv

end DiagonalExtension.QuadraticTaylor

open Filter
open scoped Topology ContDiff
namespace DiagonalExtension.ConvexNeighborhood
open CutoffHessian QuadraticTaylor
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def taylor2 (f : E → ℝ) : E → ℝ :=
  polynomial (f 0) (fderiv ℝ f 0) (fderiv ℝ (fderiv ℝ f) 0)

theorem local_convex_extension {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (h0 : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hpos : ∀ v : E, v ≠ 0 → 0 < (fderiv ℝ (fderiv ℝ f) 0 v) v)
    {R : ℝ} (hR : 0 < R) :
    ∃ c : ℝ, 0 < c ∧ ∃ Φ : E → ℝ, ContDiff ℝ ∞ Φ ∧
      Φ =ᶠ[𝓝 0] f ∧ (∀ x ∉ Metric.ball 0 R, Φ x = taylor2 f x) ∧
      HasCompactSupport (fun x => Φ x - taylor2 f x) ∧
      ∀ x v, c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ Φ) x v) v := by
  obtain ⟨g,hg,_,he⟩ := SmoothExtension.extend_local hU h0 hf
  have he0 : g 0 = f 0 := he.eq_of_nhds
  have he1 : fderiv ℝ g 0 = fderiv ℝ f 0 := he.fderiv_eq
  have he2 : fderiv ℝ (fderiv ℝ g) 0 = fderiv ℝ (fderiv ℝ f) 0 :=
    (he.fderiv (𝕜 := ℝ)).fderiv_eq
  have hsym : ∀ v w, (fderiv ℝ (fderiv ℝ g) 0 v) w =
      (fderiv ℝ (fderiv ℝ g) 0 w) v :=
    hg.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨c,hc,hcB⟩ := SmoothLevel.positive_quadratic_lower
    (fderiv ℝ (fderiv ℝ g) 0) (by simpa only [he2] using hpos)
  let q := taylor2 g
  have hq : ContDiff ℝ ∞ q := smooth _ _ _
  have hj0 : g 0 = q 0 := by simp [q,taylor2,polynomial]
  have hj1 : fderiv ℝ g 0 = fderiv ℝ q 0 := by
    dsimp [q,taylor2]
    rw [fderiv_polynomial _ _ _ hsym]
    simp
  have hj2 : fderiv ℝ (fderiv ℝ g) 0 = fderiv ℝ (fderiv ℝ q) 0 :=
    (hessian_polynomial _ _ _ hsym 0).symm
  obtain ⟨Φ,hΦ,hΦe,hΦq,hΦc,hΦb⟩ := glue_convex hq hg hj0 hj1 hj2 hc hR
    (fun x v => by simpa only [q,taylor2,hessian_polynomial _ _ _ hsym] using hcB v)
  have hqeq : q = taylor2 f := by simp only [q,taylor2,he0,he1,he2]
  refine ⟨c/2,half_pos hc,Φ,hΦ,hΦe.trans he,?_,?_,hΦb⟩
  · simpa only [hqeq] using hΦq
  · simpa only [hqeq] using hΦc

end DiagonalExtension.ConvexNeighborhood

end

end OAI
