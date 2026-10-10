import OAI.Analysis.LiebThirring.CutoffEnergy

namespace OAI


noncomputable section
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff

/-- A locally integrable function whose distributional derivative vanishes is constant.
This uses only smooth compact tests, hence applies to the H¹ definition. -/
lemma ae_const_of_weak_derivative_zero {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = 0) : ∃ c : ℝ, f =ᵐ[volume] fun _ ↦ c := by
  have hc (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
      ∀ x y : ℝ, (ρ ⋆[lsmul ℝ ℝ, volume] f) x = (ρ ⋆[lsmul ℝ ℝ, volume] f) y := by
    have hder (x : ℝ) : HasDerivAt (ρ ⋆[lsmul ℝ ℝ, volume] f) 0 x := by
      have hd := hρc.hasDerivAt_convolution_left (lsmul ℝ ℝ) (hρ.of_le (by simp)) hf x
      have ht := hw (fun y ↦ ρ (x-y)) (hρ.comp (contDiff_const.sub contDiff_id))
        (hρc.comp_homeomorph (Homeomorph.subLeft x))
      have hdφ (y : ℝ) : deriv (fun y ↦ ρ (x-y)) y = -deriv ρ (x-y) := by
        simpa only [Function.comp_def, zero_sub, mul_neg, mul_one] using
          ((hρ.differentiable (by simp) (x-y)).hasDerivAt.comp y
            ((hasDerivAt_const y x).sub (hasDerivAt_id y))).deriv
      simp_rw [hdφ,mul_neg,integral_neg] at ht
      have hz : ((deriv ρ ⋆[lsmul ℝ ℝ, volume] f) x) = 0 := by
        rw [convolution_eq_swap]
        simpa only [lsmul_apply,smul_eq_mul,mul_comm,neg_eq_zero] using ht
      rwa [hz] at hd
    exact is_const_of_deriv_eq_zero (fun x ↦ (hder x).differentiableAt)
      (fun x ↦ (hder x).deriv)
  let b : ℕ → ContDiffBump (0 : ℝ) := fun n ↦
    ⟨(n+1 : ℝ)⁻¹,2*(n+1 : ℝ)⁻¹,by positivity,by nlinarith [inv_pos.mpr (show (0 : ℝ)<n+1 by positivity)]⟩
  have hb : Tendsto (fun n ↦ (b n).rOut) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ ↦ (n+1 : ℝ)⁻¹) atTop (𝓝 0) :=
      by simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero] using ht.const_mul 2
  have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := b) hb (K := 2) (Eventually.of_forall (fun _ ↦ le_refl _)) hf
  obtain ⟨x₀,hx₀⟩ := ha.exists
  refine ⟨f x₀,?_⟩
  filter_upwards [ha] with x hx
  apply tendsto_nhds_unique hx
  convert hx₀ using 1
  funext n
  exact hc ((b n).normed volume) (b n).contDiff_normed (b n).hasCompactSupport_normed x x₀


lemma primitive_weak_derivative {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, (∫ t in (0 : ℝ)..x, g t) * deriv φ x) = -(∫ x, g x * φ x) := by
  obtain ⟨R,hR,hRs⟩ := hφc.isBounded.subset_ball_lt 0 (0 : ℝ)
  have hs : tsupport φ ⊆ Ioo (-R) R := by
    intro x hx
    have hh := hRs hx
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt,mem_Ioo] using hh
  have hzero : φ (-R) = 0 ∧ φ R = 0 := by
    constructor <;> apply image_eq_zero_of_notMem_tsupport <;>
      intro h <;> have := hs h <;> simp_all
  let F := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hgi := locallyIntegrable_intervalIntegrable hg (-R) R
  have h0 : (0 : ℝ) ∈ uIcc (-R) R := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  have hF : AbsolutelyContinuousOnInterval F (-R) R :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral h0
  have hφa : AbsolutelyContinuousOnInterval φ (-R) R :=
    (hφ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hfd : ∀ᵐ x, x ∈ uIcc (-R) R → deriv F x = g x := by
    filter_upwards [hgi.ae_hasDerivAt_integral] with x hx hmem
    exact (hx hmem 0 h0).deriv
  have he := hF.integral_mul_deriv_eq_deriv_mul hφa
  rw [hzero.1,hzero.2,mul_zero,mul_zero,sub_self,zero_sub] at he
  have hi : (∫ x in (-R)..R, deriv F x * φ x) = ∫ x in (-R)..R, g x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfd] with x hx hmem
    rw [hx (uIoc_subset_uIcc hmem)]
  rw [hi] at he
  have hleft : Function.support (fun x ↦ F x * deriv φ x) ⊆ Ioc (-R) R := by
    intro x hx
    have hd : x ∈ tsupport (deriv φ) :=
      subset_tsupport _ (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)
    exact Ioo_subset_Ioc_self (hs (tsupport_deriv_subset hd))
  have hright : Function.support (fun x ↦ g x * φ x) ⊆ Ioc (-R) R := by
    intro x hx
    exact Ioo_subset_Ioc_self (hs (subset_tsupport _ (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)))
  rwa [intervalIntegral.integral_eq_integral_of_support_subset hleft,
    intervalIntegral.integral_eq_integral_of_support_subset hright] at he

/-- The precise one-dimensional Sobolev representative, obtained from the weak derivative
without assuming any pointwise regularity or adding a representative to the domain. -/
lemma weak_derivative_representation {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x * deriv φ x) = -(∫ x, g x * φ x)) :
    ∃ c : ℝ, f =ᵐ[volume] fun x ↦ c + ∫ t in (0 : ℝ)..x, g t := by
  let F := fun x ↦ ∫ t in (0 : ℝ)..x, g t
  have hFc : Continuous F := intervalIntegral.continuous_primitive (locallyIntegrable_intervalIntegrable hg) 0
  obtain ⟨c,hc⟩ := ae_const_of_weak_derivative_zero (hf.sub hFc.locallyIntegrable) (fun φ hφ hφc ↦ by
    have hi₁ : Integrable (fun x ↦ f x * deriv φ x) volume :=
      hf.integrable_smul_right_of_hasCompactSupport (hφ.continuous_deriv (by simp)) hφc.deriv
    have hi₂ : Integrable (fun x ↦ F x * deriv φ x) volume :=
      hFc.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (hφ.continuous_deriv (by simp)) hφc.deriv
    simp only [Pi.sub_apply,sub_mul,integral_sub hi₁ hi₂,hw φ hφ hφc]
    change -(∫ x, g x * φ x) - (∫ x, (∫ t in (0 : ℝ)..x, g t) * deriv φ x) = 0
    rw [primitive_weak_derivative hg φ hφ hφc,sub_self])
  refine ⟨c,?_⟩
  filter_upwards [hc] with x hx
  exact sub_eq_iff_eq_add.mp hx

end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

lemma h1_project_weak (u : H1) (L : ℂ →L[ℝ] ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, L (u.val x) * deriv φ x) = -(∫ x, L (u.grad x) * φ x) := by
  have hp : ContDiff ℝ ∞ (fun x ↦ (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have hpc : HasCompactSupport (fun x ↦ (φ x : ℂ)) := hφc.comp_left Complex.ofReal_zero
  have hd (x : ℝ) : deriv (fun x ↦ (φ x : ℂ)) x = ((deriv φ x : ℝ) : ℂ) :=
    ((hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  have hi₁ : Integrable (fun x ↦ u.val x * ((deriv φ x : ℝ) : ℂ)) :=
    (u.val_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      (Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp)))
      (hφc.deriv.comp_left Complex.ofReal_zero)
  have hi₂ : Integrable (fun x ↦ u.grad x * (φ x : ℂ)) :=
    (u.grad_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hp.continuous hpc
  have he := congrArg L (u.weak_derivative _ hp hpc)
  simp only [hd,map_neg,← L.integral_comp_comm hi₁,← L.integral_comp_comm hi₂] at he
  have hm (z : ℂ) (a : ℝ) : L (z*(a : ℂ)) = L z*a := by
    rw [mul_comm,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
  simpa only [hm] using he

lemma h1_continuous_representative (u : H1) :
    ∃ f : ℝ → ℂ, Continuous f ∧ u.val =ᵐ[volume] f := by
  have hr := weak_derivative_representation
    ((Complex.reCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.reCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (h1_project_weak u Complex.reCLM)
  have hi := weak_derivative_representation
    ((Complex.imCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.imCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (h1_project_weak u Complex.imCLM)
  obtain ⟨cr,hr⟩ := hr
  obtain ⟨ci,hi⟩ := hi
  let fr := fun x ↦ cr + ∫ t in (0 : ℝ)..x, (u.grad t).re
  let fi := fun x ↦ ci + ∫ t in (0 : ℝ)..x, (u.grad t).im
  have hfr : Continuous fr := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable ((Complex.reCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))) 0)
  have hfi : Continuous fi := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable ((Complex.imCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))) 0)
  refine ⟨fun x ↦ (fr x : ℂ)+(fi x : ℂ)*Complex.I,
    (Complex.continuous_ofReal.comp hfr).add ((Complex.continuous_ofReal.comp hfi).mul continuous_const),?_⟩
  filter_upwards [hr,hi] with x hx hy
  apply Complex.ext
  · simpa [fr,fi] using (show (u.val x).re = fr x from hx)
  · simpa [fr,fi] using (show (u.val x).im = fi x from hy)

/-- Classical representative of a real weak second-order eigenfunction. -/
structure RealEigenfunction (W : ℝ → ℝ) (k : ℝ) where
  val : ℝ → ℝ
  grad : ℝ → ℝ
  val_memLp : MemLp val 2 volume
  grad_memLp : MemLp grad 2 volume
  grad_continuous : Continuous grad
  hasDerivAt : ∀ x, HasDerivAt val (grad x) x
  grad_ac : ∀ a b, AbsolutelyContinuousOnInterval grad a b
  grad_deriv : ∀ᵐ x, deriv grad x = (k^2-W x)*val x

lemma real_eigen_of_weak {W f g : ℝ → ℝ} {k : ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hW : LocallyIntegrable W volume)
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, f x*deriv φ x) = -(∫ x, g x*φ x))
    (hwe : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, g x*deriv φ x) = -(∫ x, (k^2-W x)*f x*φ x)) :
    ∃ u : RealEigenfunction W k, f =ᵐ[volume] u.val ∧ g =ᵐ[volume] u.grad := by
  obtain ⟨c,hc⟩ := weak_derivative_representation (hf.locallyIntegrable (by norm_num))
    (hg.locallyIntegrable (by norm_num)) hw
  let F := fun x ↦ c+∫ t in (0 : ℝ)..x, g t
  have hFc : Continuous F := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable (hg.locallyIntegrable (by norm_num))) 0)
  let J := fun x ↦ (k^2-W x)*F x
  have hJ : LocallyIntegrable J volume := ((locallyIntegrable_const (c := k^2)).sub hW).mul_continuous hFc
  obtain ⟨d,hd⟩ := weak_derivative_representation (hg.locallyIntegrable (by norm_num)) hJ (fun φ hφ hφc ↦ by
    rw [hwe φ hφ hφc]; congr 1
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    rw [hx])
  let G := fun x ↦ d+∫ t in (0 : ℝ)..x, J t
  have hGc : Continuous G := continuous_const.add (intervalIntegral.continuous_primitive
    (locallyIntegrable_intervalIntegrable hJ) 0)
  have hFG (x : ℝ) : F x = c+∫ t in (0 : ℝ)..x, G t := by
    change c+(∫ t in (0 : ℝ)..x, g t) = c+∫ t in (0 : ℝ)..x, G t
    congr 1
    exact intervalIntegral.integral_congr_ae (hd.mono fun _ hx _ ↦ hx)
  have hFd (x : ℝ) : HasDerivAt F (G x) x := by
    simp_rw [show F = fun x ↦ c+∫ t in (0 : ℝ)..x, G t from funext hFG]
    exact (intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable _ _) (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt).const_add c
  have hGa (a b : ℝ) : AbsolutelyContinuousOnInterval G a b := by
    have hi := locallyIntegrable_intervalIntegrable hJ (min 0 (min a b)) (max 0 (max a b))
    have h0 : (0 : ℝ) ∈ uIcc (min 0 (min a b)) (max 0 (max a b)) := by
      rw [uIcc_of_le (by exact (min_le_left _ _).trans (le_max_left _ _))]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    have h := hi.absolutelyContinuousOnInterval_intervalIntegral h0
    exact (((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ d)).contDiffOn.absolutelyContinuousOnInterval).add h).mono (by
      intro x hx
      rw [uIcc_of_le (by exact (min_le_left _ _).trans (le_max_left _ _))]
      exact ⟨(min_le_right _ _).trans hx.1,hx.2.trans (le_max_right _ _)⟩)
  have hGd : ∀ᵐ x, deriv G x = J x := by
    have hi : LocallyIntegrable J volume := hJ
    have hd' := LocallyIntegrable.ae_hasDerivAt_integral hi
    filter_upwards [hd'] with x hx
    exact ((hx 0).const_add d).deriv
  exact ⟨⟨F,G,hf.ae_eq hc,hg.ae_eq hd,hGc,hFd,hGa,hGd⟩,hc,hd⟩

end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

lemma clm_mul_real (L : ℂ →L[ℝ] ℝ) (z : ℂ) (a : ℝ) : L (z*(a : ℂ)) = L z*a := by
  rw [mul_comm,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]

lemma integrable_h1_test (u : H1) (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) : Integrable (fun x ↦ u.val x*(φ x : ℂ)) :=
  (u.val_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
    (Complex.continuous_ofReal.comp hφ) (hφc.comp_left Complex.ofReal_zero)

lemma integrable_potential_h1_test (u : H1) {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ (W x : ℂ)*u.val x*(φ x : ℂ)) := by
  obtain ⟨F,hF,hFe⟩ := h1_continuous_representative u
  have h := hW.integrable_smul_right_of_hasCompactSupport
    (hF.mul (Complex.continuous_ofReal.comp hφ))
    ((hφc.comp_left Complex.ofReal_zero).mul_left (f := F))
  apply h.congr
  filter_upwards [hFe] with x hx
  simp only [Complex.real_smul,hx,mul_assoc,Pi.mul_apply,Function.comp_apply]

lemma eigen_weak_second {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, u.grad x*((deriv φ x : ℝ) : ℂ)) =
      -(∫ x, ((k^2-W x : ℝ) : ℂ)*u.val x*(φ x : ℂ)) := by
  have hφd : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  let v := smoothH1 (fun x ↦ (φ x : ℂ)) (fun x ↦ ((deriv φ x : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (fun x ↦ (hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp)
    (Complex.continuous_ofReal.comp hφd)
    ((hφ.continuous.memLp_of_hasCompactSupport hφc).ofReal)
    ((hφd.memLp_of_hasCompactSupport hφc.deriv).ofReal)
  have he := hu.2 v
  change (∫ x, star (((deriv φ x : ℝ) : ℂ))*u.grad x) -
    (∫ x, (W x : ℂ)*star (φ x : ℂ)*u.val x) =
    -(k^2 : ℝ)*(∫ x, star (φ x : ℂ)*u.val x) at he
  simp only [Complex.star_def,Complex.conj_ofReal] at he
  have hi := (integrable_h1_test u φ hφ.continuous hφc).const_mul ((k^2 : ℝ) : ℂ)
  have hwi := integrable_potential_h1_test u hW φ hφ.continuous hφc
  have hid : Integrable (fun x ↦ ((k^2 : ℝ) : ℂ)*u.val x*(φ x : ℂ)) := by
    simpa only [mul_assoc] using hi
  simp_rw [Complex.ofReal_sub,sub_mul]
  rw [integral_sub hid hwi]
  simp_rw [mul_assoc] at he ⊢
  rw [integral_const_mul]
  simp_rw [mul_comm (u.grad _),mul_comm (u.val _)]
  simpa only [neg_sub,sub_eq_add_neg,neg_mul,neg_add_rev,neg_neg,add_comm] using (sub_eq_iff_eq_add.mp he)

lemma eigen_project_weak_second {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (L : ℂ →L[ℝ] ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, L (u.grad x)*deriv φ x) = -(∫ x, (k^2-W x)*L (u.val x)*φ x) := by
  have hi : Integrable (fun x ↦ u.grad x*((deriv φ x : ℝ) : ℂ)) :=
    (u.grad_memLp.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      (Complex.continuous_ofReal.comp (hφ.continuous_deriv (by simp)))
      (hφc.deriv.comp_left Complex.ofReal_zero)
  have hj := integrable_potential_h1_test u ((locallyIntegrable_const (c := k^2)).sub hW)
    φ hφ.continuous hφc
  change Integrable (fun x ↦ ((k^2-W x : ℝ) : ℂ)*u.val x*(φ x : ℂ)) at hj
  have he := congrArg L (eigen_weak_second hW hu φ hφ hφc)
  rw [map_neg,← L.integral_comp_comm hi,← L.integral_comp_comm hj] at he
  have hm (z : ℂ) (a : ℝ) : L ((a : ℂ)*z) = a*L z := by
    rw [mul_comm,clm_mul_real,mul_comm]
  simpa only [clm_mul_real,hm] using he

lemma eigen_project_representative {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ v : RealEigenfunction W k,
      (fun x ↦ L (u.val x)) =ᵐ[volume] v.val ∧
      (fun x ↦ L (u.grad x)) =ᵐ[volume] v.grad :=
  real_eigen_of_weak (L.comp_memLp' u.val_memLp) (L.comp_memLp' u.grad_memLp) hW
    (h1_project_weak u L) (eigen_project_weak_second hW hu L)

end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set

def RealEigenfunction.toC1L2 {W : ℝ → ℝ} {k : ℝ} (u : RealEigenfunction W k) : C1L2 :=
  ⟨(u.val,u.grad),u.val_memLp,u.grad_memLp,u.grad_continuous,u.hasDerivAt⟩

lemma RealEigenfunction.toC1L2_eigen {W : ℝ → ℝ} {k : ℝ} (u : RealEigenfunction W k) :
    u.toC1L2.IsEigen W k := by
  intro a b
  change u.grad b-u.grad a = ∫ x in a..b, (k^2-W x)*u.val x
  rw [← (u.grad_ac a b).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [u.grad_deriv] with x hx _
  exact hx

lemma eigen_C1_representative {W : ℝ → ℝ} {k : ℝ} {u : H1}
    (hW : LocallyIntegrable W volume) (hu : IsNegativeEigenfunction W k u)
    (L : ℂ →L[ℝ] ℝ) :
    ∃ v : C1L2, v.IsEigen W k ∧ (fun x ↦ L (u.val x)) =ᵐ[volume] v.val := by
  obtain ⟨v,hv,_⟩ := eigen_project_representative hW hu L
  exact ⟨v.toC1L2,v.toC1L2_eigen,hv⟩

lemma re_l2Pairing {u v : H1} {ur ui vr vi : C1L2}
    (hur : (fun x ↦ (u.val x).re) =ᵐ[volume] ur.val)
    (hui : (fun x ↦ (u.val x).im) =ᵐ[volume] ui.val)
    (hvr : (fun x ↦ (v.val x).re) =ᵐ[volume] vr.val)
    (hvi : (fun x ↦ (v.val x).im) =ᵐ[volume] vi.val) :
    (l2Pairing u v).re = inner ℝ ur vr+inner ℝ ui vi := by
  have hint : Integrable (fun x ↦ star (u.val x)*v.val x) :=
    u.val_memLp.star.integrable_mul v.val_memLp
  have hreal := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hreal
  rw [l2Pairing,← hreal,C1L2.inner_eq_integral,C1L2.inner_eq_integral,
    ← integral_add (ur.integrable_val_mul vr) (ui.integrable_val_mul vi)]
  apply integral_congr_ae
  filter_upwards [hur,hui,hvr,hvi] with x h1 h2 h3 h4
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,h1,h2,h3,h4]
  ring

lemma im_l2Pairing {u v : H1} {ur ui vr vi : C1L2}
    (hur : (fun x ↦ (u.val x).re) =ᵐ[volume] ur.val)
    (hui : (fun x ↦ (u.val x).im) =ᵐ[volume] ui.val)
    (hvr : (fun x ↦ (v.val x).re) =ᵐ[volume] vr.val)
    (hvi : (fun x ↦ (v.val x).im) =ᵐ[volume] vi.val) :
    (l2Pairing u v).im = inner ℝ ur vi-inner ℝ ui vr := by
  have hint : Integrable (fun x ↦ star (u.val x)*v.val x) :=
    u.val_memLp.star.integrable_mul v.val_memLp
  have himag := Complex.imCLM.integral_comp_comm hint
  simp only [Complex.imCLM_apply] at himag
  rw [l2Pairing,← himag,C1L2.inner_eq_integral,C1L2.inner_eq_integral,
    ← integral_sub (ur.integrable_val_mul vi) (ui.integrable_val_mul vr)]
  apply integral_congr_ae
  filter_upwards [hur,hui,hvr,hvi] with x h1 h2 h3 h4
  simp only [Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,h1,h2,h3,h4]
  ring

end SharpLiebThirring.SobolevProof

end

end OAI
