import OAI.Analysis.LipschitzHilbert.Fourier.FourierKernelFirstMoment

namespace OAI

/-! Uniform derivative bounds for a rescaled multiplier after restriction
to a fixed annulus. These are the bounds needed for its kernel moment. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def localizedMihlinProfile (m rho : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (dilatedSlopeWindow m W hW) rho

@[simp] theorem localizedMihlinProfile_apply (m rho : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) (x : ℝ) :
    localizedMihlinProfile m rho W hW x=m (W*x)*rho x := by
  rw [localizedMihlinProfile,SchwartzMap.smulLeftCLM_apply_apply
    (dilatedSlopeWindow m W hW).hasTemperateGrowth,dilatedSlopeWindow_apply,smul_eq_mul]

def annularDerivativeBudget (rho : SchwartzMap ℝ ℂ) (r : ℕ) : ℝ :=
  ∑ j∈Finset.range (r+1), (r.choose j:ℝ)*2^j*SchwartzMap.seminorm ℝ 0 (r-j) rho

theorem annularDerivativeBudget_nonneg (rho : SchwartzMap ℝ ℂ) (r : ℕ) :
    0≤annularDerivativeBudget rho r :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem dilated_mihlin_derivative_bound (m : SchwartzMap ℝ ℂ) (W A : ℝ)
    (hW : 0<W) (r : ℕ)
    (hm : ∀ y, |y|^r*‖iteratedDeriv r m y‖≤A)
    (x : ℝ) (hx : 1/2≤|x|) :
    ‖iteratedDeriv r (dilatedSlopeWindow m W hW.ne') x‖≤2^r*A := by
  have he : (dilatedSlopeWindow m W hW.ne' : ℝ → ℂ)=fun y => m (W*y) := rfl
  rw [he,iteratedDeriv_comp_const_smul (m.smooth r),norm_smul,
    Real.norm_eq_abs,abs_of_pos (pow_pos hW r)]
  have habs : |W*x|=W*|x| := by rw [abs_mul,abs_of_pos hW]
  have hp : 1≤(2*|x|)^r := one_le_pow₀ (show (1:ℝ)≤2*|x| by linarith)
  calc
    _ ≤ (2*|x|)^r*(W^r*‖iteratedDeriv r m (W*x)‖) :=
      le_mul_of_one_le_left (by positivity) hp
    _ = 2^r*(|W*x|^r*‖iteratedDeriv r m (W*x)‖) := by rw [habs,mul_pow,mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm (W*x)) (by positivity)

theorem localizedMihlinProfile_derivative_bound (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A) (r : ℕ)
    (hm : ∀ j≤r, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|}) (x : ℝ) :
    ‖iteratedDeriv r (localizedMihlinProfile m rho W hW.ne') x‖≤
      A*annularDerivativeBudget rho r := by
  let g := dilatedSlopeWindow m W hW.ne'
  have he : (localizedMihlinProfile m rho W hW.ne' : ℝ → ℂ)=
      (g : ℝ → ℂ)*rho := by
        funext y
        exact localizedMihlinProfile_apply m rho W hW.ne' y
  rw [he,iteratedDeriv_mul (g.smooth r).contDiffAt (rho.smooth r).contDiffAt]
  apply (norm_sum_le _ _).trans
  unfold annularDerivativeBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjr : j≤r := by have := Finset.mem_range.mp hj; omega
  by_cases hz : iteratedDeriv (r-j) rho x=0
  · simp only [hz,mul_zero,norm_zero]
    positivity
  · have hx := hrho (iteratedDeriv_tsupport_subset _ (r-j) (subset_closure hz))
    have hg := dilated_mihlin_derivative_bound m W A hW j (hm j hjr) x hx
    have hb : ‖iteratedDeriv (r-j) rho x‖≤SchwartzMap.seminorm ℝ 0 (r-j) rho := by
      simpa only [pow_zero,one_mul] using rho.le_seminorm' ℝ 0 (r-j) x
    rw [norm_mul,norm_mul,Complex.norm_natCast]
    calc
      _ ≤ (r.choose j:ℝ)*(2^j*A)*SchwartzMap.seminorm ℝ 0 (r-j) rho :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity)) hb
          (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem schwartz_l1_bound_of_support (q : SchwartzMap ℝ ℂ) (B : ℝ) (_hB : 0≤B)
    (hq : tsupport q ⊆ Icc (-2:ℝ) 2) (hb : ∀ x, ‖q x‖≤B) :
    (∫ x, ‖q x‖)≤4*B := by
  have hz : ∀ x, x∉Icc (-2:ℝ) 2 → ‖q x‖=0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hq h)),norm_zero]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    _ ≤ ∫ _x in Icc (-2:ℝ) 2, B := integral_mono q.integrable.norm.integrableOn
      (integrableOn_const measure_Icc_lt_top.ne) (fun x => hb x)
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by norm_num),smul_eq_mul]
      norm_num

theorem schwartzDerivative_l1_bound_of_support (q : SchwartzMap ℝ ℂ) (r : ℕ)
    (B : ℝ) (hB : 0≤B) (hq : tsupport q ⊆ Icc (-2:ℝ) 2)
    (hb : ∀ x, ‖iteratedDeriv r q x‖≤B) :
    (∫ x, ‖schwartzDerivative r q x‖)≤4*B := by
  apply schwartz_l1_bound_of_support _ B hB
  · rw [schwartzDerivative_apply]
    exact (iteratedDeriv_tsupport_subset q r).trans hq
  · simpa only [schwartzDerivative_apply] using hb

theorem localizedMihlinProfile_tsupport (m rho : SchwartzMap ℝ ℂ)
    (W : ℝ) (hW : W≠0) :
    tsupport (localizedMihlinProfile m rho W hW) ⊆ tsupport rho := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  apply subset_closure
  intro hz
  exact hx (by rw [localizedMihlinProfile_apply,hz,mul_zero])

theorem localizedMihlinProfile_l1 (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A) (r : ℕ)
    (hm : ∀ j≤r, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|})
    (hsupp : tsupport rho ⊆ Icc (-2:ℝ) 2) :
    (∫ x, ‖schwartzDerivative r (localizedMihlinProfile m rho W hW.ne') x‖)≤
      4*(A*annularDerivativeBudget rho r) := by
  apply schwartzDerivative_l1_bound_of_support
  · exact mul_nonneg hA (annularDerivativeBudget_nonneg rho r)
  · exact (localizedMihlinProfile_tsupport m rho W hW.ne').trans hsupp
  · exact localizedMihlinProfile_derivative_bound m rho W A hW hA r hm hrho

def localizedKernelFirstMomentConstant (rho : SchwartzMap ℝ ℂ) : ℝ :=
  8*Real.pi*(annularDerivativeBudget rho 0+
    annularDerivativeBudget rho 3/(2*Real.pi)^3)

theorem localizedKernelFirstMomentConstant_nonneg (rho : SchwartzMap ℝ ℂ) :
    0≤localizedKernelFirstMomentConstant rho := by
  unfold localizedKernelFirstMomentConstant
  have h0 := annularDerivativeBudget_nonneg rho 0
  have h3 := annularDerivativeBudget_nonneg rho 3
  positivity

theorem localizedMihlinProfile_fourier_firstMoment (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A)
    (hm : ∀ j≤3, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|})
    (hsupp : tsupport rho ⊆ Icc (-2:ℝ) 2) :
    (∫ x, |x| *‖(𝓕 (localizedMihlinProfile m rho W hW.ne')) x‖)≤
      A*localizedKernelFirstMomentConstant rho := by
  let q := localizedMihlinProfile m rho W hW.ne'
  have h0 := localizedMihlinProfile_l1 m rho W A hW hA 0
    (fun j hj => hm j (by omega)) hrho hsupp
  have h3 := localizedMihlinProfile_l1 m rho W A hW hA 3 hm hrho hsupp
  have h := schwartz_fourier_firstMoment_bound q
  change (∫ x, ‖q x‖)≤_ at h0
  apply h.trans
  have hp : 0<(2*Real.pi)^3 := by positivity
  have hd := div_le_div_of_nonneg_right h3 hp.le
  have hm' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add h0 hd)
    (by norm_num : (0:ℝ)≤2)) Real.pi_pos.le
  unfold localizedKernelFirstMomentConstant
  convert hm' using 1; ring

theorem schwartz_fourierInv_firstMoment_eq (q : SchwartzMap ℝ ℂ) :
    (∫ x, |x| *‖(𝓕⁻ q) x‖)=(∫ x, |x| *‖(𝓕 q) x‖) := by
  have he : (fun x : ℝ => |x| *‖(𝓕⁻ q) x‖)=
      fun x => |-x| *‖(𝓕 q) (-x)‖ := by
    funext x
    rw [abs_neg]
    rfl
  rw [he]
  calc
    _ = ∫ x : ℝ, |(-1:ℝ)*x| *‖(𝓕 q) ((-1:ℝ)*x)‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (-1:ℝ)*x= -x by ring]
    _ = _ := by
      simpa only [inv_neg,inv_one,abs_neg,abs_one,one_smul] using
        Measure.integral_comp_mul_left (fun x : ℝ => |x| *‖(𝓕 q) x‖) (-1)

theorem localizedMihlinProfile_kernel_firstMoment (m rho : SchwartzMap ℝ ℂ)
    (W A : ℝ) (hW : 0<W) (hA : 0≤A)
    (hm : ∀ j≤3, ∀ y, |y|^j*‖iteratedDeriv j m y‖≤A)
    (hrho : tsupport rho ⊆ {x : ℝ | 1/2≤|x|})
    (hsupp : tsupport rho ⊆ Icc (-2:ℝ) 2) :
    (∫ x, |x| *‖(𝓕⁻ (localizedMihlinProfile m rho W hW.ne')) x‖)≤
      A*localizedKernelFirstMomentConstant rho := by
  rw [schwartz_fourierInv_firstMoment_eq]
  exact localizedMihlinProfile_fourier_firstMoment m rho W A hW hA hm hrho hsupp

end LipschitzHilbert.PacketRepresentation

end

end OAI
