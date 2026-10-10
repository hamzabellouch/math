import OAI.Geometry.Perimeter.Regularity.SmulMemPhaseSupport

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

def harmonicKernelRaw (x : Euc n) : ℝ := densityProfile 1 (‖x‖^2)
def harmonicKernelMass (n : ℕ) : ℝ := ∫ x : Euc n, harmonicKernelRaw x

theorem harmonicKernelRaw_contDiff : ContDiff ℝ ∞ (harmonicKernelRaw (n := n)) :=
  (densityProfile_contDiff 1).comp (contDiff_id.norm_sq (𝕜 := ℝ))

theorem harmonicKernelRaw_tsupport : tsupport (harmonicKernelRaw (n := n)) ⊆
    Metric.closedBall 0 1 := by
  have h := radialProfile_tsupport (0:Euc n) (fun s hs ↦ densityProfile_zero 1 hs) zero_lt_one
  change tsupport (fun x : Euc n ↦ densityProfile 1 (‖x‖^2)) ⊆ _
  simpa only [one_pow,one_mul,sub_zero,div_one] using h

theorem harmonicKernelRaw_compact : HasCompactSupport (harmonicKernelRaw (n := n)) :=
  (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport _) harmonicKernelRaw_tsupport

theorem harmonicKernelMass_pos (n : ℕ) : 0 < harmonicKernelMass n := by
  apply harmonicKernelRaw_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    harmonicKernelRaw_compact (fun x ↦ (densityProfile_mem_Icc 1 _).1) (x := 0)
  simp only [harmonicKernelRaw,norm_zero,zero_pow (by decide : 2 ≠ 0),densityProfile]
  norm_num [Real.smoothTransition.one_of_one_le]

def harmonicKernel (x : Euc n) : ℝ := harmonicKernelRaw x / harmonicKernelMass n

theorem harmonicKernel_contDiff : ContDiff ℝ ∞ (harmonicKernel (n := n)) :=
  harmonicKernelRaw_contDiff.div_const _

theorem harmonicKernel_tsupport : tsupport (harmonicKernel (n := n)) ⊆ Metric.closedBall 0 1 :=
  by
    change tsupport (fun x : Euc n ↦ harmonicKernelRaw x / harmonicKernelMass n) ⊆ _
    simp only [div_eq_mul_inv]
    exact tsupport_mul_subset_left.trans harmonicKernelRaw_tsupport

theorem harmonicKernel_compact : HasCompactSupport (harmonicKernel (n := n)) :=
  (isCompact_closedBall 0 1).of_isClosed_subset (isClosed_tsupport _) harmonicKernel_tsupport

theorem harmonicKernel_integral : (∫ x : Euc n, harmonicKernel x) = 1 := by
  simp only [harmonicKernel,integral_div]
  exact div_self (harmonicKernelMass_pos n).ne'

def scaledHarmonicKernel (t : ℝ) (x : Euc n) : ℝ := t^n*harmonicKernel (t•x)

theorem scaledHarmonicKernel_contDiff (t : ℝ) :
    ContDiff ℝ ∞ (scaledHarmonicKernel (n := n) t) :=
  contDiff_const.mul (harmonicKernel_contDiff.comp (contDiff_id.const_smul t))

theorem scaledHarmonicKernel_eq {t : ℝ} (ht : 0 < t) (x : Euc n) :
    scaledHarmonicKernel t x = t^n*densityProfile 1 (t^2*‖x‖^2)/harmonicKernelMass n := by
  simp only [scaledHarmonicKernel,harmonicKernel,harmonicKernelRaw,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht,mul_pow]
  ring

theorem scaledHarmonicKernel_integral {t : ℝ} (ht : 0 < t) :
    (∫ x : Euc n, scaledHarmonicKernel t x) = 1 := by
  change (∫ x : Euc n, t^n*harmonicKernel (t•x)) = 1
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euc n))
    harmonicKernel t (hR := ht.le)
  simp only [finrank_euclideanSpace,Fintype.card_fin,smul_eq_mul,harmonicKernel_integral] at h
  rw [h]
  simp [ht.ne']

theorem scaledHarmonicKernel_tsupport {t : ℝ} (ht : 0 < t) :
    tsupport (scaledHarmonicKernel (n := n) t) ⊆ Metric.closedBall 0 (1/t) := by
  have he : scaledHarmonicKernel (n := n) t = fun x ↦
      (t^n/harmonicKernelMass n)*densityProfile 1 (t^2*‖x-0‖^2) := by
    funext x
    rw [scaledHarmonicKernel_eq ht,sub_zero]; ring
  rw [he]
  exact tsupport_mul_subset_right.trans
    (radialProfile_tsupport 0 (fun s hs ↦ densityProfile_zero 1 hs) ht)

theorem scaledHarmonicKernel_bound {t : ℝ} (ht : 0 < t) (x : Euc n) :
    |scaledHarmonicKernel t x| ≤ t^n/harmonicKernelMass n := by
  rw [scaledHarmonicKernel_eq ht,abs_div,abs_of_pos (harmonicKernelMass_pos n),
    abs_mul,abs_of_pos (pow_pos ht _),abs_of_nonneg (densityProfile_mem_Icc 1 _).1]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_right (pow_nonneg ht.le _) (densityProfile_mem_Icc 1 _).2)
    (harmonicKernelMass_pos n).le

theorem shifted_scaledHarmonicKernel_integral {t : ℝ} (ht : 0 < t) (c : Euc n) :
    (∫ x, scaledHarmonicKernel t (c-x)) = 1 := by
  rw [integral_sub_left_eq_self]
  exact scaledHarmonicKernel_integral ht

theorem shifted_scaledHarmonicKernel_support {t : ℝ} (ht : 0 < t) (c : Euc n) :
    Function.support (fun x ↦ scaledHarmonicKernel t (c-x)) ⊆ Metric.closedBall c (1/t) := by
  intro x hx
  have h := scaledHarmonicKernel_tsupport ht (subset_tsupport _ hx)
  simpa only [Metric.mem_closedBall,dist_zero_right,dist_eq_norm,sub_zero,norm_sub_rev] using h

end RPISingularHarnack

end

end OAI
