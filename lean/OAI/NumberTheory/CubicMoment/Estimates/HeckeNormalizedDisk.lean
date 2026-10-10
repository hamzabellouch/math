import OAI.NumberTheory.CubicMoment.Estimates.HeckeUniformGrowth
import OAI.NumberTheory.CubicMoment.Estimates.IdealLogDerivativeTwist

namespace OAI

/-! Normalize a complete Hecke function at 2+it on a disk of radius 3.
The resulting bound is explicit in the finite and archimedean conductor. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

def normalizedHeckeDisk (L : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  L (2+(t:ℂ)*Complex.I+3*z)/L (2+(t:ℂ)*Complex.I)

def normalizedHeckeDiskBound (A k : ℝ) (ε : ℂ) (t : ℝ) : ℝ :=
  2+idealZetaTwo*heckeZeroFreeMajorant A k ε*(4+|t|)^4

lemma normalizedHeckeDiskBound_gt_one (A k : ℝ) (ε : ℂ) (t : ℝ) :
    1 < normalizedHeckeDiskBound A k ε t := by
  have h1 := idealZetaTwo_pos
  have h2 := heckeZeroFreeMajorant_pos A k ε
  unfold normalizedHeckeDiskBound
  have hp : 0 ≤ idealZetaTwo*heckeZeroFreeMajorant A k ε*(4+|t|)^4 := by positivity
  linarith

lemma normalizedHeckeDisk_differentiable {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) (t : ℝ) : Differentiable ℂ (normalizedHeckeDisk L t) := by
  unfold normalizedHeckeDisk
  fun_prop

lemma normalizedHeckeDisk_zero {L : ℂ → ℂ} (t : ℝ)
    (hL0 : L (2+(t:ℂ)*Complex.I) ≠ 0) : normalizedHeckeDisk L t 0=1 := by
  simp [normalizedHeckeDisk,hL0]

lemma normalizedHeckeDisk_logDeriv {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) (t : ℝ) (z : ℂ)
    (hL0 : L (2+(t:ℂ)*Complex.I) ≠ 0) :
    logDeriv (normalizedHeckeDisk L t) z=
      3*logDeriv L (2+(t:ℂ)*Complex.I+3*z) := by
  change logDeriv (fun w : ℂ => L (2+(t:ℂ)*Complex.I+3*w)*
    (L (2+(t:ℂ)*Complex.I))⁻¹) z= _
  rw [logDeriv_mul_const z _ (inv_ne_zero hL0)]
  have h := logDeriv_fun_comp (f := L) (g := fun w : ℂ => 2+(t:ℂ)*Complex.I+3*w)
    (hL (2+(t:ℂ)*Complex.I+3*z))
    (show DifferentiableAt ℂ (fun w : ℂ => 2+(t:ℂ)*Complex.I+3*w) z by fun_prop)
  have hd : deriv (fun w : ℂ => 2+(t:ℂ)*Complex.I+3*w) z=3 := by
    simpa only [Pi.add_apply,id_eq,zero_add,mul_one] using!
      ((hasDerivAt_const z (2+(t:ℂ)*Complex.I)).add ((hasDerivAt_id z).const_mul (3:ℂ))).deriv
  rw [hd] at h
  simpa only [mul_comm] using h

theorem normalizedHeckeDisk_bound
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) (t : ℝ) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖normalizedHeckeDisk L t z‖ ≤ normalizedHeckeDiskBound A k ε t := by
  have hK := heckeZeroFreeMajorant_pos A k ε
  have hc : (2+(t:ℂ)*Complex.I).re=2 := by simp
  have hinv : ‖(L (2+(t:ℂ)*Complex.I))⁻¹‖ ≤ idealZetaTwo := by
    rw [hs _ (by rw [hc]; norm_num)]
    exact idealDirichlet_reciprocal_bound χ hχ hχ0 hχadd hc.ge
  intro z hz
  have hr : -(3/2:ℝ) ≤ (2+(t:ℂ)*Complex.I+3*z).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm z)).1
    have he : (2+(t:ℂ)*Complex.I+3*z).re=2+3*z.re := by simp
    rw [he]
    linarith
  have hi : |(2+(t:ℂ)*Complex.I+3*z).im| ≤ |t|+3 := by
    have h := Complex.abs_im_le_norm z
    have hh := abs_add_le t (3*z.im)
    have he : (2+(t:ℂ)*Complex.I+3*z).im=t+3*z.im := by simp
    rw [he]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at hh
    linarith
  have hl := shifted_hecke_uniform_strip hχ hχdual hA hk hL hs hds hFE hcomp _ hr
  have hp : (1+|(2+(t:ℂ)*Complex.I+3*z).im|)^4 ≤ (4+|t|)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hfinal := mul_le_mul
    (hl.trans (mul_le_mul_of_nonneg_left hp (heckeZeroFreeMajorant_pos A k ε).le))
    hinv (_root_.norm_nonneg _) (by positivity)
  rw [normalizedHeckeDisk,div_eq_mul_inv,norm_mul]
  exact hfinal.trans (by unfold normalizedHeckeDiskBound; nlinarith)

end CubicFirstMoment

end

end OAI
