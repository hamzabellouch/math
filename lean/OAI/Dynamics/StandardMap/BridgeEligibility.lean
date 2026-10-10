import OAI.Dynamics.StandardMap.BridgeKernel

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma PlaneAreaPreserving.eligible_row {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (s : ℂ) (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4) (hstable : ‖A s‖=‖A‖⁻¹) :
    ‖A‖/3 ≤ |(A 1).re| ∨ ‖A‖/3 ≤ |(A 1).im| := by
  have him := vertical_im_lower s hu hs
  have hD : 0 < ‖A‖ := by obtain ⟨a,ha,hb,hc,hd,he⟩:=hA.singular_pair; linarith
  have hw := abs_wedge_le_norm_mul (A 1) (A s)
  rw [hA,hstable] at hw
  have haxes : wedge 1 s=s.im := by simp [wedge]
  rw [haxes] at hw
  have hlow : (3/4)*‖A‖ ≤ ‖A 1‖ := by
    have hh:=mul_le_mul_of_nonneg_right (him.trans hw) hD.le
    simpa only [mul_assoc,inv_mul_cancel₀ hD.ne',mul_one] using hh
  have hup:=Complex.norm_le_abs_re_add_abs_im (A 1)
  by_contra hh
  push Not at hh
  linarith
lemma prefix_stable_vertical (v : ℕ → ℝ) (M : ℝ) (B : ℕ)
    (hB : 1 ≤ B) (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hsmall : 3*M^(-(47/50:ℝ)) ≤ 1/4)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖) :
    ∃ s : ℂ, ‖s‖=1 ∧ |s.re| ≤ 1/4 ∧ ‖transferProduct v B s‖=‖transferProduct v B‖⁻¹ ∧
      ∀ l, 1 ≤ l → l ≤ B → ‖transferProduct v l s‖ ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)) := by
  obtain ⟨s,hu,hs,hpref⟩:=prefix_stable_vector v M B hB hM hq hv hg
  refine ⟨s,hu,?_,hs,hpref⟩
  have hh:=hpref 1 le_rfl hB
  have hc : (transferProduct v 1 s).im=s.re := rfl
  calc
    _ = |(transferProduct v 1 s).im| := congrArg abs hc.symm
    _ ≤ ‖transferProduct v 1 s‖ := Complex.abs_im_le_norm _
    _ ≤ 3*M^(-(47/50:ℝ)) := by simpa using hh
    _ ≤ _ := hsmall
lemma initial_kernel_dirichlet (v : ℕ → ℝ) (J : ℕ) (u : ℂ)
    (_hui : u.im=1) (_hJ : 1 ≤ J) (huj : linearSolution v 1 u.re J=0)
    (ht : tSolution v J ≠ 0) :
    ∀ p, linearSolution v 1 u.re p=dirichletSolution v J p := by
  have hb:=boundaryValue_unique v J ht u.re huj
  intro p
  rw [hb]
  rfl
end StandardMapEntropy

end OAI
