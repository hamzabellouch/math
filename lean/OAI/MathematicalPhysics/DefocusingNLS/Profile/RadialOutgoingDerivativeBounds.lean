import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialOutgoingDerivativeExpansion

namespace OAI

/-! Every logarithmic derivative of the true outgoing profile is bounded. -/

open Set Filter Polynomial
open scoped ContDiff
namespace DefocusingNLS

theorem radialExteriorCanonical_positive_derivative_decay (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) (k : ℕ) (hk : 0 < k) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun s => (radialExteriorCanonical ν n m L s).1) t‖ ≤
        A*Real.exp (-2*t) := by
  obtain ⟨A,T,hA,hb⟩ := radialExteriorCanonical_derivative_expansion ν m n L hX hm 0 k
  refine ⟨A,hA,?_⟩
  filter_upwards [eventually_ge_atTop T,eventually_gt_atTop L] with t ht hLt
  have hs := radialExteriorODE_position_contDiffOn ν n
    (radialExteriorCanonical ν n m L) L
    (fun s hs => ((radialExteriorCanonical_spec hX).2.2 s hs.le).2)
  have hf : ContDiffAt ℝ k (fun s => (radialExteriorCanonical ν n m L s).1) t :=
    ((hs t hLt).contDiffAt (Ioi_mem_nhds hLt)).of_le (by simp)
  have hc : radialExteriorPolynomialFunction (radialExteriorExpansion ν n m 0)=
      fun _ => m := by
    funext s
    simp [radialExteriorExpansion,radialExteriorPolynomialFunction]
  have hh := hb t ht
  rw [hc,iteratedDeriv_sub hf contDiffAt_const,iteratedDeriv_const] at hh
  simpa only [Nat.ne_of_gt hk,ite_false,sub_zero,Nat.zero_add,Nat.cast_one,mul_one] using hh

theorem radialExteriorCanonical_derivatives_bounded (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in atTop,
      ‖iteratedDeriv k (fun s => (radialExteriorCanonical ν n m L s).1) t‖ ≤ A := by
  cases k with
  | zero =>
    have ht := (continuous_fst.tendsto (m,(0 : ℂ))).comp
      (radialExteriorCanonical_spec hX).2.1.tendsto
    refine ⟨‖m‖+1,by positivity,?_⟩
    simpa only [iteratedDeriv_zero,Function.comp_def] using
      ht.norm.eventually (gt_mem_nhds (by linarith : ‖m‖ < ‖m‖+1)) |>.mono
        (fun _ h => h.le)
  | succ k =>
    obtain ⟨A,hA,hb⟩ := radialExteriorCanonical_positive_derivative_decay ν m n L hX hm
      (k+1) (by omega)
    refine ⟨A,hA,?_⟩
    filter_upwards [hb,eventually_ge_atTop (0 : ℝ)] with t ht ht0
    exact ht.trans (mul_le_of_le_one_right hA (Real.exp_le_one_iff.mpr (by linarith)))

end DefocusingNLS

end OAI
