import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserRegularity
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! Uniform derivative control of the actual Poisson charge, from exactly
the six derivatives of the manufactured scalar potential. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial coordinateLaplacian axis)

theorem dirPartial_iterated_norm_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (v : Position) {k : ℕ} (hk : k ≤ 5) (x : Position) :
    ‖iteratedFDeriv ℝ k (dirPartial V v) x‖ ≤
      ‖v‖*‖iteratedFDeriv ℝ (k+1) V x‖ := by
  have hf : ContDiff ℝ 5 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := v) hf.contDiffAt
    (show (k : WithTop ℕ∞) ≤ 5 by exact_mod_cast hk)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

private theorem axis_second_partial_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (a : Fin 3) {k : ℕ} (hk : k ≤ 4) (x : Position) :
    ‖iteratedFDeriv ℝ k (dirPartial (dirPartial V (axis a)) (axis a)) x‖ ≤
      ‖iteratedFDeriv ℝ (k+2) V x‖ := by
  have hp : ContDiff ℝ 5 (dirPartial V (axis a)) :=
    (hV.fderiv_right (by norm_num : (5 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const
  have hpp : ContDiff ℝ 4 (fderiv ℝ (dirPartial V (axis a))) :=
    hp.fderiv_right (by norm_num)
  have h := norm_iteratedFDeriv_clm_apply_const (x := x) (c := axis a) hpp.contDiffAt
    (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)
  rw [norm_iteratedFDeriv_fderiv] at h
  have h' := dirPartial_iterated_norm_bound V hV (axis a) (show k+1 ≤ 5 by omega) x
  have hn : ‖axis a‖ = 1 := by simp [axis]
  simp only [hn, one_mul] at h h'
  exact h.trans (by simpa only [Nat.add_assoc] using h')

/-- All derivatives of the manufactured charge through order four have a
bound depending only on the scalar field's order-six bound. -/
theorem manufacturedCharge_derivative_bound (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : Position) :
    ‖iteratedFDeriv ℝ k (manufacturedCharge V) x‖ ≤ 3*B/(4*Real.pi) := by
  have hpp (a : Fin 3) : ContDiff ℝ 4 (dirPartial (dirPartial V (axis a)) (axis a)) :=
    (((hV.fderiv_right (by norm_num : (5 : WithTop ℕ∞)+1 ≤ 6)).clm_apply contDiff_const).fderiv_right
      (by norm_num : (4 : WithTop ℕ∞)+1 ≤ 5)).clm_apply contDiff_const
  have he : coordinateLaplacian V = fun y =>
      ∑ a : Fin 3, dirPartial (dirPartial V (axis a)) (axis a) y :=
    funext (fun _ => NeutralAtom.coordinateLaplacian_eq_partials
      (hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 6)).contDiffAt)
  have hl : ‖iteratedFDeriv ℝ k (coordinateLaplacian V) x‖ ≤ 3*B := by
    rw [he, iteratedFDeriv_fun_sum_apply (fun a _ =>
      ((hpp a).of_le (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).contDiffAt)]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _a : Fin 3, B := Finset.sum_le_sum (fun a _ =>
        (axis_second_partial_bound V hV a hk x).trans (hbound (k+2) (by omega) x))
      _ = _ := by simp
  have hlreg : ContDiff ℝ 4 (coordinateLaplacian V) := by
    rw [he]
    exact ContDiff.sum (fun a _ => hpp a)
  have hc : (manufacturedCharge V) = fun y => (4*Real.pi)⁻¹ • coordinateLaplacian V y := by
    funext y
    unfold manufacturedCharge
    simp only [smul_eq_mul]
    ring
  rw [hc, iteratedFDeriv_const_smul_apply'
    (hlreg.of_le (show (k : WithTop ℕ∞) ≤ 4 by exact_mod_cast hk)).contDiffAt]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left hl (by positivity)).trans_eq (by ring)

end ContinuumCoulomb

end

end OAI
