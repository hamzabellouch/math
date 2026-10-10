import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialOutgoingDerivativeBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Symbol estimates in logarithmic radius before composition with the radial coordinate. -/

open Set Filter
open scoped ContDiff
namespace DefocusingNLS

theorem radial_complexExp_contDiff (ν : ℂ) :
    ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (ν*(t : ℂ))) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem radial_complexExp_iteratedDeriv (ν : ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => Complex.exp (ν*(t : ℂ))) =
      fun t : ℝ => ν^k*Complex.exp (ν*(t : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    have hd := (((hasDerivAt_id t).ofReal_comp.const_mul ν).cexp).const_mul (ν^k)
    simp only [id_eq,Complex.ofReal_one,mul_one] at hd
    rw [hd.deriv]
    simp only [pow_succ]
    ring

theorem radial_logarithmic_product_bound (ν : ℂ) (F : ℝ → ℂ) (L : ℝ)
    (hF : ContDiffOn ℝ ∞ F (Ioi L))
    (hb : ∀ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ t : ℝ in atTop, ‖iteratedDeriv k F t‖ ≤ B)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop,
      ‖iteratedDeriv k (fun s : ℝ => Complex.exp (ν*(s : ℂ))*F s) t‖ ≤
        C*Real.exp (ν.re*t) := by
  choose B hB hbound using hb
  let C := ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*‖ν‖^i*B (k-i)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg _) _)) (hB _))
  have he : ∀ᶠ t : ℝ in atTop, ∀ i ∈ Finset.range (k+1), ‖iteratedDeriv (k-i) F t‖ ≤ B (k-i) :=
    (eventually_all_finset _).mpr (fun i _ => hbound (k-i))
  refine ⟨C,hC,?_⟩
  filter_upwards [he,eventually_gt_atTop L] with t ht hLt
  have hf : ContDiffAt ℝ k F t :=
    ((hF t hLt).contDiffAt (Ioi_mem_nhds hLt)).of_le (by simp)
  rw [iteratedDeriv_fun_mul ((radial_complexExp_contDiff ν).contDiffAt.of_le (by simp)) hf]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1),
        ((k.choose i : ℝ)*‖ν‖^i*B (k-i))*Real.exp (ν.re*t) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [radial_complexExp_iteratedDeriv]
      simp only [norm_mul,norm_pow,Complex.norm_natCast,Complex.norm_exp]
      have hre : (ν*(t : ℂ)).re=ν.re*t := by simp
      rw [hre]
      have hh := mul_le_mul_of_nonneg_left (ht i hi)
        (show 0 ≤ (k.choose i : ℝ)*(‖ν‖^i*Real.exp (ν.re*t)) by positivity)
      convert hh using 1
      ring
    _ = _ := by rw [← Finset.sum_mul]

theorem radialExteriorCanonical_logarithmic_symbol (ν m : ℂ) (n : ℕ) (L : ℝ)
    (hX : HasRadialExterior ν n m L) (hm : m ≠ 0) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop,
      ‖iteratedDeriv k (fun s : ℝ => Complex.exp (ν*(s : ℂ))*
        (radialExteriorCanonical ν n m L s).1) t‖ ≤ C*Real.exp (ν.re*t) := by
  apply radial_logarithmic_product_bound ν _ L _
    (radialExteriorCanonical_derivatives_bounded ν m n L hX hm) k
  exact radialExteriorODE_position_contDiffOn ν n _ L
    (fun s hs => ((radialExteriorCanonical_spec hX).2.2 s hs.le).2)

end DefocusingNLS

end OAI
