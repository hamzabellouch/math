import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLeaf

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open scoped SchwartzMap ContDiff FourierTransform

def leafLogProfile (ρ : 𝓢(ℝ, ℂ)) (v z : ℝ) : ℂ :=
  Real.exp (z / 2) • ρ (-v * Real.exp z)

def leafProfileBound (ρ : 𝓢(ℝ, ℂ)) : ℝ :=
  (SchwartzMap.seminorm ℝ 0 0) ρ + (SchwartzMap.seminorm ℝ 1 1) ρ + 1

theorem leafProfileBound_pos (ρ : 𝓢(ℝ, ℂ)) : 0 < leafProfileBound ρ := by
  have h0 := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) ρ
  have h1 := apply_nonneg (SchwartzMap.seminorm ℝ 1 1) ρ
  dsimp [leafProfileBound]
  linarith

theorem leafLogProfile_hasDerivAt (ρ : 𝓢(ℝ, ℂ)) (v z : ℝ) :
    HasDerivAt (leafLogProfile ρ v)
      ((Real.exp (z / 2) / 2) • ρ (-v * Real.exp z) +
        Real.exp (z / 2) • ((-v * Real.exp z) • deriv ρ (-v * Real.exp z))) z := by
  have ha : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (z / 2) / 2) z := by
    simpa only [id_eq,div_eq_mul_inv,one_mul] using ((hasDerivAt_id z).div_const 2).exp
  have hb : HasDerivAt (fun t : ℝ => -v * Real.exp t) (-v * Real.exp z) z :=
    (Real.hasDerivAt_exp z).const_mul (-v)
  simpa only [leafLogProfile,Function.comp_def,add_comm] using!
    ha.fun_smul ((ρ.differentiableAt).hasDerivAt.scomp z hb)

theorem leafLogProfile_deriv_bound (ρ : 𝓢(ℝ, ℂ)) (v z : ℝ) :
    ‖deriv (leafLogProfile ρ v) z‖ ≤ Real.exp (z / 2) * leafProfileBound ρ := by
  rw [(leafLogProfile_hasDerivAt ρ v z).deriv]
  have hρ := SchwartzMap.norm_le_seminorm ℝ ρ (-v * Real.exp z)
  have hd := SchwartzMap.le_seminorm' ℝ 1 1 ρ (-v * Real.exp z)
  simp only [pow_one,iteratedDeriv_one] at hd
  have h0 := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) ρ
  have h1 := apply_nonneg (SchwartzMap.seminorm ℝ 1 1) ρ
  calc
    _ ≤ ‖(Real.exp (z / 2) / 2) • ρ (-v * Real.exp z)‖ +
        ‖Real.exp (z / 2) • ((-v * Real.exp z) • deriv ρ (-v * Real.exp z))‖ := norm_add_le _ _
    _ = (Real.exp (z / 2) / 2) * ‖ρ (-v * Real.exp z)‖ +
        Real.exp (z / 2) * (|-v * Real.exp z| * ‖deriv ρ (-v * Real.exp z)‖) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (div_nonneg (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 2))]
    _ ≤ (Real.exp (z / 2) / 2) * (SchwartzMap.seminorm ℝ 0 0) ρ +
        Real.exp (z / 2) * (SchwartzMap.seminorm ℝ 1 1) ρ :=
      add_le_add (mul_le_mul_of_nonneg_left hρ (by positivity))
        (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)
    _ ≤ _ := by
      unfold leafProfileBound
      nlinarith [Real.exp_pos (z / 2)]

theorem leafLogProfile_contDiff (ρ : 𝓢(ℝ, ℂ)) (v : ℝ) :
    ContDiff ℝ ∞ (leafLogProfile ρ v) := by
  unfold leafLogProfile
  apply ContDiff.fun_smul
  · fun_prop
  · exact (ρ.smooth ⊤).comp (by fun_prop)

theorem exp_half_log_eq_sqrt {r : ℝ} (hr : 0 < r) :
    Real.exp (Real.log r / 2) = Real.sqrt r := by
  have he : Real.exp (Real.log r / 2) ^ 2 = r := by
    rw [pow_two,← Real.exp_add]
    convert Real.exp_log hr using 2
    ring
  nlinarith [Real.sq_sqrt hr.le,Real.sqrt_nonneg r,Real.exp_pos (Real.log r / 2)]

theorem leafLogProfile_eq_scalar (ρ : 𝓢(ℝ, ℂ)) (v X P : ℝ) (hX : 0 < X) (hP : 0 < P) :
    leafLogProfile ρ v (Real.log (X / P)) =
      (Real.sqrt (X / P):ℂ) * ρ (-v * X / P) := by
  rw [leafLogProfile,exp_half_log_eq_sqrt (div_pos hX hP),Real.exp_log (div_pos hX hP),Complex.real_smul]
  congr 2
  ring

end Ostmann.Arithmetic

end

end OAI
