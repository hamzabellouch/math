import OAI.Analysis.Cotype.WalshDuality
import OAI.Analysis.Cotype.WalshAmplification

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω]

def finiteL2DualLinear (g : Ω → (X →L[ℝ] ℝ)) : PiLp 2 (fun _ : Ω => X) →ₗ[ℝ] ℝ where
  toFun z := ∑ a, g a (z a)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

theorem finiteL2DualLinear_bound (g : Ω → (X →L[ℝ] ℝ)) (z : PiLp 2 (fun _ : Ω => X)) :
    ‖finiteL2DualLinear g z‖ ≤ ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ * ‖z‖ := by
  calc
    _ ≤ ∑ a, ‖g a (z a)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖g a‖ * ‖z a‖ := Finset.sum_le_sum (fun a _ => (g a).le_opNorm _)
    _ ≤ _ := by
      simpa only [PiLp.norm_eq_of_L2, ofLp_toLp] using
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => ‖g a‖) (fun a => ‖z a‖)

def finiteL2Dual (g : Ω → (X →L[ℝ] ℝ)) : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ :=
  (finiteL2DualLinear g).mkContinuous ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖
    (finiteL2DualLinear_bound g)

@[simp] theorem finiteL2Dual_apply (g : Ω → (X →L[ℝ] ℝ)) (z : PiLp 2 (fun _ : Ω => X)) :
    finiteL2Dual g z = ∑ a, g a (z a) := rfl

theorem finiteL2Dual_norm_le (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ ≤ ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ :=
  (finiteL2Dual g).opNorm_le_bound (norm_nonneg _) (finiteL2DualLinear_bound g)

def probabilityL2Vector {n : ℕ} (f : Cube n → X) : PiLp 2 (fun _ : Cube n => X) :=
  Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) • toLp 2 f

def probabilityL2Dual {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) :
    PiLp 2 (fun _ : Cube n => X) →L[ℝ] ℝ :=
  Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) • finiteL2Dual g

theorem probabilityL2Vector_norm {n : ℕ} (f : Cube n → X) :
    ‖probabilityL2Vector f‖ = cubeL2 X f := by
  rw [probabilityL2Vector, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    cubeL2_eq_piLp]

theorem probabilityL2Dual_norm_le {n : ℕ} (g : Cube n → (X →L[ℝ] ℝ)) :
    ‖probabilityL2Dual g‖ ≤ cubeL2 (X →L[ℝ] ℝ) g := by
  rw [probabilityL2Dual, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    cubeL2_eq_piLp]
  exact mul_le_mul_of_nonneg_left (finiteL2Dual_norm_le g) (Real.sqrt_nonneg _)

theorem probabilityL2Dual_amplification {n : ℕ} (T : X →L[ℝ] Y)
    (f : Cube n → X) (g : Cube n → (Y →L[ℝ] ℝ)) :
    probabilityL2Dual g (l2Amplification T (probabilityL2Vector f)) =
      dualPairing (fun u => T (f u)) g := by
  simp only [probabilityL2Dual, smul_apply, smul_eq_mul, finiteL2Dual_apply,
    l2Amplification_apply, probabilityL2Vector,
    map_smul, Finset.mul_sum, dualPairing, average]
  apply Finset.sum_congr rfl
  intro u _
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (by positivity)]

end Cotype

end

end OAI
