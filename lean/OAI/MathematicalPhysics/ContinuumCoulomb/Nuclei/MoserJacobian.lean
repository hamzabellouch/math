import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserFlowRegularity
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! The continuity equation yields the density-Jacobian identity along the
flow. The proof uses finite-dimensional ODE regularity. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open NeutralAtom (dirPartial axis)

private theorem linear_apply_coordinates (L : Position →L[ℝ] ℝ) (v : Position) :
    L v = ∑ a : Fin 3, v a * L (axis a) := by
  have he : v = ∑ a : Fin 3, v a • axis a := by
    ext b
    simp [axis, Pi.single_apply]
  calc
    L v = L (∑ a : Fin 3, v a • axis a) := congrArg L he
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

private theorem divergence_scalar_mul (f : Position → ℝ) (v : Position → Position)
    (hf : Differentiable ℝ f) (hv : Differentiable ℝ v) (x : Position) :
    (∑ a : Fin 3, dirPartial (fun y => f y * v y a) (axis a) x) =
      fderiv ℝ f x (v x) + f x * fieldDivergence v x := by
  have hcoord (a : Fin 3) : Differentiable ℝ (fun y => v y a) := by
    intro y
    exact ((PiLp.hasFDerivAt_apply 2 (v y) a).comp y (hv y).hasFDerivAt).differentiableAt
  have hp (a : Fin 3) : dirPartial (fun y => f y * v y a) (axis a) x =
      v x a * dirPartial f (axis a) x + f x * dirPartial (fun y => v y a) (axis a) x := by
    unfold dirPartial
    rw [fderiv_fun_mul (hf x) (hcoord a x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    linear_apply_coordinates (fderiv ℝ f x) (v x)]
  rfl

theorem moser_continuity_expanded {rho : ℝ} (hrho : 0 < rho)
    (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x : Position) :
    manufacturedCharge V x +
      t * fderiv ℝ (manufacturedCharge V) x (moserVelocity rho V t x) +
      homotopyDensity rho V t x * fieldDivergence (moserVelocity rho V t) x = 0 := by
  have hσ : Differentiable ℝ (manufacturedCharge V) :=
    (manufacturedCharge_C4 V hV).differentiable (by norm_num)
  have hρc : ContDiff ℝ 4 (homotopyDensity rho V t) :=
    contDiff_const.add (contDiff_const.mul (manufacturedCharge_C4 V hV))
  have hρ : Differentiable ℝ (homotopyDensity rho V t) :=
    hρc.differentiable (by norm_num)
  have hv := (moserVelocity_C4 hrho V hV hbound ht.1 ht.2).differentiable (by norm_num)
  have h := moser_continuity_equation hrho V (hV.of_le (by norm_num)) hbound ht.1 ht.2 x
  rw [homotopyDensity_time_deriv, divergence_scalar_mul _ _ hρ hv] at h
  have hd : fderiv ℝ (homotopyDensity rho V t) x = t • fderiv ℝ (manufacturedCharge V) x := by
    unfold homotopyDensity
    rw [fderiv_const_add, fderiv_const_mul (hσ x)]
  rw [hd, smul_apply, smul_eq_mul] at h
  simpa only [add_assoc] using h

theorem flowJacobian_zero (G : Position → ℝ → Position) (hG : ∀ x, G x 0 = x)
    (x : Position) : flowJacobian G 0 x = 1 := by
  have he : (fun y => G y 0) = id := funext hG
  simp [flowJacobian, he, ContinuousLinearMap.det]

/-- Density times the determinant of the actual flow derivative is exactly
constant, including the endpoint used by cubature. -/
theorem moser_density_jacobian (hpublished : PublishedC4FlowInput)
    {rho : ℝ} (hrho : 0 < rho) (V : Position → ℝ) (hV : ContDiff ℝ 6 V)
    (hbound : ∀ x, |manufacturedCharge V x| ≤ rho/2)
    (G : Position → ℝ → Position) (hG : IsUnitTimeFlow (moserVelocity rho V) G)
    (x : Position) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    homotopyDensity rho V t (G x t) * flowJacobian G t x = rho := by
  have hJ := (moser_flow_C4 hpublished hrho V hV hbound G hG).2
  let P : ℝ → ℝ := fun s => homotopyDensity rho V s (G x s) * flowJacobian G s x
  have hσ : Differentiable ℝ (manufacturedCharge V) :=
    (manufacturedCharge_C4 V hV).differentiable (by norm_num)
  have hP (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt P 0 (Set.Icc (0 : ℝ) 1) s := by
    have hσG := (hσ (G x s)).hasFDerivAt.comp_hasDerivWithinAt s (hG.2 x s hs)
    have hρG := (((hasDerivAt_id s).hasDerivWithinAt.mul hσG).const_add rho)
    have hmul := hρG.mul (hJ x s hs)
    have hzero := moser_continuity_expanded hrho V hV hbound hs (G x s)
    convert hmul using 1
    · rfl
    · simp only [id_eq, one_mul, Function.comp_apply, Pi.mul_apply]
      dsimp only [homotopyDensity] at hzero ⊢
      linear_combination -(flowJacobian G s x) * hzero
  have hn := norm_image_sub_le_of_norm_deriv_le_segment' hP
    (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ 0)) t ht
  have he : P t = P 0 := by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hn
  simpa only [P, (homotopyDensity_endpoints rho V (G x 0)).1,
    flowJacobian_zero G hG.1 x, mul_one] using he

end ContinuumCoulomb

end

end OAI
