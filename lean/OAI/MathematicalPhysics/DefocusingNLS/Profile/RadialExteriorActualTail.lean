import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCorrection
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailData

namespace OAI

/-! An actual nonlinear slow solution on a sufficiently long exterior tail. -/

open Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_radialExterior_actual_tail (ν : ℂ) (n : ℕ) (m : ℂ)
    (δ : ℝ) (hδ : 0 < δ) (hδm : δ < ‖m‖) :
    ∃ T : ℝ, ∃ F G : ℝ → ℂ,
      Tendsto F atTop (nhds m) ∧ Tendsto G atTop (nhds 0) ∧
      ∀ t, T ≤ t → F t ≠ 0 ∧
        HasDerivAt F (G t) t ∧
        HasDerivAt G (-(2*ν+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*G t-
          ν*(ν+10)*F t+oddPowerNonlinearity n (F t)) t := by
  let L := radialExteriorMatrixBound ν+radialExteriorCutoffRate n m δ
  have hL : 0 < L := add_pos_of_pos_of_nonneg (radialExteriorMatrixBound_pos ν)
    (radialExteriorCutoffRate_nonneg n m δ)
  obtain ⟨j,hj⟩ := exists_nat_gt (L/2)
  have hκ : L < 2*(j : ℝ) := by linarith
  have hκ0 : 0 < 2*(j : ℝ) := hL.trans hκ
  let P := radialExteriorExpansion ν n m j
  obtain ⟨R,hR⟩ := radialExterior_normalized_residual ν n m j
  let r := boundedRadialResidual R
  obtain ⟨v,hv,hd⟩ := exists_radialExterior_nonlinear_tail (2*(j : ℝ)) ν n m δ hδ.le hκ
    (boundedRadialPolynomial P) (boundedRadialPolynomial P).continuous r
  let Y := radialExteriorUnweight (2*(j : ℝ)) v
  let F : ℝ → ℂ := fun t => radialExteriorPolynomialFunction P t+(Y t).1
  let G : ℝ → ℂ := fun t => radialExteriorPolynomialFunction (radialPolynomialEuler P) t+(Y t).2
  have hYlim : Tendsto Y atTop (nhds 0) := radialExteriorUnweight_tendsto _ hκ0 v
  have hY1 : Tendsto (fun t => (Y t).1) atTop (nhds 0) := by
    simpa using! (continuous_fst.tendsto (0 : ℂ × ℂ)).comp hYlim
  have hY2 : Tendsto (fun t => (Y t).2) atTop (nhds 0) := by
    simpa using! (continuous_snd.tendsto (0 : ℂ × ℂ)).comp hYlim
  have hP : Tendsto (radialExteriorPolynomialFunction P) atTop (nhds m) := by
    simpa only [P,radialExteriorExpansion_constant] using radialExteriorPolynomialFunction_tendsto P
  have hF : Tendsto F atTop (nhds m) := by simpa only [add_zero] using hP.add hY1
  have hG : Tendsto G atTop (nhds 0) := by
    simpa only [radialPolynomialEuler_coeff,Nat.cast_zero,mul_zero,zero_mul,add_zero] using
      (radialExteriorPolynomialFunction_tendsto (radialPolynomialEuler P)).add hY2
  have ep : ∀ᶠ t : ℝ in atTop, ‖radialExteriorPolynomialFunction P t-m‖ < δ :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hP).eventually (gt_mem_nhds hδ)
  have ef : ∀ᶠ t : ℝ in atTop, ‖F t-m‖ < δ :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hF).eventually (gt_mem_nhds hδ)
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((ep.and ef).and (eventually_ge_atTop (0 : ℝ)))
  refine ⟨T,F,G,hF,hG,?_⟩
  intro t ht
  obtain ⟨⟨hpt,hft⟩,ht0⟩ := hT t ht
  have hFne : F t ≠ 0 := by
    intro hz
    rw [hz,zero_sub,norm_neg] at hft
    exact (hδm.trans hft).false
  refine ⟨hFne,?_⟩
  have hvt : HasDerivAt (fun s => v s)
      ((2*(j : ℝ)) • v t+(0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(v t).2)+
        radialExteriorErrorMatrix ν (v t)+
        (0,radialExteriorWeightedIncrement (2*(j : ℝ))
          (radialExteriorCutoffPower n m δ) (boundedRadialPolynomial P) t (v t).1)+r t) t := by
    simpa only [radialExteriorErrorField,add_assoc] using hd t
  have hyt := radialExteriorUnweight_hasDerivAt (2*(j : ℝ)) t ν
    (radialExteriorCutoffPower n m δ) (boundedRadialPolynomial P) r v hvt
  change HasDerivAt Y _ t at hyt
  rw [boundedRadialPolynomial_nonneg P t ht0] at hyt
  rw [radialExteriorCutoffPower_eq n m δ _ hpt.le,
    radialExteriorCutoffPower_eq n m δ _ hft.le] at hyt
  have hr := hR t ht0
  change Real.exp (-(2*(j : ℝ))*t) • r t = _ at hr
  rw [hr] at hyt
  have hy : HasDerivAt Y
      ((Y t).2,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Y t).2-
        (2*ν+10)*(Y t).2-ν*(ν+10)*(Y t).1+
        oddPowerNonlinearity n (radialExteriorPolynomialFunction P t+(Y t).1)-
        oddPowerNonlinearity n (radialExteriorPolynomialFunction P t)-
        radialExteriorPolynomialFunction (radialExteriorPolynomialResidual ν n P) t) t := by
    apply hyt.congr_deriv
    apply Prod.ext <;> simp [radialExteriorErrorMatrix] <;> ring
  exact radialExterior_corrected_jet ν n P Y t hy

end DefocusingNLS

end OAI
