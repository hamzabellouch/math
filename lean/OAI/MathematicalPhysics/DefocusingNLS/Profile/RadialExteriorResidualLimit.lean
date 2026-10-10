import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorLinearResidual
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialSubunitLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialQuotientLimit

namespace OAI

/-! Uniform normalized residuals for the actual exterior expansions as the power grows. -/

open Polynomial Set Filter
namespace DefocusingNLS

theorem radialExteriorPolynomialResidual_eq (ν : ℂ) (n : ℕ) (P : ℂ[X]) :
    radialExteriorPolynomialResidual ν n P=
      radialExteriorLinearResidual ν P-radialPolynomialPower n P := rfl

theorem radialExterior_normalized_residual_limit (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀))
    (hm₀ : ‖m₀‖ < 1) (j : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ R : ℕ → ℂ[X], ∃ R₀ : ℂ[X],
      (∀ n, radialExteriorPolynomialResidual (ν n) n (radialExteriorExpansion (ν n) n (m n) j)=X^j*R n) ∧
      radialExteriorLinearResidual ν₀ (radialFreeExpansion ν₀ m₀ j)=X^j*R₀ ∧
      TendstoUniformlyOn (fun n z => (R n).eval z) (fun z => R₀.eval z)
        atTop (Metric.closedBall (0 : ℂ) ε) := by
  classical
  let P : ℕ → ℂ[X] := fun n => radialExteriorExpansion (ν n) n (m n) j
  let Q : ℂ[X] := radialFreeExpansion ν₀ m₀ j
  have hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (nhds (Q.coeff k)) :=
    radialExteriorExpansion_coefficient_limit ν m ν₀ m₀ hν hm hm₀ j
  obtain ⟨ε,ρ,hε,hε1,hρ,hρ1,hcircle⟩ := radialPolynomial_eventually_subunit_circle P Q j
    (Eventually.of_forall (fun n => radialExteriorExpansion_degree _ _ _ _))
    (fun k _ => hP k) (by simpa only [Q,radialFreeExpansion_constant] using hm₀)
  have hL := (radialExteriorLinearResidual_uniform_limit ν m ν₀ m₀ hν hm hm₀ j).mono
    (show Metric.closedBall (0 : ℂ) ε ⊆ Metric.closedBall 0 1 from
      fun z hz => Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hz).trans hε1))
  have hN := radialPolynomialPower_uniform_limit P ε ρ hε hρ hρ1 hcircle
  have hres : TendstoUniformlyOn
      (fun n z => (radialExteriorPolynomialResidual (ν n) n (P n)).eval z)
      (fun z => (radialExteriorLinearResidual ν₀ Q).eval z)
      atTop (Metric.closedBall (0 : ℂ) ε) := by
    have hs := hL.sub hN
    change TendstoUniformlyOn
      (fun n z => (radialExteriorLinearResidual (ν n) (P n)).eval z-
        (radialPolynomialPower n (P n)).eval z)
      (fun z => (radialExteriorLinearResidual ν₀ Q).eval z-0)
      atTop (Metric.closedBall (0 : ℂ) ε) at hs
    simpa only [radialExteriorPolynomialResidual_eq,eval_sub,sub_zero] using hs
  have hd : ∀ n, ∃ R : ℂ[X],
      radialExteriorPolynomialResidual (ν n) n (P n)=X^j*R :=
    fun n => radialExteriorExpansion_residual (ν n) n (m n) j
  choose R hR using hd
  obtain ⟨R₀,hR₀⟩ := radialExteriorLinearResidual_free_divisible ν₀ m₀ hm₀ j
  refine ⟨ε,hε,hε1,R,R₀,hR,hR₀,?_⟩
  exact radialPolynomial_quotient_uniform_limit _ R _ R₀ j ε hε hR hR₀ hres

end DefocusingNLS

end OAI
