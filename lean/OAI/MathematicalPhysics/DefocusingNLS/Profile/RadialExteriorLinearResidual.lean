import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExpansionLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialUniform

namespace OAI

/-! The linear part of the formal residual and its large-power limit. -/

open Polynomial Filter
namespace DefocusingNLS

noncomputable def radialExteriorLinearResidual (ν : ℂ) (P : ℂ[X]) : ℂ[X] :=
  radialPolynomialEuler (radialPolynomialEuler P)+C (2*ν+10)*radialPolynomialEuler P+
    C (ν*(ν+10))*P-C Complex.I*P.derivative

theorem radialExteriorLinearResidual_coeff (ν : ℂ) (P : ℂ[X]) (k : ℕ) :
    (radialExteriorLinearResidual ν P).coeff k =
      (ν-2*(k : ℂ))*(ν+10-2*(k : ℂ))*P.coeff k-
        Complex.I*(P.coeff (k+1)*(k+1 : ℕ)) := by
  simp only [radialExteriorLinearResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative]
  push_cast
  ring

theorem radialExteriorLinearResidual_degree (ν : ℂ) (P : ℂ[X]) (d : ℕ)
    (hd : P.natDegree ≤ d) : (radialExteriorLinearResidual ν P).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have h0 : P.coeff k=0 := coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk)
  have h1 : P.coeff (k+1)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [radialExteriorLinearResidual_coeff,h0,h1,mul_zero,zero_mul,sub_zero]

theorem radialExteriorLinearResidual_coefficient_limit
    (ν : ℕ → ℂ) (ν₀ : ℂ) (hν : Tendsto ν atTop (nhds ν₀))
    (P : ℕ → ℂ[X]) (Q : ℂ[X])
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (nhds (Q.coeff k))) (k : ℕ) :
    Tendsto (fun n => (radialExteriorLinearResidual (ν n) (P n)).coeff k) atTop
      (nhds ((radialExteriorLinearResidual ν₀ Q).coeff k)) := by
  simp only [radialExteriorLinearResidual_coeff]
  exact (((hν.sub_const (2*(k : ℂ))).mul ((hν.add_const 10).sub_const (2*(k : ℂ)))).mul
    (hP k)).sub (((hP (k+1)).mul_const ((k+1 : ℕ) : ℂ)).const_mul Complex.I)

theorem radialExteriorLinearResidual_uniform_limit (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀))
    (hm₀ : ‖m₀‖ < 1) (j : ℕ) :
    TendstoUniformlyOn (fun n z =>
        (radialExteriorLinearResidual (ν n) (radialExteriorExpansion (ν n) n (m n) j)).eval z)
      (fun z => (radialExteriorLinearResidual ν₀ (radialFreeExpansion ν₀ m₀ j)).eval z)
      atTop (Metric.closedBall (0 : ℂ) 1) := by
  apply radialPolynomial_eval_tendstoUniformly _ _ j
  · exact Eventually.of_forall (fun n => radialExteriorLinearResidual_degree _ _ _
      (radialExteriorExpansion_degree _ _ _ _))
  · exact radialExteriorLinearResidual_degree _ _ _ (radialFreeExpansion_degree _ _ _)
  · intro k _
    exact radialExteriorLinearResidual_coefficient_limit ν ν₀ hν _ _
      (radialExteriorExpansion_coefficient_limit ν m ν₀ m₀ hν hm hm₀ j) k

theorem radialExteriorLinearResidual_free_divisible (ν m : ℂ) (hm : ‖m‖ < 1) (j : ℕ) :
    X^j ∣ radialExteriorLinearResidual ν (radialFreeExpansion ν m j) := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  let P : ℕ → ℂ[X] := fun n => radialExteriorExpansion ν n m j
  have hc : ∀ k, Tendsto (fun n => (P n).coeff k) atTop
      (nhds ((radialFreeExpansion ν m j).coeff k)) :=
    radialExteriorExpansion_coefficient_limit _ _ ν m tendsto_const_nhds tendsto_const_nhds hm j
  have hL := radialExteriorLinearResidual_coefficient_limit (fun _ : ℕ => ν) ν
    tendsto_const_nhds P _ hc k
  have hN := radialPolynomialPower_coefficient_limit P (radialFreeExpansion ν m j) j k
    (Eventually.of_forall (fun n => radialExteriorExpansion_degree ν n m j))
    (fun k _ => hc k) (by simpa only [radialFreeExpansion_constant] using hm)
  have hlim := hL.sub hN
  simp only [sub_zero] at hlim
  have he : (fun n => (radialExteriorLinearResidual ν (P n)).coeff k-
      (radialPolynomialPower n (P n)).coeff k)=fun _ => (0 : ℂ) := by
    funext n
    exact X_pow_dvd_iff.mp (radialExteriorExpansion_residual ν n m j) k hk
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end DefocusingNLS

end OAI
