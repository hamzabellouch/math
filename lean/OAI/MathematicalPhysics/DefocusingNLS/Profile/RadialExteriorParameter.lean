import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorJetLimit

namespace OAI

/-! Fixed-power continuity of the actual exterior expansion and residual coefficients. -/

open Polynomial Set Filter
namespace DefocusingNLS

theorem continuous_radialPolynomial_mul_coeff
    (P Q : ℂ × ℂ → ℂ[X])
    (hP : ∀ k, Continuous (fun z => (P z).coeff k))
    (hQ : ∀ k, Continuous (fun z => (Q z).coeff k)) (k : ℕ) :
    Continuous (fun z => (P z*Q z).coeff k) := by
  simp_rw [coeff_mul]
  exact continuous_finsetSum _ (fun i _ => (hP i.1).mul (hQ i.2))

theorem continuous_radialPolynomial_pow_coeff (P : ℂ × ℂ → ℂ[X])
    (hP : ∀ k, Continuous (fun z => (P z).coeff k)) (n k : ℕ) :
    Continuous (fun z => ((P z)^n).coeff k) := by
  induction n generalizing k with
  | zero => simp only [pow_zero]; exact continuous_const
  | succ n ih =>
    simp only [pow_succ]
    exact continuous_radialPolynomial_mul_coeff _ P ih hP k

theorem continuous_radialPolynomialPower_coeff (P : ℂ × ℂ → ℂ[X])
    (hP : ∀ k, Continuous (fun z => (P z).coeff k)) (n k : ℕ) :
    Continuous (fun z => (radialPolynomialPower n (P z)).coeff k) := by
  apply continuous_radialPolynomial_mul_coeff
    (fun z => (P z)^(n+1))
    (fun z => (Polynomial.mapRingHom (starRingEnd ℂ) (P z))^n)
    (fun j => continuous_radialPolynomial_pow_coeff P hP (n+1) j)
    (fun j => continuous_radialPolynomial_pow_coeff _ ?_ n j) k
  intro j
  simpa only [Polynomial.coe_mapRingHom,coeff_map] using! (hP j).star

theorem continuous_radialExteriorExpansion_coeff (n j k : ℕ) :
    Continuous (fun z : ℂ × ℂ => (radialExteriorExpansion z.1 n z.2 j).coeff k) := by
  induction j generalizing k with
  | zero =>
    simp only [radialExteriorExpansion,coeff_C]
    split_ifs <;> fun_prop
  | succ j ih =>
    simp only [radialExteriorExpansion_step,coeff_add,coeff_monomial]
    apply Continuous.add (ih k)
    split_ifs
    · exact (((continuous_fst.sub continuous_const).mul
        (continuous_fst.add continuous_const |>.sub continuous_const)).mul (ih j) |>.sub
        (continuous_radialPolynomialPower_coeff _ ih n j)).div_const _
    · exact continuous_const

theorem continuous_radialExteriorResidual_coeff (n j k : ℕ) :
    Continuous (fun z : ℂ × ℂ =>
      (radialExteriorPolynomialResidual z.1 n (radialExteriorExpansion z.1 n z.2 j)).coeff k) := by
  simp only [radialExteriorPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative]
  apply Continuous.sub
  · have h₀ := continuous_radialExteriorExpansion_coeff n j k
    have h₁ := continuous_radialExteriorExpansion_coeff n j (k+1)
    fun_prop
  · exact continuous_radialPolynomialPower_coeff _ (continuous_radialExteriorExpansion_coeff n j) n k

theorem radialExteriorExpansion_fixed_power_limit (n j : ℕ)
    (z : ℕ → ℂ × ℂ) (z₀ : ℂ × ℂ) (hz : Tendsto z atTop (nhds z₀)) :
    TendstoUniformlyOn
      (fun i x => (radialExteriorExpansion (z i).1 n (z i).2 j).eval x)
      (fun x => (radialExteriorExpansion z₀.1 n z₀.2 j).eval x)
      atTop (Metric.closedBall (0 : ℂ) 1) := by
  apply radialPolynomial_eval_tendstoUniformly _ _ j
    (Eventually.of_forall (fun i => radialExteriorExpansion_degree _ _ _ _))
    (radialExteriorExpansion_degree _ _ _ _)
  intro k _
  exact (continuous_radialExteriorExpansion_coeff n j k).continuousAt.tendsto.comp hz

theorem radialExteriorBase_fixed_power_limit (n j : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (z : ℕ → ℂ × ℂ) (z₀ : ℂ × ℂ) (hz : Tendsto z atTop (nhds z₀)) :
    Tendsto (fun i => boundedRadialPolynomialAfter T
      (radialExteriorExpansion (z i).1 n (z i).2 j)) atTop
      (nhds (boundedRadialPolynomialAfter T (radialExteriorExpansion z₀.1 n z₀.2 j))) := by
  exact boundedRadialPolynomialAfter_limit T 1
    (Real.exp_le_one_iff.mpr (by nlinarith)) _ _
    (radialExteriorExpansion_fixed_power_limit n j z z₀ hz)

theorem radialExteriorResidual_degree (ν m : ℂ) (n j : ℕ) :
    (radialExteriorPolynomialResidual ν n (radialExteriorExpansion ν n m j)).natDegree ≤
      (2*n+1)*j := by
  let P := radialExteriorExpansion ν n m j
  have hP : P.natDegree ≤ j := radialExteriorExpansion_degree _ _ _ _
  have hE := radialPolynomialEuler_degree P j hP
  have hEE := radialPolynomialEuler_degree (radialPolynomialEuler P) j hE
  have hN : (radialPolynomialPower n P).natDegree ≤ (2*n+1)*j := by
    unfold radialPolynomialPower
    apply natDegree_mul_le.trans
    have hmap : (Polynomial.mapRingHom (starRingEnd ℂ) P).natDegree ≤ j :=
      natDegree_map_le.trans hP
    calc
      _ ≤ (n+1)*j+n*j := add_le_add (natDegree_pow_le_of_le _ hP)
        (natDegree_pow_le_of_le _ hmap)
      _ = _ := by ring
  have hlin : (radialPolynomialEuler (radialPolynomialEuler P)+
      C (2*ν+10)*radialPolynomialEuler P+C (ν*(ν+10))*P-
      C Complex.I*P.derivative).natDegree ≤ j := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le
      · exact (natDegree_add_le _ _).trans
          (max_le hEE ((natDegree_C_mul_le _ _).trans hE))
      · exact (natDegree_C_mul_le _ _).trans hP
    · exact (natDegree_C_mul_le _ _).trans
        ((natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hP))
  exact (natDegree_sub_le _ _).trans
    (max_le (hlin.trans (by nlinarith [Nat.zero_le (n*j)])) hN)

theorem radialExteriorResidual_fixed_power_limit (n j : ℕ)
    (z : ℕ → ℂ × ℂ) (z₀ : ℂ × ℂ) (hz : Tendsto z atTop (nhds z₀)) :
    TendstoUniformlyOn
      (fun i x => (radialExteriorPolynomialResidual (z i).1 n
        (radialExteriorExpansion (z i).1 n (z i).2 j)).eval x)
      (fun x => (radialExteriorPolynomialResidual z₀.1 n
        (radialExteriorExpansion z₀.1 n z₀.2 j)).eval x)
      atTop (Metric.closedBall (0 : ℂ) 1) := by
  apply radialPolynomial_eval_tendstoUniformly _ _ ((2*n+1)*j)
    (Eventually.of_forall (fun i => radialExteriorResidual_degree _ _ _ _))
    (radialExteriorResidual_degree _ _ _ _)
  intro k _
  exact (continuous_radialExteriorResidual_coeff n j k).continuousAt.tendsto.comp hz

theorem radialExteriorSource_fixed_power_limit (n j : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (z : ℕ → ℂ × ℂ) (z₀ : ℂ × ℂ) (hz : Tendsto z atTop (nhds z₀))
    (R : ℕ → ℂ[X]) (R₀ : ℂ[X])
    (hR : ∀ i, radialExteriorPolynomialResidual (z i).1 n
      (radialExteriorExpansion (z i).1 n (z i).2 j)=X^j*R i)
    (hR₀ : radialExteriorPolynomialResidual z₀.1 n
      (radialExteriorExpansion z₀.1 n z₀.2 j)=X^j*R₀) :
    Tendsto (fun i => boundedRadialResidualAfter T (R i)) atTop
      (nhds (boundedRadialResidualAfter T R₀)) := by
  apply boundedRadialResidualAfter_limit T 1
    (Real.exp_le_one_iff.mpr (by nlinarith)) _ _
  exact radialPolynomial_quotient_uniform_limit _ _ _ _ j 1 (by norm_num) hR hR₀
    (radialExteriorResidual_fixed_power_limit n j z z₀ hz)

end DefocusingNLS

end OAI
