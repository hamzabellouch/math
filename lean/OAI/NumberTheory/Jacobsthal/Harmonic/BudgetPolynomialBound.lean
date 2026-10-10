import OAI.NumberTheory.Jacobsthal.Estimates.UniformFailureBudget
import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialMesh

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section


namespace NumberTheoryLean.BudgetPolynomialBound

open UniformFailureBudget PrimeKilledChain

noncomputable def coefficient (A C₁ C₂ C₃ D : ℝ) : ℝ :=
  2*(224*C₁+1+24*D+4*C₂*(24*A+5)+4*C₃*(24*A+3))

theorem coefficient_nonneg {A C₁ C₂ C₃ D : ℝ} (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hD : 0 ≤ D) : 0 ≤ coefficient A C₁ C₂ C₃ D := by
  unfold coefficient
  positivity

theorem budget_polynomial_bound {c₁ c₂ C₁ C₂ C₃ D κ w S A P : ℝ} (N : ℕ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hκ : 0 ≤ κ) (hc₁ : 4*κ ≤ c₁) (hc₂ : 2*κ ≤ c₂) (hκr : κ ≤ normalizationRate)
    (hw : 0 ≤ Real.log w) (hP : 1 ≤ P) (hS : 0 ≤ S) (hSP : S ≤ P) (hNP : (N:ℝ) ≤ A*P)
    (hclock : 4*(N:ℝ)*ExponentialMesh.mesh κ w ≤ 1)
    (hparent : D*(1+S)^3*ExponentialMesh.mesh κ w ≤ 1) :
    (N:ℝ)*stepBudget c₁ c₂ C₁ C₂ C₃ D w S (ExponentialMesh.mesh κ w) N ≤
      (A*coefficient A C₁ C₂ C₃ D)*P^7*Real.exp (-κ*Real.sqrt (Real.log w)) := by
  let τ := ExponentialMesh.mesh κ w
  let e := Real.exp (-κ*Real.sqrt (Real.log w))
  let E₁ := Real.exp (-c₁*Real.sqrt ((1/2:ℝ)*Real.log w))
  let E₂ := Real.exp (-c₂*Real.sqrt ((1/2:ℝ)*Real.log w))
  have hτ : 0 < τ := ExponentialMesh.mesh_pos κ w
  have hτe : τ ≤ e := ExponentialMesh.mesh_upper κ w
  have hτ1 : τ ≤ 1 := ExponentialMesh.mesh_le_one hκ w
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hE₁ : E₁ ≤ e := ExponentialMesh.prime_error_dominated hκ (by linarith) hw
  have hE₂ : E₂ ≤ e := ExponentialMesh.prime_error_dominated hκ hc₂ hw
  have hEdiv : E₁/τ ≤ 2*e := ExponentialMesh.prime_error_over_mesh hκ hc₁ hw
  have hP0 : 0 ≤ P := by linarith
  have hS1 : 0 ≤ S+1 := by linarith
  have hSp : 1+S ≤ 2*P := by linarith
  have hpow2 : 1 ≤ P^2 := one_le_pow₀ hP
  have hpow6 : 1 ≤ P^6 := one_le_pow₀ hP
  have hpow36 : P^3 ≤ P^6 := pow_le_pow_right₀ hP (by norm_num)
  have hpow46 : P^4 ≤ P^6 := pow_le_pow_right₀ hP (by norm_num)
  have he2 : e ≤ P^2*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow2 he
  have he6 : e ≤ P^6*e := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow6 he
  have hcount : (S/τ+2)*(τ^2+E₁) ≤ 7*P*e := by
    have hid : (S/τ+2)*(τ^2+E₁) = S*τ+2*τ^2+S*(E₁/τ)+2*E₁ := by
      field_simp
      ring
    rw [hid]
    have hsq : τ^2 ≤ τ := by nlinarith only [hτ.le, hτ1]
    have h1 := mul_le_mul_of_nonneg_left hτe hS
    have h2 := mul_le_mul_of_nonneg_left hEdiv hS
    have h3 := mul_le_mul_of_nonneg_right hSP he
    have h4 := mul_le_mul_of_nonneg_right hP he
    nlinarith only [hsq, h1, h2, h3, h4, hE₁, hτe]
  have hfirst : (S/τ+2)*(C₁*(1+S)^5*(τ^2+E₁)) ≤ 224*C₁*P^6*e := by
    calc
      _ = (C₁*(1+S)^5)*((S/τ+2)*(τ^2+E₁)) := by ring
      _ ≤ (C₁*(2*P)^5)*(7*P*e) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSp 5) hC₁) hcount
        (by positivity) (by positivity)
      _ = _ := by ring
  have hU : upperDisplacement S τ N ≤ 24*A*P^2*e := by
    have hexp := ExponentialMesh.exp_increment (show 0 ≤ 4*(N:ℝ)*τ by positivity) hclock
    have hNmul : 12*(N:ℝ)*τ ≤ 12*(A*P)*e := by
      exact mul_le_mul (by nlinarith only [hNP] : 12*(N:ℝ) ≤ 12*(A*P)) hτe hτ.le (by positivity)
    calc
      _ ≤ (S+1)*(12*(N:ℝ)*τ) := by
        unfold upperDisplacement
        apply mul_le_mul_of_nonneg_left _ hS1
        nlinarith only [hexp]
      _ ≤ (2*P)*(12*(A*P)*e) := mul_le_mul (by linarith) hNmul (by positivity) (by positivity)
      _ = _ := by ring
  have hδ : upperDisplacement S τ N+3*τ ≤ (24*A+3)*P^2*e := by
    nlinarith only [hU, hτe, he2]
  have hδE : upperDisplacement S τ N+3*τ+2*E₂ ≤ (24*A+5)*P^2*e := by
    nlinarith only [hδ, hE₂, he2]
  have hpar : Real.exp (D*(1+S)^3*τ)-1 ≤ 24*D*P^6*e := by
    have hexp := ExponentialMesh.exp_increment (show 0 ≤ D*(1+S)^3*τ by positivity) hparent
    have hsmall : D*(1+S)^3*τ ≤ D*(2*P)^3*e := mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSp 3) hD) hτe hτ.le (by positivity)
    calc
      _ ≤ 3*(D*(2*P)^3*e) := hexp.trans (mul_le_mul_of_nonneg_left hsmall (by norm_num))
      _ = (24*D*e)*P^3 := by ring
      _ ≤ (24*D*e)*P^6 := mul_le_mul_of_nonneg_left hpow36 (by positivity)
      _ = _ := by ring
  have hb₂ : C₂*(1+S)^2*(upperDisplacement S τ N+3*τ+2*E₂) ≤ 4*C₂*(24*A+5)*P^6*e := by
    calc
      _ ≤ (C₂*(2*P)^2)*((24*A+5)*P^2*e) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSp 2) hC₂) hδE
        (by have hu := upperDisplacement_nonneg hS1 hτ.le N; positivity) (by positivity)
      _ = (4*C₂*(24*A+5)*e)*P^4 := by ring
      _ ≤ (4*C₂*(24*A+5)*e)*P^6 := mul_le_mul_of_nonneg_left hpow46 (by positivity)
      _ = _ := by ring
  have hb₃ : C₃*(1+S)^2*(upperDisplacement S τ N+3*τ) ≤ 4*C₃*(24*A+3)*P^6*e := by
    calc
      _ ≤ (C₃*(2*P)^2)*((24*A+3)*P^2*e) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hSp 2) hC₃) hδ
        (by have hu := upperDisplacement_nonneg hS1 hτ.le N; positivity) (by positivity)
      _ = (4*C₃*(24*A+3)*e)*P^4 := by ring
      _ ≤ (4*C₃*(24*A+3)*e)*P^6 := mul_le_mul_of_nonneg_left hpow46 (by positivity)
      _ = _ := by ring
  have hε : epsilon w ≤ P^6*e := by
    apply le_trans _ he6
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hκr) (Real.sqrt_nonneg (Real.log w))
  have hbudget : stepBudget c₁ c₂ C₁ C₂ C₃ D w S τ N ≤ coefficient A C₁ C₂ C₃ D*P^6*e := by
    have hsum := add_le_add (add_le_add (add_le_add (add_le_add hfirst hε) hpar) hb₂) hb₃
    calc
      _ ≤ 2*(224*C₁*P^6*e+P^6*e+24*D*P^6*e+4*C₂*(24*A+5)*P^6*e+4*C₃*(24*A+3)*P^6*e) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = _ := by unfold coefficient; ring
  have hK := coefficient_nonneg hA hC₁ hC₂ hC₃ hD
  calc
    _ ≤ (N:ℝ)*(coefficient A C₁ C₂ C₃ D*P^6*e) := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)
    _ ≤ (A*P)*(coefficient A C₁ C₂ C₃ D*P^6*e) := mul_le_mul_of_nonneg_right hNP (by positivity)
    _ = _ := by ring

end NumberTheoryLean.BudgetPolynomialBound

end

end Erdos970

end OAI
