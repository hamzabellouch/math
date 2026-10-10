import OAI.NumberTheory.TotientAsymptotic.FordParameterBounds
import OAI.NumberTheory.TotientAsymptotic.FordLogProduct

namespace OAI

/-! Polynomial costs of all bands fit in the published prefactor. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_band_cost_split (C : ℝ) (k : ℕ) (y S : ℝ) (Y U : ℕ → ℝ) :
    fordBandCost C k y S Y U=
      (C*(k:ℝ)^2*(B y)^2)*
      (Real.exp (fordBandCap k y S Y*(Real.log k+1))/(Real.log (U (k-1)))^2) := by
  unfold fordBandCost
  ring

lemma ford_polynomial_budget {C A M B : ℝ} {b : ℕ}
    (hb : 1 ≤ b) (hB : 1 ≤ B) (hbB : (b:ℝ) ≤ B)
    (hC : 1 ≤ C) (_hA : 0 ≤ A) (hM : 0 ≤ M)
    (hAC : 216*A ≤ C) (hMC : M ≤ C) (hCb : 0 ≤ C) :
    (216*A)*M*B^5*(∏ k ∈ Finset.Icc 2 b,C*(k:ℝ)^2*B^2) ≤ (C*B)^(6*b) := by
  have hcount : (Finset.Icc 2 b).card=b-1 := by simp
  have hb0 : 0 ≤ B := by linarith
  have hprod : (∏ k ∈ Finset.Icc 2 b,C*(k:ℝ)^2*B^2) ≤ (C*B^4)^(b-1) := by
    calc
      _ ≤ ∏ _k ∈ Finset.Icc 2 b,C*B^4 := by
        apply Finset.prod_le_prod₀
        · intro k _; positivity
        · intro k hk
          have hkB : (k:ℝ) ≤ B := (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2).trans hbB
          have hh := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hkB 2) hCb)
            (sq_nonneg B)
          convert hh using 1
          ring
      _ = _ := by simp only [Finset.prod_const,hcount]
  have hAM : (216*A)*M ≤ C^2 := by
    have hh := mul_le_mul hAC hMC hM hCb
    nlinarith
  have hpref := mul_le_mul_of_nonneg_right hAM (pow_nonneg hb0 5)
  have hall := mul_le_mul hpref hprod (Finset.prod_nonneg (fun k _ => by positivity)) (by positivity : 0 ≤ C^2*B^5)
  have he : C^2*B^5*(C*B^4)^(b-1)=C^(b+1)*B^(4*b+1) := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hb
    simp only [Nat.add_sub_cancel_left,mul_pow,pow_add,pow_mul]
    ring
  have hCbpow : C^(b+1) ≤ C^(6*b) := pow_le_pow_right₀ hC (by omega)
  have hBpow : B^(4*b+1) ≤ B^(6*b) := pow_le_pow_right₀ hB (by omega)
  calc
    _ ≤ C^2*B^5*(C*B^4)^(b-1) := hall
    _ = C^(b+1)*B^(4*b+1) := he
    _ ≤ C^(6*b)*B^(6*b) := mul_le_mul hCbpow hBpow (by positivity) (by positivity)
    _ = _ := (mul_pow C B (6*b)).symm

end TotientAsymptotic

end

end OAI
