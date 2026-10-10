import OAI.MeasureTheory.Falconer.Radial.WeakRadialDeletionBudget
import OAI.MeasureTheory.Falconer.Estimates.RegularizationSubpower

namespace OAI

/-! # Absorbing the actual regularization and radial deletion costs -/

namespace Falconer
open scoped ENNReal

theorem weak_radial_total_real_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ)^N)^(-2:ℝ)+(N:ℝ)^k*((2:ℝ)^N)^(-lam)+
        (J:ℝ)*(A*((2:ℝ)^N)^(-a)+((2:ℝ)^N)^(-b))+
        ((J:ℝ)+1)*((2:ℝ)^N)^(-f) ≤ ((2:ℝ)^N)^(-c) := by
  let q := min (lam/2) (min a (min b (min f 2)))
  have hq : 0 < q := lt_min (half_pos hlam) (lt_min ha (lt_min hb (lt_min hf (by norm_num))))
  have hql : q ≤ lam/2 := min_le_left _ _
  have hqa : q ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hqb : q ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqf : q ≤ f := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hq2 : q ≤ 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let D : ℝ := 2+(J:ℝ)*A+(J:ℝ)+((J:ℝ)+1)
  obtain ⟨N₁,h₁⟩ := PlanarFalconer.fixed_polynomial_subpower k (half_pos hlam)
  obtain ⟨N₂,h₂⟩ := Regularization.fixed_constant_absorbed (half_pos hq) D
  refine ⟨q/2,half_pos hq,max 1 (max N₁ N₂),?_⟩
  intro N hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast ((le_max_left _ _).trans hN)
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hp : (N:ℝ)^k ≤ R^(lam/2) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith : (N:ℝ) ≤ 4*(N:ℝ)+1) k).trans (h₁ N hN₁)
  have hpoly : (N:ℝ)^k*R^(-lam) ≤ R^(-q) := by
    calc
      _ ≤ R^(lam/2)*R^(-lam) := mul_le_mul_of_nonneg_right hp (by positivity)
      _ = R^(-(lam/2)) := by rw [← Real.rpow_add hR]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hbound : R^(-2:ℝ)+(N:ℝ)^k*R^(-lam)+
      (J:ℝ)*(A*R^(-a)+R^(-b))+((J:ℝ)+1)*R^(-f) ≤ D*R^(-q) := by
    have h2 := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hq2)
    have ha' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqa)
    have hb' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqb)
    have hf' := Real.rpow_le_rpow_of_exponent_le hR1 (neg_le_neg hqf)
    calc
      _ ≤ R^(-q)+R^(-q)+(J:ℝ)*(A*R^(-q)+R^(-q))+((J:ℝ)+1)*R^(-q) := by
        gcongr
      _ = _ := by dsimp [D]; ring
  apply hbound.trans
  calc
    _ ≤ R^(q/2)*R^(-q) := mul_le_mul_of_nonneg_right (h₂ N hN₂) (by positivity)
    _ = R^(-(q/2)) := by rw [← Real.rpow_add hR]; congr 1; ring

theorem dyadic_thin_cost (N : ℕ) : ((2:ℝ≥0∞)^(2*N))⁻¹ =
    ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ)) := by
  rw [Real.rpow_neg (by positivity),Real.rpow_two,
    ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat,
    ← pow_mul,Nat.mul_comm 2 N]

theorem weak_radial_total_cost (J k : ℕ) {A lam a b f : ℝ}
    (hA : 0 ≤ A) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hf : 0 < f) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((2:ℝ≥0∞)^(2*N))⁻¹+(N^k:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        (J:ℝ≥0∞)*(ENNReal.ofReal (A*((2:ℝ)^N)^(-a))+ENNReal.ofReal (((2:ℝ)^N)^(-b)))+
        (J+1:ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^N)^(-f)) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) := by
  obtain ⟨c,hc,N₀,hN₀⟩ := weak_radial_total_real_cost J k hA hlam ha hb hf
  refine ⟨c,hc,N₀,fun N hN => ?_⟩
  have hh := ENNReal.ofReal_le_ofReal (hN₀ N hN)
  rw [dyadic_thin_cost]
  convert hh using 1
  simp (disch := positivity) only [ENNReal.ofReal_add,ENNReal.ofReal_mul,
    ENNReal.ofReal_pow,ENNReal.ofReal_natCast,ENNReal.ofReal_one]
  norm_cast

end Falconer

end OAI
