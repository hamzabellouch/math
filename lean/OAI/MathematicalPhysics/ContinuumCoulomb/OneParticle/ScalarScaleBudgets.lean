import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialConstantBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! Fixed size-independent thresholds for the scalar conditions in the
manufactured continuum comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem exists_inverse_power_offset {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r k : ℕ, q+r ≤ k → ∀ N : ℝ, 2 ≤ N →
      N^r/N^k ≤ ε := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds hε 1
  refine ⟨q,by omega,fun r k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  calc
    _ ≤ N^r/N^(q+r) := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ (by linarith : 1 ≤ N) hk)
    _ = (N^q)⁻¹ := by rw [pow_add]; field_simp
    _ ≤ ε := (hbound N hN).1

theorem exists_polynomial_ratio_offset (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ r p k : ℕ, q+r+p ≤ k → ∀ N : ℝ, 2 ≤ N →
      C*N^r/(N^k)^2 ≤ ε/N^p := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds hε C
  refine ⟨q,by omega,fun r p k hk N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  calc
    _ ≤ N^q*N^r/(N^k)^2 := by
      gcongr
      exact (hbound N hN).2
    _ ≤ 1/N^(q+p) := by
      rw [div_le_div_iff₀ (by positivity : 0 < (N^k)^2) (pow_pos hN0 _),
        one_mul,← pow_add,← pow_add,← pow_mul]
      exact pow_le_pow_right₀ hN1 (by omega)
    _ = (N^q)⁻¹/N^p := by rw [pow_add]; field_simp
    _ ≤ ε/N^p := div_le_div_of_nonneg_right (hbound N hN).1 (by positivity)

theorem exists_logarithmic_scale_threshold (D : ℝ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      D ≤ 25*(k:ℝ)*Real.log N := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k₀,hk₀⟩ := exists_nat_ge (max 1 (D/(25*Real.log 2)))
  refine ⟨k₀,by exact_mod_cast (le_max_left _ _).trans hk₀,fun k hk N hN => ?_⟩
  have hquot : D/(25*Real.log 2) ≤ (k:ℝ) :=
    ((le_max_right _ _).trans hk₀).trans (by exact_mod_cast hk)
  have hD := (div_le_iff₀ (by positivity : 0 < 25*Real.log 2)).mp hquot
  have hlogs : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  calc
    D ≤ 25*(k:ℝ)*Real.log 2 := by nlinarith only [hD]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlogs (by positivity)

theorem exists_centered_slab_threshold (C S₀ : ℝ) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ N : ℝ, 2 ≤ N →
      ∀ H S : ℝ, (N^k)^50 ≤ H → (N^k)^5 ≤ S → S ≤ 2*(N^k)^5 →
        S₀ ≤ S ∧ 1 ≤ H ∧ C*S^3 ≤ H ∧ (N^k)^5 ≤ H/2 := by
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds
    (show (0:ℝ)<1 by norm_num) (max S₀ (8*max C 0))
  refine ⟨q,by omega,fun k hk N hN H S hH hS hShi => ?_⟩
  have hN1 : 1 ≤ N := by linarith
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hS0 : 0 ≤ S := (pow_nonneg (by positivity : 0 ≤ N^k) 5).trans hS
  have hR2 : 2 ≤ N^k := hN.trans (le_self_pow₀ hN1 (by omega))
  have hmax : max S₀ (8*max C 0) ≤ N^k :=
    (hbound N hN).2.trans (pow_le_pow_right₀ hN1 hk)
  have hC : 8*max C 0 ≤ (N^k)^35 :=
    ((le_max_right _ _).trans hmax).trans (le_self_pow₀ hR1 (by decide))
  have hCH : C*S^3 ≤ (N^k)^50 := by
    calc
      _ ≤ max C 0*(2*(N^k)^5)^3 :=
        mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hS0 hShi 3)
          (pow_nonneg hS0 3) (le_max_right _ _)
      _ = (8*max C 0)*(N^k)^15 := by ring
      _ ≤ (N^k)^35*(N^k)^15 := mul_le_mul_of_nonneg_right hC (by positivity)
      _ = _ := by ring
  have htwo : 2*(N^k)^5 ≤ (N^k)^50 := by
    calc
      _ ≤ (N^k)*(N^k)^5 := mul_le_mul_of_nonneg_right hR2 (by positivity)
      _ = (N^k)^6 := by ring
      _ ≤ _ := pow_le_pow_right₀ hR1 (by decide)
  exact ⟨(le_max_left _ _).trans (hmax.trans ((le_self_pow₀ hR1 (by decide)).trans hS)),
    (one_le_pow₀ hR1).trans hH,hCH.trans hH,by linarith [htwo.trans hH]⟩

end ContinuumCoulomb

end

end OAI
