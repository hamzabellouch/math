import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedComplementBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ScalarScaleBudgets

namespace OAI

/-! Polynomial particle counts meet the exact separation and coercivity
conditions used by the full manufactured-field comparison. -/

noncomputable section
namespace ContinuumCoulomb

theorem polynomial_count_le_exp_separation {N D : ℝ} (hN : 2 ≤ N)
    {r k : ℕ} (hrk : r ≤ k) (hD : 25*(k:ℝ)*Real.log N ≤ D) :
    N^r ≤ Real.exp ((19/320:ℝ)*D) := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hrlog : (r:ℝ)*Real.log N ≤ (k:ℝ)*Real.log N :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hrk) hlog
  have hklog : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _) hlog
  calc
    _ = Real.exp ((r:ℝ)*Real.log N) := by rw [Real.exp_nat_mul,Real.exp_log hN0]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hrlog,hklog,hD])

theorem exists_manufactured_kinetic_exponent {freq rho γ : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (hγ : 0 < γ) (hγ1 : γ ≤ 1/4) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (N : ℝ), 2 ≤ N → ∀ (r : ℕ) (M η ε : ℝ),
      1 ≤ M → M ≤ N^r → 0 ≤ η → η ≤ 1 → ε ≤ 1 →
      M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+((-1/2:ℝ)+freq/2))+2*M*ε ≤
        N^(q+2*r) ∧
      2/N^(q+2*r) ≤ (γ/8)/(2*(M*((M+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
        ((-1/2:ℝ)+freq/2))+γ/8+1)) := by
  let C := manufacturedKineticBudgetConstant freq rho
  let b := γ/(16*C)
  have hC : 0 < C := manufacturedKineticBudgetConstant_positive hf hrho
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨q,hq,hbound⟩ := exists_polynomial_constant_bounds (by positivity : 0 < b/2) C
  refine ⟨q,by omega,fun N hN r M η ε hM hMN hη hη1 hε => ?_⟩
  have hN0 : 0 < N := by linarith
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hM2 : M^2 ≤ N^(2*r) := by
    rw [show 2*r=r*2 by omega,pow_mul]
    exact pow_le_pow_left₀ hMp.le hMN 2
  obtain ⟨hkin,hgap⟩ := manufactured_kinetic_complement_budgets hf hrho hγ hγ1 hM hη hη1 hε
  constructor
  · apply hkin.trans
    change C*M^2 ≤ _
    calc
      _ ≤ N^q*N^(2*r) := mul_le_mul (hbound N hN).2 hM2 (sq_nonneg M) (by positivity)
      _ = _ := (pow_add _ _ _).symm
  · have hsmall : 2/(N^q) ≤ b := by
      have h := (hbound N hN).1
      change (N^q)⁻¹ ≤ b/2 at h
      change 2*(N^q)⁻¹ ≤ b
      linarith
    have hn : 2/N^(q+2*r) ≤ b/N^(2*r) := by
      calc
        _ = (2/N^q)/N^(2*r) := by rw [pow_add]; field_simp
        _ ≤ _ := div_le_div_of_nonneg_right hsmall (by positivity)
    apply hn.trans
    apply le_trans _ hgap
    change b/N^(2*r) ≤ b/M^2
    exact div_le_div_of_nonneg_left hb.le (pow_pos hMp 2) hM2

end ContinuumCoulomb

end

end OAI
