import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.QuadraticSieveDivisorDyadicBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem divisorDyadicDepth_log_bound {D N : ℕ} (hD : 0<D) (hN : 0<N)
    (hDN : D≤N^2) :
    (divisorDyadicDepth D : ℝ)*Real.log 2 ≤ 2*Real.log 2+2*Real.log (N : ℝ) := by
  have hNreal : (0 : ℝ)<N := by exact_mod_cast hN
  have hpowNat : 2^(Nat.log 2 (2*D))≤2*N^2 :=
    (Nat.pow_log_le_self 2 (by omega : 2*D≠0)).trans (Nat.mul_le_mul_left 2 hDN)
  have hpow : (2 : ℝ)^(Nat.log 2 (2*D))≤2*(N : ℝ)^2 := by exact_mod_cast hpowNat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ)<2^(Nat.log 2 (2*D))) hpow
  rw [Real.log_pow,Real.log_mul (by norm_num : (2 : ℝ)≠0) (by positivity),Real.log_pow] at hlog
  simp only [divisorDyadicDepth,Nat.cast_add,Nat.cast_one]
  norm_num at hlog
  nlinarith

theorem divisorDyadicDepth_fourth_le_rpow (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ D N : ℕ, 0<D → 0<N → D≤N^2 →
      (divisorDyadicDepth D : ℝ)^4 ≤ C*(N : ℝ)^ε := by
  let δ : ℝ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  let B : ℝ := 2+2/(δ*Real.log 2)
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B^4,by positivity,?_⟩
  intro D N hD hN hDN
  have hNreal : (0 : ℝ)<N := by exact_mod_cast hN
  have hNr : 1≤(N : ℝ)^δ := Real.one_le_rpow (by exact_mod_cast hN) hδ.le
  have hlog := divisorDyadicDepth_log_bound hD hN hDN
  have hlogN := Real.log_le_rpow_div hNreal.le hδ
  have hBr : B*((N : ℝ)^δ)*Real.log 2 =
      2*Real.log 2*((N : ℝ)^δ)+2*((N : ℝ)^δ/δ) := by
    dsimp [B]
    field_simp
  have hdepth : (divisorDyadicDepth D : ℝ)≤B*(N : ℝ)^δ := by
    apply (mul_le_mul_iff_right₀ hl).mp
    rw [mul_comm (Real.log 2) (B*(N : ℝ)^δ),hBr]
    nlinarith
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (divisorDyadicDepth D)) hdepth 4
  rw [mul_pow,←Real.rpow_mul_natCast hNreal.le] at hpow
  have hexp : δ*(4 : ℕ)=ε := by dsimp [δ]; norm_num
  simpa only [hexp] using hpow

end Ostmann.QuadraticSieve

end

end OAI
