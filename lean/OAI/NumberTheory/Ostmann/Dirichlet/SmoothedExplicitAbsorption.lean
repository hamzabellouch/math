import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace OAI

namespace Ostmann.Dirichlet

theorem exists_smoothed_error_absorption (E K M D J : ℝ)
    (hE : 0 ≤ E) (hK : 0 < K) (hM : 0 ≤ M) (hD : 0 ≤ D) (hJ : 0 ≤ J) :
    ∃ C : ℝ, 0 < C ∧ ∀ U V Z R L : ℝ,
      0 ≤ U → 0 ≤ V → 0 ≤ Z → 1 ≤ R → 0 ≤ L →
      K*Z + K*M*U*R^5 + 2*E*K*U*R^6 +
        4*E*K*Real.exp 1*V*R^5 + 2*K*Real.exp 1*J*V*(L+D) ≤
      C*(Z+U*R^7+V*R^7*(1+L)^7) := by
  let CU := K*M+2*E*K
  let CV := 4*E*K*Real.exp 1+2*K*Real.exp 1*J*(D+1)
  let C := 1+max K (max CU CV)
  have hCU : 0 ≤ CU := by dsimp [CU]; positivity
  have hCV : 0 ≤ CV := by dsimp [CV]; positivity
  have hCK : K ≤ C := le_trans (le_max_left _ _) (by dsimp [C]; linarith)
  have hCUp : CU ≤ C := le_trans ((le_max_left _ _).trans (le_max_right _ _))
    (by dsimp [C]; linarith)
  have hCVp : CV ≤ C := le_trans ((le_max_right _ _).trans (le_max_right _ _))
    (by dsimp [C]; linarith)
  refine ⟨C,hK.trans_le hCK,?_⟩
  intro U V Z R L hU hV hZ hR hL
  have hR0 : 0 ≤ R := by linarith
  have hL1 : 1 ≤ 1+L := by linarith
  have hR5 : R^5 ≤ R^7 := pow_le_pow_right₀ hR (by norm_num)
  have hR6 : R^6 ≤ R^7 := pow_le_pow_right₀ hR (by norm_num)
  have hR7 : 1 ≤ R^7 := one_le_pow₀ hR
  have hLP : 1 ≤ (1+L)^7 := one_le_pow₀ hL1
  have hLpow : 1+L ≤ (1+L)^7 := le_self_pow₀ hL1 (by norm_num)
  have hRp : R^5 ≤ R^7*(1+L)^7 := hR5.trans (le_mul_of_one_le_right (by positivity) hLP)
  have hLL : L+D ≤ (D+1)*(R^7*(1+L)^7) := by
    calc
      _ ≤ (D+1)*(1+L) := by nlinarith
      _ ≤ (D+1)*(R^7*(1+L)^7) := by
        gcongr
        exact hLpow.trans (le_mul_of_one_le_left (by positivity) hR7)
  have h1 := mul_le_mul_of_nonneg_left hR5 (show 0 ≤ K*M*U by positivity)
  have h2 := mul_le_mul_of_nonneg_left hR6 (show 0 ≤ 2*E*K*U by positivity)
  have h3 := mul_le_mul_of_nonneg_left hRp (show 0 ≤ 4*E*K*Real.exp 1*V by positivity)
  have h4 := mul_le_mul_of_nonneg_left hLL (show 0 ≤ 2*K*Real.exp 1*J*V by positivity)
  have hraw : K*Z + K*M*U*R^5 + 2*E*K*U*R^6 +
        4*E*K*Real.exp 1*V*R^5 + 2*K*Real.exp 1*J*V*(L+D) ≤
      K*Z+CU*(U*R^7)+CV*(V*R^7*(1+L)^7) := by
    dsimp [CU,CV]
    nlinarith only [h1,h2,h3,h4]
  apply hraw.trans
  have hk := mul_le_mul_of_nonneg_right hCK hZ
  have hu := mul_le_mul_of_nonneg_right hCUp (show 0 ≤ U*R^7 by positivity)
  have hv := mul_le_mul_of_nonneg_right hCVp (show 0 ≤ V*R^7*(1+L)^7 by positivity)
  nlinarith only [hk,hu,hv]

end Ostmann.Dirichlet

end OAI
