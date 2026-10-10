import OAI.NumberTheory.DukePrimeDegree.Geometry.ControlledDistanceCuts

namespace OAI

/-! # Size bounds for the explicit quotient distance cuts -/

noncomputable section
namespace DukePrimeDegree

lemma quotientNetBound_le_power {n : ℕ} (hn : 0 < n)
    {R s : ℝ} (hR : 0 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1) :
    quotientNetBound n R s ≤
      (192*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/s)^(n*n) := by
  let E := Real.exp (R+1)
  have hE : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp_iff.mpr (by linarith)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have h4 : (1:ℝ) ≤ 4*(n:ℝ)*E := by nlinarith
  have h12 : (1:ℝ) ≤ 12*(n:ℝ) := by linarith
  have hmin : s/(12*(n:ℝ))/(4*(n:ℝ)*E) ≤ 1 :=
    ((div_le_self (by positivity) h4).trans (div_le_self hs.le h12)).trans hs1
  change (2*E+2)^(n*n)/(min 1 (s/(12*(n:ℝ))/(4*(n:ℝ)*E)))^(n*n) ≤ _
  rw [min_eq_right hmin,←div_pow]
  have heq : (2*E+2)/(s/(12*(n:ℝ))/(4*(n:ℝ)*E)) =
      48*(n:ℝ)*(n:ℝ)*E*(2*E+2)/s := by
    field_simp
    ring
  have he2 : E*E=Real.exp (2*(R+1)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  apply pow_le_pow_left₀ (by positivity)
  rw [heq]
  apply div_le_div_of_nonneg_right _ hs.le
  calc
    _ ≤ 48*(n:ℝ)*(n:ℝ)*E*(4*E) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by rw [←he2]; ring

lemma half_le_log_one_add {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r/2 ≤ Real.log (1+r) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hr)
  apply (le_div_iff₀ (by linarith : 0 < r+2)).mpr
  nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]

theorem distanceCut_size_bound {n : ℕ} (hn : 0 < n)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    quotientNetBound n R (Real.log (1+r)/4) * (48/Real.log (1+r)) ≤
      (1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/r)^(n*n) * (96/r) := by
  let τ := Real.log (1+r)
  have hτ : 0 < τ := Real.log_pos (by linarith)
  have hτlow : r/2 ≤ τ := half_le_log_one_add hr.le hr1
  have hτhi : τ ≤ r := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1+r by linarith)
    dsimp [τ]
    linarith
  have hnet := quotientNetBound_le_power hn hR (by positivity : 0 < τ/4)
    (show τ/4 ≤ 1 by linarith)
  have hb : 192*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/(τ/4) ≤
      1536*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1))/r := by
    apply (div_le_div_iff₀ (by positivity) hr).mpr
    have hp : 0 ≤ 384*(n:ℝ)*(n:ℝ)*Real.exp (2*(R+1)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hτlow hp]
  have hc : 48/τ ≤ 96/r := by
    apply (div_le_div_iff₀ hτ hr).mpr
    linarith
  exact mul_le_mul (hnet.trans (pow_le_pow_left₀ (by positivity) hb _)) hc
    (by positivity) (by positivity)

end DukePrimeDegree

end

end OAI
