import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.DyadCount
import OAI.Combinatorics.RamseyFive.Entropy.HighBudgetPoly

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

noncomputable def highPolyConstant (k c : ℝ) : ℝ :=
  403+40*k^2+20*k^4*(200*k+2)^2+k^4*(c+400*2^(200:ℕ))+2*k^200*c

lemma highPolyConstant_pos {k c : ℝ} (hk : 0≤k) (hc : 0≤c) : 0<highPolyConstant k c := by
  unfold highPolyConstant
  positivity

lemma highBudgetPoly_bound {σ E p P a k c : ℝ}
    (hσ : 1≤σ) (hE : 1≤E) (hp : 0≤p) (hphi : p≤k*σ)
    (hP : 0≤P) (hPhi : P≤σ) (ha : 0≤a) (hahi : a≤c*σ*E)
    (hk : 0≤k) (hc : 0≤c) :
    highBudgetPoly a p P≤highPolyConstant k c*σ^(205:ℕ)*E := by
  have hσ0 : 0≤σ := by linarith
  have hE0 : 0≤E := by linarith
  have hpow (j : ℕ) (hj : j≤205) : σ^j≤σ^(205:ℕ) := pow_le_pow_right₀ hσ hj
  have hpowE (j : ℕ) (hj : j≤205) : σ^j≤σ^(205:ℕ)*E :=
    (hpow j hj).trans (le_mul_of_one_le_right (pow_nonneg hσ0 _) hE)
  have h1 : 1≤σ^(205:ℕ)*E := by simpa using hpowE 0 (by omega)
  have hr : 40*p^2≤(40*k^2)*σ^(205:ℕ)*E := by
    calc
      _ ≤ 40*(k*σ)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hphi 2) (by norm_num)
      _ = (40*k^2)*σ^2 := by ring
      _ ≤ (40*k^2)*(σ^(205:ℕ)*E) := mul_le_mul_of_nonneg_left (hpowE 2 (by omega)) (by positivity)
      _ = _ := by ring
  have hbase : 200*p+2*P≤(200*k+2)*σ := by nlinarith
  have ht : 20*p^4*(200*p+2*P)^2≤(20*k^4*(200*k+2)^2)*σ^(205:ℕ)*E := by
    calc
      _ ≤ 20*(k*σ)^4*((200*k+2)*σ)^2 := by gcongr
      _ = (20*k^4*(200*k+2)^2)*σ^6 := by ring
      _ ≤ (20*k^4*(200*k+2)^2)*(σ^(205:ℕ)*E) :=
        mul_le_mul_of_nonneg_left (hpowE 6 (by omega)) (by positivity)
      _ = _ := by ring
  have hm : p^4*(P^200*a+400*(2*P)^200)≤
      (k^4*(c+400*2^(200:ℕ)))*σ^(205:ℕ)*E := by
    calc
      _ ≤ (k*σ)^4*(σ^200*(c*σ*E)+400*(2*σ)^200) := by
        apply mul_le_mul (pow_le_pow_left₀ hp hphi 4)
        · exact add_le_add
            (mul_le_mul (pow_le_pow_left₀ hP hPhi 200) hahi ha (pow_nonneg hσ0 _))
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg (by norm_num) hP)
                (mul_le_mul_of_nonneg_left hPhi (by norm_num)) 200) (by norm_num))
        · exact add_nonneg (mul_nonneg (pow_nonneg hP _) ha)
            (mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg (by norm_num) hP) _))
        · exact pow_nonneg (mul_nonneg hk hσ0) _
      _ = k^4*c*σ^(205:ℕ)*E+(400*k^4*2^(200:ℕ))*σ^(204:ℕ) := by ring
      _ ≤ k^4*c*σ^(205:ℕ)*E+(400*k^4*2^(200:ℕ))*(σ^(205:ℕ)*E) := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hpowE 204 (by omega))
          (show 0≤400*k^4*2^(200:ℕ) from mul_nonneg
            (mul_nonneg (by norm_num) (pow_nonneg hk _)) (pow_nonneg (by norm_num) _)))
      _ = _ := by ring
  have hs : 2*p^200*a≤(2*k^200*c)*σ^(205:ℕ)*E := by
    calc
      _ ≤ 2*(k*σ)^200*(c*σ*E) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hphi 200) (by norm_num)) hahi ha
        (mul_nonneg (by norm_num) (pow_nonneg (mul_nonneg hk hσ0) _))
      _ = (2*k^200*c)*σ^(201:ℕ)*E := by ring
      _ ≤ (2*k^200*c)*σ^(205:ℕ)*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpow 201 (by omega))
          (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hk _)) hc)) hE0
  unfold highBudgetPoly
  calc
    _ ≤ 3*(σ^(205:ℕ)*E)+(40*k^2)*σ^(205:ℕ)*E+
        (20*k^4*(200*k+2)^2)*σ^(205:ℕ)*E+
        (k^4*(c+400*2^(200:ℕ)))*σ^(205:ℕ)*E+
        (2*k^200*c)*σ^(205:ℕ)*E+400*(σ^(205:ℕ)*E) := by
      have h3 : (3:ℝ)≤3*(σ^(205:ℕ)*E) := by linarith
      have h400 : (400:ℝ)≤400*(σ^(205:ℕ)*E) := by linarith
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h3 hr) ht) hm) hs) h400
    _ = _ := by unfold highPolyConstant; ring

lemma dyadFactor_exp_bound {σ P : ℝ} {m : ℕ} (hσ : 1≤σ)
    (hm : (m:ℝ)≤Real.exp (3*σ)) :
    dyadFactor m (P/100)≤(8*2^(200:ℕ))*σ*Real.exp (P/50) := by
  unfold dyadFactor
  have hdy := dyad_count_le hσ hm
  rw [show (2:ℝ)*(P/100)=P/50 by ring]
  calc
    _ ≤ 2^(200:ℕ)*(8*σ)*Real.exp (P/50) := by gcongr
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry

end

end OAI
