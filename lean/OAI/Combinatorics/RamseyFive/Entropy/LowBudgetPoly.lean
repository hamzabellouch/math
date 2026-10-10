import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.HighPolyConstant

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open scoped BigOperators

noncomputable def lowBudgetPoly (a s p P : ℝ) : ℝ :=
  highBudgetPoly a p P+s*p^3*(200*p+2*P)

lemma lowMomentBudget_eq_high (Q M A B b L : ℝ) (p R N₁ N₂ : ℕ)
    (hB : B≠0) (hb : b≠0) : lowMomentBudget Q M A B b L p R N₁ N₂=
      highMomentBudget Q M A B b L p R N₂+
        B*((N₁:ℝ)/B)*(p:ℝ)^3*(200*p+2*((R:ℝ)*L)) := by
  unfold lowMomentBudget highMomentBudget certificateMajorant highCertificateMajorant
  push_cast
  field_simp [hB, hb]
  ring

lemma lowMomentBudget_le_poly (Q a s B b L : ℝ) (p R N₁ N₂ : ℕ)
    (hB : 1≤B) (hb : 0<b) (ha : 0≤a) (hL : 0≤L)
    (hroot : Q/(B*b^8)≤40) (hanchor : (N₂:ℝ)*b/B≤20) (hpair : Q/B^2≤400)
    (hone : (N₁:ℝ)/B ≤ s) :
    lowMomentBudget Q (a*B^2) (a*B) B b L p R N₁ N₂ ≤
      B*lowBudgetPoly a s p ((R:ℝ)*L) := by
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  rw [lowMomentBudget_eq_high _ _ _ _ _ _ _ _ _ _ hB0.ne' hb.ne']
  unfold lowBudgetPoly
  conv_rhs => rw [mul_add]
  apply add_le_add (highMomentBudget_le_poly Q a B b L p R N₂ hB hb ha hL hroot hanchor hpair)
  have hn := mul_le_mul_of_nonneg_left hone hB0.le
  have hp : 0≤(p:ℝ)^3*(200*p+2*((R:ℝ)*L)) := by positivity
  convert mul_le_mul_of_nonneg_right hn hp using 1 <;> ring

open Filter Asymptotics ParameterHierarchy
open scoped Topology

lemma lowBudgetPoly_bound {σ P p a s k c : ℝ} (hσ : 1≤σ)
    (hP : 0≤P) (hPhi : P≤σ) (hp : 0≤p) (hphi : p≤k*σ)
    (ha : 0≤a) (hahi : a≤c*σ*Real.exp (P/50))
    (hs : s≤4*Real.exp (P/10000)) (hk : 0≤k) (hc : 0≤c) :
    lowBudgetPoly a s p P≤(highPolyConstant k c+4*k^3*(200*k+2))*σ^205*Real.exp (P/50) := by
  have hσ0 : 0≤σ := by linarith
  have hhigh := highBudgetPoly_bound hσ (Real.one_le_exp_iff.mpr (by positivity : 0≤P/50))
    hp hphi hP hPhi ha hahi hk hc
  have hpow : σ^(4:ℕ)≤σ^(205:ℕ) := pow_le_pow_right₀ hσ (by norm_num)
  have hE : Real.exp (P/10000)≤Real.exp (P/50) := Real.exp_le_exp.mpr (by linarith)
  have hterm : s*p^3*(200*p+2*P)≤(4*k^3*(200*k+2))*σ^205*Real.exp (P/50) := by
    calc
      _ ≤ (4*Real.exp (P/10000))*(k*σ)^3*((200*k+2)*σ) := by
        apply mul_le_mul (mul_le_mul hs (pow_le_pow_left₀ hp hphi 3) (by positivity) (by positivity))
          (by nlinarith only [hphi,hPhi]) (by positivity) (by positivity)
      _ = (4*k^3*(200*k+2))*σ^4*Real.exp (P/10000) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hE
        (Real.exp_nonneg _) (by positivity)
  unfold lowBudgetPoly
  calc
    _ ≤ highPolyConstant k c*σ^205*Real.exp (P/50)+
        (4*k^3*(200*k+2))*σ^205*Real.exp (P/50) := add_le_add hhigh hterm
    _ = _ := by ring

theorem eventually_low_poly_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (k c : ℝ) (hk : 0≤k) (hc : 0≤c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R p a s : ℝ,Range η σ D R →
      0≤p → p≤k*σ → 0≤a → a≤c*σ*Real.exp (P η σ D R/50) →
      s≤4*Real.exp (P η σ D R/10000) →
      Real.exp (P η σ D R/50)+2*(p+1)*lowBudgetPoly a s p (P η σ D R)≤
        Real.exp (P η σ D R/5) := by
  let C := highPolyConstant k c+4*k^3*(200*k+2)
  have hC : 0<C := add_pos_of_pos_of_nonneg (highPolyConstant_pos hk hc) (by positivity)
  have hK : 0<1+2*(k+1)*C := by positivity
  have hab := eventually_power_absorption hη hη' (1+2*(k+1)*C) 206 (1/10)
    hK (by norm_num) (by norm_num)
  have hs := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hs] with σ hσ hab hs
  intro D R p a s hr hp hphi ha hahi hsi
  have hpar := finite_bounds hη hη' hσ hr
  have hP : 0≤P η σ D R := (Real.rpow_nonneg (by linarith) _).trans hpar.2.2.2.2.2.1
  have hPhi : P η σ D R≤σ := by
    have hh := hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hpol := lowBudgetPoly_bound hσ hP hPhi hp hphi ha hahi hsi hk hc
  have hcoef : 1+2*(p+1)*C*σ^(205:ℕ)≤(1+2*(k+1)*C)*σ^(206:ℕ) := by
    have hh : p+1≤(k+1)*σ := by nlinarith
    have h1 : 1≤σ^(206:ℕ) := one_le_pow₀ hσ
    calc
      _ ≤ σ^(206:ℕ)+2*((k+1)*σ)*C*σ^(205:ℕ) := by gcongr
      _ = _ := by rw [show σ^(206:ℕ)=σ^205*σ from pow_succ σ 205]; ring
  have hh : (1+2*(k+1)*C)*σ^(206:ℕ)≤Real.exp (P η σ D R/10) := by
    have ht := hab D R hr
    rw [show σ^(206:ℝ)=σ^(206:ℕ) from Real.rpow_natCast σ 206] at ht
    simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using ht
  calc
    _ ≤ Real.exp (P η σ D R/50)+2*(p+1)*(C*σ^(205:ℕ)*Real.exp (P η σ D R/50)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpol (by positivity))
    _ = (1+2*(p+1)*C*σ^(205:ℕ))*Real.exp (P η σ D R/50) := by ring
    _ ≤ Real.exp (P η σ D R/10)*Real.exp (P η σ D R/50) :=
      mul_le_mul_of_nonneg_right (hcoef.trans hh) (Real.exp_nonneg _)
    _ = Real.exp (P η σ D R/10+P η σ D R/50) := (Real.exp_add ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end SharpRamseyFive.ScoreGeometry

end

end OAI
