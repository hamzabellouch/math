import OAI.Probability.EntangledGames.TestExtraction

namespace OAI

noncomputable section
namespace ThresholdParallelRepetition

lemma power_ratio_bound {v δ : ℝ} (hv : 0 ≤ v) (hδ : 0 < δ) (hs : v+δ ≤ 1) (T : ℕ) :
    (v+δ/2)^T/(v+δ)^T ≤ Real.exp (-(δ*(T : ℝ)/2)) := by
  have hs0 : 0 < v+δ := by linarith
  have hr0 : 0 ≤ (v+δ/2)/(v+δ) := div_nonneg (by linarith) hs0.le
  have hr : (v+δ/2)/(v+δ) ≤ Real.exp (-δ/2) := by
    have he := Real.add_one_le_exp (-δ/2)
    have hratio : (v+δ/2)/(v+δ) ≤ 1-δ/2 := by
      apply (div_le_iff₀ hs0).mpr
      nlinarith
    linarith
  rw [← div_pow]
  have hh := pow_le_pow_left₀ hr0 hr T
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans_eq (by congr 1; ring)

lemma inverse_power_bound {s δ : ℝ} (hδ : 0 < δ) (hs : δ ≤ s) (T : ℕ) :
    1/s^T ≤ Real.exp ((T : ℝ)/δ) := by
  have hs0 : 0 < s := hδ.trans_le hs
  have hh := Real.log_le_sub_one_of_pos (one_div_pos.mpr hδ)
  rw [one_div, Real.log_inv] at hh
  have hlog := Real.log_le_log hδ hs
  have hl : -Real.log s ≤ 1/δ := by simpa only [one_div] using (show -Real.log s ≤ δ⁻¹ by linarith)
  have hpow := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg T : (0:ℝ) ≤ T)
  have he : 1/s^T = Real.exp (-(T : ℝ)*Real.log s) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hs0, one_div]
  rw [he]
  apply Real.exp_le_exp.mpr
  simpa only [mul_neg, neg_mul, div_eq_mul_inv, one_mul] using hpow

end ThresholdParallelRepetition

end

noncomputable section
namespace ThresholdParallelRepetition

lemma analytic_threshold_bound {v δ θ R E q : ℝ}
    (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : v+δ ≤ 1)
    (hθ : 2 ≤ θ) (hδθ : 8 ≤ δ*θ)
    (hθR : θ/δ ≤ R/4) (hR : 2/δ ≤ R/4) (hE : E ≤ δ*θ/8)
    (hq : q*(v+δ)^(⌊θ⌋₊) ≤ (v+δ/2)^(⌊θ⌋₊)+Real.exp (-R)*(2/δ)) :
    q ≤ Real.exp (-E) := by
  let T := ⌊θ⌋₊
  let L := δ*θ/4
  have hθ0 : 0 ≤ θ := by linarith
  have hT : (T : ℝ) ≤ θ := Nat.floor_le hθ0
  have hT' : θ/2 ≤ (T : ℝ) := by
    have hh := Nat.lt_floor_add_one θ
    dsimp [T]; linarith
  have hs0 : 0 < v+δ := by linarith
  have hp0 : 0 < (v+δ)^T := pow_pos hs0 _
  have hq' : q ≤ (v+δ/2)^T/(v+δ)^T + Real.exp (-R)*(2/δ)/(v+δ)^T := by
    rw [← add_div]
    exact (le_div_iff₀ hp0).mpr hq
  have hfirst : (v+δ/2)^T/(v+δ)^T ≤ Real.exp (-L) := by
    apply (power_ratio_bound hv hδ hs T).trans
    apply Real.exp_le_exp.mpr
    dsimp [L]
    nlinarith
  have hTδ : (T : ℝ)/δ ≤ R/4 := (div_le_div_of_nonneg_right hT hδ.le).trans hθR
  have hfac : 2/δ ≤ Real.exp (2/δ) := by linarith [Real.add_one_le_exp (2/δ)]
  have hbad : Real.exp (-R)*(2/δ)/(v+δ)^T ≤ Real.exp (-R/2) := by
    calc
      Real.exp (-R)*(2/δ)/(v+δ)^T = Real.exp (-R)*(2/δ)*(1/(v+δ)^T) := by ring
      _ ≤ Real.exp (-R)*Real.exp (2/δ)*Real.exp ((T : ℝ)/δ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hfac (Real.exp_pos _).le
        · exact inverse_power_bound hδ (by linarith) T
        · positivity
        · positivity
      _ = Real.exp (-R+2/δ+(T : ℝ)/δ) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-R/2) := Real.exp_le_exp.mpr (by linarith)
  have hδ2 : δ*δ ≤ 1 := by nlinarith
  have hL : L ≤ R/2 := by
    have hh : δ*θ ≤ θ/δ := by
      apply (le_div_iff₀ hδ).mpr
      nlinarith [mul_le_mul_of_nonneg_right hδ2 hθ0]
    have hR0 : 0 < R := by have := div_pos (show (0:ℝ)<2 by norm_num) hδ; linarith
    dsimp [L]; linarith
  have hqL : q ≤ 2*Real.exp (-L) := by
    have hb : Real.exp (-R)*(2/δ)/(v+δ)^T ≤ Real.exp (-L) :=
      hbad.trans (Real.exp_le_exp.mpr (by linarith))
    linarith
  have htwo : 2 ≤ Real.exp (L/2) := by
    have hh := Real.add_one_le_exp (L/2)
    dsimp [L] at *
    linarith
  calc
    q ≤ 2*Real.exp (-L) := hqL
    _ ≤ Real.exp (L/2)*Real.exp (-L) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-L/2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-E) := by apply Real.exp_le_exp.mpr; dsimp [L]; linarith

lemma large_rate_parameters {δ k D : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 0 < k) (hD : 1 ≤ D) (hbig : (2:ℝ)^100*D ≤ δ^12*k) :
    2 ≤ δ^9*k/((2:ℝ)^90*D) ∧
    8 ≤ δ*(δ^9*k/((2:ℝ)^90*D)) ∧
    (δ^9*k/((2:ℝ)^90*D))/δ ≤ (δ^8*k/(2:ℝ)^83)/4 ∧
    2/δ ≤ (δ^8*k/(2:ℝ)^83)/4 ∧
    δ^13*k/((2:ℝ)^101*D) ≤ δ*(δ^9*k/((2:ℝ)^90*D))/8 := by
  have hD0 : 0 < D := by linarith
  have hden : 0 < (2:ℝ)^90*D := by positivity
  have h129 : δ^12 ≤ δ^9 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h1210 : δ^12 ≤ δ^10 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h1310 : δ^13 ≤ δ^10 := pow_le_pow_of_le_one hδ.le hδ1 (by omega)
  have h129k := mul_le_mul_of_nonneg_right h129 hk.le
  have h1210k := mul_le_mul_of_nonneg_right h1210 hk.le
  have h1310k := mul_le_mul_of_nonneg_right h1310 hk.le
  have h8k : 0 ≤ δ^8*k := by positivity
  have h10k : 0 ≤ δ^10*k := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hD h8k
    nlinarith
  · apply (div_le_iff₀ hδ).mpr
    nlinarith
  · rw [← mul_div_assoc, div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (2:ℝ)^101*D) (by positivity : 0 < (2:ℝ)^90*D*8)).mpr
    have hh := mul_le_mul_of_nonneg_right h1310k hD0.le
    nlinarith [mul_nonneg h10k hD0.le]

end ThresholdParallelRepetition

end

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace ThresholdParallelRepetition
open QuantumSampling FiniteProbability Law MixedExposure
namespace RepeatedModel
variable {I m n : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype m] [DecidableEq m] [Nonempty m] [Fintype n] [DecidableEq n] [Nonempty n]
  {x y a b : ℕ} (G : Game x y a b)
  (M : RepeatedModel (Fin (x+1)) (Fin (y+1)) (Fin (a+1)) (Fin (b+1)) I m n)
  (hμ : M.μ = G.questionLaw) (hV : M.V = G.accepts)
include hμ hV

lemma threshold_exp_bound {δ : ℝ} (hδ : 0 < δ) (hs : entangledValue G+δ ≤ 1) :
    Tests.threshold M.joint M.winsAt (entangledValue G+δ) ≤
      Real.exp (-(δ^13*(Fintype.card I : ℝ)/((2:ℝ)^101*(1+Real.log (((a+1)*(b+1) : ℕ) : ℝ))))) := by
  let D : ℝ := 1+Real.log (((a+1)*(b+1) : ℕ) : ℝ)
  let k : ℝ := Fintype.card I
  let θ : ℝ := δ^9*k/((2:ℝ)^90*D)
  let R : ℝ := δ^8*k/(2:ℝ)^83
  let E : ℝ := δ^13*k/((2:ℝ)^101*D)
  have hd : (1:ℝ) ≤ (((a+1)*(b+1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
  have hD : 1 ≤ D := by dsimp [D]; linarith [Real.log_nonneg hd]
  have hD0 : 0 < D := by linarith
  have hk : 0 < k := by dsimp [k]; exact_mod_cast Fintype.card_pos (α := I)
  have hv := entangledValue_nonneg G
  have hδ1 : δ ≤ 1 := by linarith
  change _ ≤ Real.exp (-E)
  by_cases hsmall : δ^12*k ≤ (2:ℝ)^100*D
  · apply (M.threshold_mean_bound G hμ hV hδ hs).trans
    apply Real.exp_le_exp.mpr
    suffices E ≤ δ by linarith
    dsimp [E]
    apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^101*D)).mpr
    have hh := mul_le_mul_of_nonneg_left hsmall hδ.le
    nlinarith [mul_nonneg hδ.le hD0.le]
  · obtain ⟨hθ,hδθ,hθR,hR,hE⟩ := large_rate_parameters hδ hδ1 hk hD (le_of_not_ge hsmall)
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have htest := M.threshold_power_bound G hμ hV hδ hs ⌊θ⌋₊ (Nat.floor_le hθ0)
    exact analytic_threshold_bound hv hδ hδ1 hs hθ hδθ hθR hR hE htest

end RepeatedModel
end ThresholdParallelRepetition

end

end OAI
