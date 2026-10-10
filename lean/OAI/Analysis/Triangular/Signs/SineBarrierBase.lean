import OAI.Analysis.Triangular.Certificate.WaveIntervals

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set Filter
namespace AtomicTriangular.Construction

def sinePolynomial (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040+x^9/362880-x^11/39916800
lemma sinePolynomial_lower {x : ℝ} (hx : 0≤x) (hx2 : x≤2) : sinePolynomial x≤Real.sin x := by
  have ha : Antitone (fun j : ℕ => x^(2*j+1)/((2*j+1).factorial:ℝ)) := by
    apply antitone_nat_of_succ_le
    intro j
    have hf : (0:ℝ)<((2*j+1).factorial:ℝ) := by positivity
    have hn : (0:ℝ)<(2*j+2:ℕ)*(2*j+3:ℕ) := by positivity
    have hd : (((2*(j+1)+1).factorial:ℕ):ℝ) = ((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ)*((2*j+1).factorial:ℝ) := by
      rw [show 2*(j+1)+1=(2*j+1)+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
      push_cast
      ring
    rw [hd,show 2*(j+1)+1=2*j+1+2 by omega,pow_add]
    apply (div_le_div_iff₀ (by positivity) hf).mpr
    have hb : x^2≤((2*j+3:ℕ):ℝ)*((2*j+2:ℕ):ℝ) := by
      have hj : (0:ℝ)≤j := Nat.cast_nonneg j
      push_cast
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg (pow_nonneg hx (2*j+1)) hf.le)
    nlinarith
  have ht : Tendsto (fun n : ℕ => ∑ j ∈ range n, (-1:ℝ)^j*(x^(2*j+1)/((2*j+1).factorial:ℝ))) atTop (nhds (Real.sin x)) := by
    simpa only [mul_div_assoc] using (Real.hasSum_sin x).tendsto_sum_nat
  have hh := ha.alternating_series_le_tendsto ht 3
  norm_num [sum_range_succ,sinePolynomial] at hh ⊢
  linarith

def piLow : ℚ := 314159265358979/100000000000000
def piHigh : ℚ := 15707963267949/5000000000000
lemma sine_pi_bounds : (piLow:ℝ)≤Real.pi ∧ Real.pi≤(piHigh:ℝ) := by
  rcases AtomicTriangular.Constants.pStar_bracket with ⟨h1,h2⟩
  constructor
  · have hh : (piLow:ℝ)≤AtomicTriangular.Constants.pStar := by norm_num [piLow,AtomicTriangular.Constants.pStar]
    exact hh.trans h1.le
  · have hh : AtomicTriangular.Constants.pStar+AtomicTriangular.Constants.eps≤(piHigh:ℝ) := by norm_num [piHigh,AtomicTriangular.Constants.pStar,AtomicTriangular.Constants.eps]
    exact h2.le.trans hh

def sineLower (d : ℚ) : ℚ :=
  let l:=piLow*d/36
  let u:=piHigh*d/36
  2*(l-u^3/6+l^5/120-u^7/5040+l^9/362880-u^11/39916800)
lemma sine_lower {d : ℚ} (hd : 0≤d) (hd18 : d≤18) :
    (sineLower d:ℝ)≤2*Real.sin (Real.pi*d/36) := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hd18' : (d:ℝ)≤18 := by exact_mod_cast hd18
  have hl : 0≤(piLow:ℝ)*d/36 := by
    have : (0:ℝ)≤piLow := by norm_num [piLow]
    positivity
  have hlay : (piLow:ℝ)*d/36≤Real.pi*d/36 := by nlinarith [sine_pi_bounds.1]
  have huay : Real.pi*d/36≤(piHigh:ℝ)*d/36 := by nlinarith [sine_pi_bounds.2]
  have hx : 0≤Real.pi*d/36 := by positivity
  have hx2 : Real.pi*d/36≤2 := by nlinarith [Real.pi_lt_four]
  have hs := sinePolynomial_lower hx hx2
  have h3 := pow_le_pow_left₀ hx huay 3
  have h5 := pow_le_pow_left₀ hl hlay 5
  have h7 := pow_le_pow_left₀ hx huay 7
  have h9 := pow_le_pow_left₀ hl hlay 9
  have h11 := pow_le_pow_left₀ hx huay 11
  unfold sineLower
  push_cast
  unfold sinePolynomial at hs
  linarith
lemma sine_arc_lower {d : ℚ} {t : ℝ} (hd : 0≤d) (hd18 : d≤18)
    (ht : t∈Icc (d:ℝ) (36-d)) : (sineLower d:ℝ)≤2*|Real.sin (Real.pi*t/36)| := by
  have hd0 : (0:ℝ)≤d := by exact_mod_cast hd
  have hx0 : 0≤Real.pi*d/36 := by positivity
  have hleft : -(Real.pi/2)≤Real.pi*d/36 := (neg_nonpos.mpr (by positivity)).trans hx0
  have hmon : Real.sin (Real.pi*d/36)≤Real.sin (Real.pi*t/36) := by
    by_cases h : t≤18
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.1])
    · rw [show Real.pi*t/36=Real.pi-(Real.pi*(36-t)/36) by ring,Real.sin_pi_sub]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two hleft (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos,ht.2])
  linarith [sine_lower hd hd18,le_abs_self (Real.sin (Real.pi*t/36))]

def vanishingLower (v : ℚ) : ℚ := 2*(piLow/36-(piHigh/36)^3*v^2/6)
lemma sine_vanishing_lower {v : ℚ} {u : ℝ} (hv : 0≤v) (hv3 : v≤3) (hu : |u|≤v) :
    (vanishingLower v:ℝ)*|u|≤2*|Real.sin (Real.pi*u/36)| := by
  have hv0 : (0:ℝ)≤v := by exact_mod_cast hv
  have hv3' : (v:ℝ)≤3 := by exact_mod_cast hv3
  have hp0 : (0:ℝ)≤piHigh := by norm_num [piHigh]
  have hx : 0≤Real.pi*|u|/36 := by positivity
  have hl : (piLow:ℝ)/36*|u|≤Real.pi*|u|/36 := by nlinarith [sine_pi_bounds.1,abs_nonneg u]
  have hq : (Real.pi/36)^3≤((piHigh:ℝ)/36)^3 := pow_le_pow_left₀ (by positivity) (by linarith [sine_pi_bounds.2]) 3
  have hu2 : |u|^2≤(v:ℝ)^2 := (sq_le_sq₀ (abs_nonneg u) hv0).mpr hu
  have hc : (Real.pi*|u|/36)^3≤((piHigh:ℝ)/36)^3*(v:ℝ)^2*|u| := by
    have h1 := mul_le_mul_of_nonneg_right hq (pow_nonneg (abs_nonneg u) 3)
    have h2 := mul_le_mul_of_nonneg_left hu2 (mul_nonneg (pow_nonneg (by positivity : 0≤(piHigh:ℝ)/36) 3) (abs_nonneg u))
    nlinarith
  have hs := Real.sin_ge_sub_cube hx
  have he : |Real.sin (Real.pi*u/36)|=Real.sin (Real.pi*|u|/36) := by
    have hb : |Real.pi*u/36|≤Real.pi := by
      rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
      nlinarith [Real.pi_pos]
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hb,abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<36)]
  rw [he]
  unfold vanishingLower
  push_cast
  linarith
end AtomicTriangular.Construction
end

end OAI
