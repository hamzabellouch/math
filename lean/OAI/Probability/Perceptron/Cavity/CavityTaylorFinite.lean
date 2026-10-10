import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkModel
import OAI.Probability.Perceptron.Variational.DilationExpansion
import OAI.Probability.Perceptron.Brownian.CavityGaussianFields

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators

def cavityTaylorError (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (N L q v : ℝ) : ℝ :=
  let t:=Real.log (Real.sqrt (1-q/(N+L)))
  let u:=v/Real.sqrt (N+L)
  (‖weightedDerivative g.d1 h1 1‖+‖weightedDerivative g.d2 h2 2‖)*t^2/2+
      ‖weightedDerivative g.d2 h2 1‖*|t| * |u|+
      ‖weightedDerivative g.d3 h3 1‖*|t| * u^2/2+‖g.d3‖*|u| ^3/6+
      |t+q/(2*N)| * ‖weightedDerivative g.d1 h1 1‖+
      |v/Real.sqrt (N+L)-v/Real.sqrt N| * ‖g.d1‖+
      |(v/Real.sqrt (N+L))^2/2-v^2/(2*N)| * ‖g.d2‖

lemma Jet3.cavity_finite_expansion (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ)) (N L q s v : ℝ)
    (hρ : 0<1-q/(N+L)) :
    |g.f (Real.sqrt (1-q/(N+L))*s+v/Real.sqrt (N+L))-g.f s-
      (v/Real.sqrt N*g.d1 s+q/(2*N)*(g.d2 s-s*g.d1 s)+
        1/(2*N)*g.d2 s*(v^2-q))|≤cavityTaylorError g h1 h2 h3 N L q v := by
  let t:=Real.log (Real.sqrt (1-q/(N+L)))
  let u:=v/Real.sqrt (N+L)
  have he : Real.exp t=Real.sqrt (1-q/(N+L)) := Real.exp_log (Real.sqrt_pos.mpr hρ)
  have ht:=g.cavity_log_dilation_expansion h1 h2 h3 s t u
  rw [he] at ht
  have hlin : |(t+q/(2*N))*(s*g.d1 s)|≤|t+q/(2*N)| * ‖weightedDerivative g.d1 h1 1‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using weightedDerivative_bound g.d1 h1 1 s) (abs_nonneg _)
  have hshift : |(u-v/Real.sqrt N)*g.d1 s|≤|u-v/Real.sqrt N| * ‖g.d1‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (g.d1.norm_coe_le_norm s) (abs_nonneg _)
  have hquad : |(u^2/2-v^2/(2*N))*g.d2 s|≤|u^2/2-v^2/(2*N)| * ‖g.d2‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (g.d2.norm_coe_le_norm s) (abs_nonneg _)
  calc
    _=|(g.f (Real.sqrt (1-q/(N+L))*s+u)-g.f s-t*s*g.d1 s-u*g.d1 s-u^2/2*g.d2 s)+
      (t+q/(2*N))*(s*g.d1 s)+(u-v/Real.sqrt N)*g.d1 s+
        (u^2/2-v^2/(2*N))*g.d2 s| := by dsimp [u]; congr 1; ring
    _≤|g.f (Real.sqrt (1-q/(N+L))*s+u)-g.f s-t*s*g.d1 s-u*g.d1 s-u^2/2*g.d2 s|+
      |(t+q/(2*N))*(s*g.d1 s)|+|(u-v/Real.sqrt N)*g.d1 s|+
      |(u^2/2-v^2/(2*N))*g.d2 s| := by
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _≤_ := add_le_add (add_le_add (add_le_add ht hlin) hshift) hquad

theorem cavity_pattern_sum_expansion (n M L : ℕ) (g : Jet3)
    (h1 : HasCompactSupport (g.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (g.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (g.d3 : ℝ→ℝ))
    (a : Fin M→Fin (n+1)→ℝ) (x : NormalizedSpin (n+1)) (z : Spin L)
    (y : Fin M→Spin L) (hρ : ‖z‖^2<(n+1:ℕ)+L) :
    |(∑ i,g.f (Real.sqrt (1-‖z‖^2/((n+1:ℕ)+L))*(∑ j,a i j*x.val j)+
        inner ℝ z (y i)/Real.sqrt ((n+1:ℕ)+L)))-
      normalizedPatternEnergy (n+1) M g.f a x-
      (cavityLinearField M L (fun i=>g.d1 (∑ j,a i j*x.val j))
          (Real.sqrt (n+1:ℕ))⁻¹ z y+
        ‖z‖^2/2*bulkC (n+1) M g a x+
        cavityQuadraticField M L (fun i=>g.d2 (∑ j,a i j*x.val j))
          (1/(2*(n+1:ℕ))) z y)|≤
      ∑ i,cavityTaylorError g h1 h2 h3 (n+1:ℕ) L (‖z‖^2) (inner ℝ z (y i)) := by
  have hp : (0:ℝ)<((n+1:ℕ):ℝ)+L := by positivity
  have hr : 0<1-‖z‖^2/((n+1:ℕ)+L) := sub_pos.mpr ((div_lt_one hp).mpr hρ)
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    g.cavity_finite_expansion h1 h2 h3 (n+1:ℕ) L (‖z‖^2)
      (∑ j,a i j*x.val j) (inner ℝ z (y i)) hr)
  have he : cavityLinearField M L (fun i=>g.d1 (∑ j,a i j*x.val j))
          (Real.sqrt (n+1:ℕ))⁻¹ z y+
        ‖z‖^2/2*bulkC (n+1) M g a x+
        cavityQuadraticField M L (fun i=>g.d2 (∑ j,a i j*x.val j))
          (1/(2*(n+1:ℕ))) z y =
      ∑ i, (inner ℝ z (y i)/Real.sqrt (n+1:ℕ)*g.d1 (∑ j,a i j*x.val j)+
        ‖z‖^2/(2*(n+1:ℕ))*(g.d2 (∑ j,a i j*x.val j)-
          (∑ j,a i j*x.val j)*g.d1 (∑ j,a i j*x.val j))+
        1/(2*(n+1:ℕ))*g.d2 (∑ j,a i j*x.val j)*((inner ℝ z (y i))^2-‖z‖^2)) := by
    unfold cavityLinearField cavityQuadraticField bulkC
    simp only [←mul_assoc,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  unfold normalizedPatternEnergy
  rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans hs

lemma cavity_log_small {x : ℝ} (hx : 0≤x) (hx' : x≤1/2) :
    |Real.log (1-x)|≤2*x ∧ |Real.log (1-x)+x|≤2*x^2 := by
  have ha : |x|<1 := by rw [abs_of_nonneg hx]; linarith
  have h₀:=Real.abs_log_sub_add_sum_range_le ha 0
  have h₁:=Real.abs_log_sub_add_sum_range_le ha 1
  simp only [Finset.range_zero,Finset.sum_empty,zero_add,pow_one,abs_of_nonneg hx] at h₀
  simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
    zero_add,Nat.cast_zero,pow_one,div_one,abs_of_nonneg hx] at h₁
  constructor
  · apply h₀.trans
    apply (div_le_iff₀ (by linarith : 0<1-x)).mpr
    nlinarith
  · apply (by simpa only [add_comm] using h₁ : |Real.log (1-x)+x|≤x^2/(1-x)).trans
    apply (div_le_iff₀ (by linarith : 0<1-x)).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (show 0≤1-2*x by linarith)]

lemma cavity_scale_log_bounds {N L D q : ℝ} (hN : 0<N) (hL : 0≤L)
    (hD : 0≤D) (hDN : 2*D≤N) (hq : 0≤q) (hqD : q≤D) :
    |Real.log (Real.sqrt (1-q/(N+L)))|≤D/N ∧
    |Real.log (Real.sqrt (1-q/(N+L)))+q/(2*N)|≤(D^2+D*L/2)/N^2 := by
  have hNL : 0<N+L := by linarith
  have hx : 0≤q/(N+L) := div_nonneg hq hNL.le
  have hx' : q/(N+L)≤1/2 := (div_le_iff₀ hNL).mpr (by linarith)
  have hxN : q/(N+L)≤D/N := by
    apply (div_le_div_of_nonneg_right hqD hNL.le).trans
    exact div_le_div_of_nonneg_left hD hN (by linarith)
  have hb:=cavity_log_small hx hx'
  have hp : 0≤1-q/(N+L) := by linarith
  rw [Real.log_sqrt hp]
  constructor
  · rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (div_le_div_of_nonneg_right hb.1 (by norm_num)).trans (by linarith)
  · have he : Real.log (1-q/(N+L))/2+q/(2*N)=
        (Real.log (1-q/(N+L))+q/(N+L))/2+q*L/(2*N*(N+L)) := by
        field_simp
        ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (by positivity : 0≤q*L/(2*N*(N+L)))]
    have ht : |Real.log (1-q/(N+L))+q/(N+L)|/2≤(D/N)^2 :=
      (div_le_div_of_nonneg_right hb.2 (by norm_num)).trans (by
        have hh:=pow_le_pow_left₀ hx hxN 2
        nlinarith)
    have hc : q*L/(2*N*(N+L))≤D*L/(2*N^2) := by
      apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqD hL) (by positivity)).trans
      exact div_le_div_of_nonneg_left (mul_nonneg hD hL) (by positivity)
        (by nlinarith)
    calc
      _≤(D/N)^2+D*L/(2*N^2) := add_le_add ht hc
      _=_ := by ring

lemma cavity_inv_sqrt_difference {N L : ℝ} (hN : 0<N) (hL : 0≤L) :
    |(Real.sqrt (N+L))⁻¹-(Real.sqrt N)⁻¹|≤L/(N*Real.sqrt N) := by
  have hNL : 0<N+L := by linarith
  have ha:=Real.sqrt_pos.mpr hN
  have hb:=Real.sqrt_pos.mpr hNL
  have hab : Real.sqrt N≤Real.sqrt (N+L) := Real.sqrt_le_sqrt (by linarith)
  have he : |(Real.sqrt (N+L))⁻¹-(Real.sqrt N)⁻¹|=
      L/(Real.sqrt N*Real.sqrt (N+L)*(Real.sqrt N+Real.sqrt (N+L))) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ ha hab))]
    apply (eq_div_iff (by positivity : Real.sqrt N*Real.sqrt (N+L)*(Real.sqrt N+Real.sqrt (N+L))≠0)).mpr
    field_simp
    nlinarith [Real.sq_sqrt hN.le,Real.sq_sqrt hNL.le]
  rw [he]
  apply div_le_div_of_nonneg_left hL (by positivity)
  calc
    N*Real.sqrt N=(Real.sqrt N*Real.sqrt N)*Real.sqrt N := by rw [←pow_two,Real.sq_sqrt hN.le]
    _≤(Real.sqrt N*Real.sqrt (N+L))*(Real.sqrt N+Real.sqrt (N+L)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hab ha.le) (by linarith) ha.le (by positivity)

lemma cavity_shift_difference {N L v : ℝ} (hN : 0<N) (hL : 0≤L) :
    |v/Real.sqrt (N+L)-v/Real.sqrt N|≤|v| * L/(N*Real.sqrt N) := by
  rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (cavity_inv_sqrt_difference hN hL) (abs_nonneg v)

lemma cavity_square_shift_difference {N L v : ℝ} (hN : 0<N) (hL : 0≤L) :
    |(v/Real.sqrt (N+L))^2/2-v^2/(2*N)|≤v^2*L/(2*N^2) := by
  have hNL : 0<N+L := by linarith
  rw [div_pow,Real.sq_sqrt hNL.le]
  have he : v^2/(N+L)/2-v^2/(2*N)= -(v^2*L/(2*N*(N+L))) := by field_simp; ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

end SphericalPerceptronFreeEnergy
end

end OAI
