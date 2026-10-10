import OAI.Combinatorics.SparsestCut.UniformMetric

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.RateComparison
open Filter
noncomputable section
def weight (x : ℝ) : ℝ := Real.sqrt x*(Real.log x)^2*Real.sqrt (Real.log x)
lemma weight_pos {d : ℕ} (hd : 0<d) (hl : 1≤Real.log d) : 0<weight d := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hl' : 0<Real.log d := by linarith
  unfold weight
  positivity
lemma logarithms {d n : ℕ} (hd : 0<d) (hl : 1≤Real.log d)
    (hnlo : d^d≤n) (hnhi : n≤d^(4030*d)) :
    0<Real.log n ∧ Real.log d≤Real.log (Real.log n) ∧
      Real.log n≤4030*(d:ℝ)*Real.log d := by
  have hx : (0:ℝ)<d := by exact_mod_cast hd
  have hlo : (d:ℝ)*Real.log d≤Real.log n := by
    calc
      _ = Real.log ((d:ℝ)^d) := (Real.log_pow _ _).symm
      _ ≤ _ := Real.log_le_log (by positivity) (by exact_mod_cast hnlo)
  have hdn : (d:ℝ)≤Real.log n := (le_mul_of_one_le_right hx.le hl).trans hlo
  have hn0 : 0<n := (pow_pos hd _).trans_le hnlo
  have hn0' : (0:ℝ)<n := by exact_mod_cast hn0
  refine ⟨hx.trans_le hdn,Real.log_le_log hx hdn,?_⟩
  calc
    _ ≤ Real.log ((d:ℝ)^(4030*d)) := Real.log_le_log hn0' (by exact_mod_cast hnhi)
    _ = _ := by rw [Real.log_pow]; push_cast; ring
lemma bound {d n : ℕ} (hd : 0<d) (hl : 1≤Real.log d)
    (hnlo : d^d≤n) (hnhi : n≤d^(4030*d)) :
    Real.sqrt (Real.log n)/(Real.log (Real.log n))^3≤Real.sqrt 4030*(d:ℝ)/weight d := by
  have hx : (0:ℝ)<d := by exact_mod_cast hd
  have hℓ : 0<Real.log d := by linarith
  obtain ⟨hn0,hll,hln⟩ := logarithms hd hl hnlo hnhi
  have hll0 : 0<Real.log (Real.log n) := hℓ.trans_le hll
  have hs : Real.sqrt (Real.log n)≤Real.sqrt 4030*Real.sqrt d*Real.sqrt (Real.log d) := by
    calc
      _ ≤ Real.sqrt (4030*(d:ℝ)*Real.log d) := Real.sqrt_le_sqrt hln
      _ = _ := by rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by norm_num)]
  apply (div_le_div_iff₀ (pow_pos hll0 _) (weight_pos hd hl)).mpr
  have hlim := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ.le hll 3)
    (mul_nonneg (Real.sqrt_nonneg 4030) hx.le)
  calc
    _ ≤ (Real.sqrt 4030*Real.sqrt d*Real.sqrt (Real.log d))*weight d :=
      mul_le_mul_of_nonneg_right hs (weight_pos hd hl).le
    _ = Real.sqrt 4030*(d:ℝ)*(Real.log d)^3 := by
      unfold weight
      calc
        _ = Real.sqrt 4030*(Real.sqrt d)^2*(Real.sqrt (Real.log d))^2*(Real.log d)^2 := by ring
        _ = _ := by rw [Real.sq_sqrt hx.le,Real.sq_sqrt hℓ.le]; ring
    _ ≤ _ := hlim
lemma gap_of_gl {d n : ℕ} (hd : 0<d) (hl : 1≤Real.log d)
    (hnlo : d^d≤n) (hnhi : n≤d^(4030*d))
    {α β opt gl : ℝ} (hα : 0<α) (hβ : 0<β) (hopt : 1≤opt) (hgl : 0<gl)
    (hbound : gl≤β*weight d/(α*(d:ℝ))) :
    (α/(β*Real.sqrt 4030))*Real.sqrt (Real.log n)/(Real.log (Real.log n))^3≤opt/gl := by
  have hx : (0:ℝ)<d := by exact_mod_cast hd
  have hw := weight_pos hd hl
  have hs : (0:ℝ)<Real.sqrt 4030 := by positivity
  have hr := bound hd hl hnlo hnhi
  have hconst : 0<α/(β*Real.sqrt 4030) := by positivity
  have hratio : α*(d:ℝ)/(β*weight d)≤opt/gl := by
    apply (div_le_div_iff₀ (mul_pos hβ hw) hgl).mpr
    have h := (le_div_iff₀ (mul_pos hα hx)).mp hbound
    have h' := mul_le_mul_of_nonneg_right hopt (mul_pos hβ hw).le
    nlinarith only [h,h']
  calc
    _ = (α/(β*Real.sqrt 4030))*(Real.sqrt (Real.log n)/(Real.log (Real.log n))^3) := by ring
    _ ≤ (α/(β*Real.sqrt 4030))*(Real.sqrt 4030*(d:ℝ)/weight d) :=
      mul_le_mul_of_nonneg_left hr hconst.le
    _ = α*(d:ℝ)/(β*weight d) := by field_simp
    _ ≤ _ := hratio
end
end UniformSparsestCut.RateComparison

end

end OAI
