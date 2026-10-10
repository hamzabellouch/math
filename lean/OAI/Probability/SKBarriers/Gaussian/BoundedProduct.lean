import Mathlib

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem unitBoundedProduct_abs_le {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) : |a*b|≤1 := by
  rw [abs_mul]
  calc
    _ ≤ 1*1 := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
    _ = _ := by ring

theorem unitBoundedProduct_sub {a b c d : ℝ} (hb : |b|≤1) (hc : |c|≤1) :
    |a*b-c*d|≤|a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| * |b|+|c| * |b-d| := by rw [abs_mul,abs_mul]
    _ ≤ |a-c| * 1+1*|b-d| := add_le_add
      (mul_le_mul_of_nonneg_left hb (abs_nonneg _)) (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

theorem unitBoundedProduct_lipschitz {f g : ℝ → ℝ} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfb : ∀ x,|f x|≤1) (hgb : ∀ x,|g x|≤1) :
    LipschitzWith (K+L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have H := unitBoundedProduct_sub (a:=f x) (d:=g y) (hgb x) (hfb y)
  have Hf := hf.dist_le_mul x y
  have Hg := hg.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_add] at Hf Hg ⊢
  nlinarith

theorem unitBoundedProduct_tendstoUniformly {F G : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hG : ∀ n x,|G n x|≤1) (hf : ∀ x,|f x|≤1)
    (hF : TendstoUniformly F f atTop) (hU : TendstoUniformly G g atTop) :
    TendstoUniformly (fun n x => F n x*G n x) (fun x => f x*g x) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hF (ε/2) (by positivity),
    Metric.tendstoUniformly_iff.mp hU (ε/2) (by positivity)] with n hn hm x
  have H := unitBoundedProduct_sub (a:=F n x) (d:=g x) (hG n x) (hf x)
  have Hf := hn x
  have Hg := hm x
  simp only [Real.dist_eq] at Hf Hg ⊢
  rw [abs_sub_comm] at Hf Hg ⊢
  linarith

end SK.Analytic

end
end

end OAI
