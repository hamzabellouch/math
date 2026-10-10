import OAI.Geometry.TranslativeCovering.SourceLocalization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CoveringGrowth
open Filter Real
open scoped Topology
lemma super_domination {C δ r : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*Real.exp (r*(n:ℝ)) ≤
      Real.exp (δ*((n:ℝ)*Real.log n)) := by
  filter_upwards [polynomial (C := C) (by norm_num : (0:ℝ)<1) k,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop ((r+1)/δ))] with n hn hl
  calc
    _ ≤ Real.exp (n:ℝ)*Real.exp (r*(n:ℝ)) := by gcongr; simpa using hn
    _ = Real.exp ((r+1)*(n:ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by
      change (r+1)/δ ≤ Real.log n at hl
      have hh := mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp hl) (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hh])

lemma exponential_domination {C δ r : ℝ} (hδ : 0 < δ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*Real.exp (-δ*((n:ℝ)*Real.log n)) ≤
      Real.exp (r*(n:ℝ)) := by
  filter_upwards [super_domination (C := C) (r := -r) hδ k] with n hn
  have hh := mul_le_mul_of_nonneg_right hn
    (Real.exp_pos (-δ*((n:ℝ)*Real.log n)+r*(n:ℝ))).le
  have he₁ : C*(n:ℝ)^k*Real.exp (-r*(n:ℝ))*Real.exp (-δ*((n:ℝ)*Real.log n)+r*(n:ℝ)) =
      C*(n:ℝ)^k*Real.exp (-δ*((n:ℝ)*Real.log n)) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have he₂ : Real.exp (δ*((n:ℝ)*Real.log n))*Real.exp (-δ*((n:ℝ)*Real.log n)+r*(n:ℝ)) = Real.exp (r*(n:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [he₁,he₂] at hh

lemma fine_base {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,C*Real.sqrt (Real.log n/(n:ℝ)) ≤
      Real.exp (-(1/3:ℝ)*Real.log n) := by
  have he := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/3)).bound
    (show 0 < 1/C^2 by positivity)
  have he' := tendsto_natCast_atTop_atTop.eventually he
  filter_upwards [he',eventually_ge_atTop 2] with n hn hn2
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1≤n))
  simp only [Real.norm_eq_abs,abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg hnp.le _)] at hn
  apply (sq_le_sq₀ (by positivity) (Real.exp_pos _).le).mp
  rw [mul_pow,Real.sq_sqrt (div_nonneg hlog hnp.le),← Real.exp_nat_mul]
  have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg C)
  have hc : C^2*((1/C^2)*(n:ℝ)^(1/3:ℝ)) = (n:ℝ)^(1/3:ℝ) := by field_simp
  rw [hc,Real.rpow_def_of_pos hnp] at hh
  have hdiv := (div_le_div_of_nonneg_right hh hnp.le)
  have hid : Real.exp (Real.log n*(1/3:ℝ))/(n:ℝ) =
      Real.exp ((2:ℝ)*(-(1/3:ℝ)*Real.log n)) := by
    conv_lhs => rw [← Real.exp_log hnp]
    rw [← Real.exp_sub,Real.log_exp]
    congr 1
    ring
  rw [hid] at hdiv
  simpa only [mul_div_assoc,Nat.cast_ofNat] using hdiv
end CoveringGrowth

end OAI
