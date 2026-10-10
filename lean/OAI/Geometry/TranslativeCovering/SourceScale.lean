import OAI.Geometry.TranslativeCovering.CubicLattice

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
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace SourceScale
open Filter SourceParameters
open scoped Topology
lemma dimension {c : ℝ} (hc : 0<c) : ∀ᶠ n : ℕ in atTop,
    2≤n ∧ 1≤c*(n:ℝ)*Real.log n ∧ c*(n:ℝ)*Real.log n≤(n:ℝ)^2 := by
  have hlog : ∀ᶠ n : ℕ in atTop,1≤Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ n : ℕ in atTop,1/c≤(n:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1/c))
  filter_upwards [hlog,hlarge,RadialShell.log_div_limit.eventually_le_const (one_div_pos.mpr hc),eventually_ge_atTop 2] with n hl hn hs hn2
  have hnp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hcn : 1≤c*(n:ℝ) := by have hh := (div_le_iff₀ hc).mp hn; linarith only [hh]
  refine ⟨hn2,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hc.le hnp.le)
    exact hcn.trans (by simpa only [mul_one] using hh)
  · have hh := (div_le_iff₀ hnp).mp hs
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hc.le hnp.le)
    have he : (c*(n:ℝ))*(1/c*(n:ℝ))=(n:ℝ)^2 := by field_simp
    rwa [he] at hm
end SourceScale

end OAI
