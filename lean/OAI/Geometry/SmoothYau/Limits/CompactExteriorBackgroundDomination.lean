import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
namespace YauCounterexamples

theorem compact_exterior_background_domination {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {r φ : X → ℝ}
    (hr : ContinuousOn r K) (hφ : ContinuousOn φ K)
    (hrpos : ∀ x ∈ K, 0 < r x) (hgap : ∀ x ∈ K, φ x < Real.log (r x)) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, (n:ℝ)^k*Real.exp ((n:ℝ)*φ x) < (r x)^n := by
  classical
  by_cases hne : K.Nonempty
  · let f := fun x => Real.exp (φ x)/r x
    have hf : ContinuousOn f K := hφ.rexp.div hr (fun x hx => (hrpos x hx).ne')
    obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne hf
    have hfz : 0 < f z := div_pos (Real.exp_pos _) (hrpos z hz)
    have hlt : f z < 1 := by
      apply (div_lt_one (hrpos z hz)).mpr
      rw [←Real.exp_log (hrpos z hz)]
      exact Real.exp_lt_exp.mpr (hgap z hz)
    have ht := tendsto_pow_const_mul_const_pow_of_lt_one k hfz.le hlt
    filter_upwards [ht.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    intro x hx
    have hfx : Real.exp (φ x) ≤ f z*r x := (div_le_iff₀ (hrpos x hx)).mp (hm hx)
    have hp := pow_le_pow_left₀ (Real.exp_pos (φ x)).le hfx n
    rw [←Real.exp_nat_mul,mul_pow] at hp
    calc
      _ ≤ (n:ℝ)^k*((f z)^n*(r x)^n) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((n:ℝ)^k*(f z)^n)*(r x)^n := by ring
      _ < 1*(r x)^n := mul_lt_mul_of_pos_right hn (pow_pos (hrpos x hx) n)
      _ = _ := one_mul _
  · exact Filter.Eventually.of_forall (fun n x hx => (hne ⟨x,hx⟩).elim)
end YauCounterexamples

end

end OAI
