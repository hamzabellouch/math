import OAI.Analysis.CircleDomains.Selection.CountableConstantPairs
import OAI.Analysis.CircleDomains.Modulus.PriorityWeights

namespace OAI

/-! Priority modification preserves every trace pair whose other
coordinate is constant on its cutoff supports. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem priorityInfiniteValue_eq_outside_support
    {X : Type*} (χ : ℕ → X → ℝ) (c : ℕ → ℝ) (v : X → ℝ)
    {x : X} (hx : x ∉ ⋃ n, support (χ n)) :
    priorityInfiniteValue (fun n => χ n x) c (v x) = v x := by
  have hzero (n : ℕ) : χ n x = 0 := by
    by_contra hh
    exact hx (mem_iUnion.mpr ⟨n, hh⟩)
  simp only [priorityInfiniteValue, priorityWeight, hzero, zero_mul, tsum_zero,
    sub_zero, one_mul, add_zero]

 theorem priority_trace_pair_null
    {X : Type*} {T : Set X} (χ : ℕ → X → ℝ) (c : ℕ → ℝ) (u v : X → ℝ)
    (hold : volume ((fun x => (u x, v x)) '' T) = 0)
    (hconstant : ∀ n, ∃ a : ℝ, ∀ x ∈ T ∩ support (χ n), u x = a) :
    volume ((fun x => (u x, priorityInfiniteValue (fun n => χ n x) c (v x))) '' T) = 0 := by
  apply pair_null_of_countable_constant_cover (fun n => support (χ n)) u v
    (fun x => priorityInfiniteValue (fun n => χ n x) c (v x)) hold
    (fun x _ hx => priorityInfiniteValue_eq_outside_support χ c v hx) hconstant

end CircleDomainRigidity

end

end OAI
