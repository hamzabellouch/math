import OAI.Analysis.MutuallyUnbiased.Certificate.Algebra

namespace OAI

namespace MUB6.Certificate.Combination

open scoped BigOperators

/-- Two balanced formal combinations agree on arbitrary real moments whenever
all their rational coefficients agree. The leaf types may differ. -/
theorem eval_eq_of_coeff_eq {ι κ η : Type*} [Fintype ι] [DecidableEq ι]
    (leftRows : κ → Sparse ι) (rightRows : η → Sparse ι)
    (left : Combination κ) (right : Combination η)
    (h : ∀ i, coeff leftRows i left = coeff rightRows i right)
    (x : ι → ℝ) : eval leftRows x left = eval rightRows x right := by
  simp_rw [eval_eq_sum_coeff, h]

/-- A balanced target expression follows from a checked combination of source
relations, without flattening either side to a deeply nested list. -/
theorem target_zero_of_coeff_eq {ι κ η : Type*} [Fintype ι] [DecidableEq ι]
    (sources : κ → Sparse ι) (targets : η → Sparse ι)
    (source : Combination κ) (target : Combination η)
    (h : ∀ i, coeff targets i target = coeff sources i source)
    (x : ι → ℝ) (hsource : ∀ k, Sparse.eval (sources k) x = 0) :
    eval targets x target = 0 := by
  rw [eval_eq_of_coeff_eq targets sources target source h x]
  exact eval_zero_of_rows sources x hsource source

end MUB6.Certificate.Combination

end OAI
