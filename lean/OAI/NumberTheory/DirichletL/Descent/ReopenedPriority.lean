import OAI.NumberTheory.DirichletL.Descent.ReopenedMarks

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_reopened_prime_priority
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : (ι→₀ℕ)→Finset ι→ℂ) (z : O) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v S=>primeMark slots lists a (S∪v.support)*V v S) z =
    ∑J∈slots.powerset,varyingReopenedRow p hp hcop hg pool Q
      (fun v=>β v*primeMark J lists a v.support) Ψ m f
      (fun v S=>primeMark (slots\J) (fun j=>lists j\v.support) a S*V v S) z := by
  unfold varyingReopenedRow
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [canonicalSourceCoefficient]
  rw [reopened_mark_priority]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem allocated_cube_coefficient_bound
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hJ : J⊆slots) (hslots : (slots : Set σ).PairwiseDisjoint lists)
    (ha : ∀ j∈slots,∀ i∈lists j,‖a j i‖≤1)
    (β : (ι→₀ℕ)→ℂ) (v : ι→₀ℕ) :
    ‖β v*primeMark J lists a v.support‖≤‖β v‖*(2:ℝ)^v.support.card := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact primeMark_norm_le_divisor_count J lists a v.support
    (fun i hi j hj hne=>hslots (hJ hi) (hJ hj) hne) (fun j hj i hi=>ha j (hJ hj) i hi)

end
end SevenEighths.InverseMoment

end OAI
