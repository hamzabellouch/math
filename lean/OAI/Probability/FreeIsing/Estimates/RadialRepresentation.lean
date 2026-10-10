import OAI.Probability.FreeIsing.Estimates.RadialWalk

namespace OAI

noncomputable section
namespace Problem367
namespace RadialWalk

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def wordOperator (S : Fin d → H →L[ℝ] H) (v : TreeVertex d) : H →L[ℝ] H :=
  (v.1.map S).prod

theorem wordOperator_step (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (v : TreeVertex d) (c : Fin d) :
    wordOperator S (treeStep v c) = wordOperator S v * S c := by
  rcases (treeStep_eq_iff v (treeStep v c) c).mp rfl with h | h
  · simp [wordOperator, h, List.map_append, List.prod_append]
  · have hv : wordOperator S v = wordOperator S (treeStep v c) * S c := by
      simp [wordOperator, h, List.map_append, List.prod_append]
    rw [hv, mul_assoc, hS c, mul_one]

def operatorAverage (S : Fin d → H →L[ℝ] H) : H →L[ℝ] H :=
  (d : ℝ)⁻¹ • ∑ c, S c

theorem operatorAverage_apply (S : Fin d → H →L[ℝ] H) (x : H) :
    operatorAverage S x = (d : ℝ)⁻¹ • ∑ c, S c x := by
  simp [operatorAverage]

theorem vectorAverage_wordOperator (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (x : H) (v : TreeVertex d) :
    vectorAverage treeStep (fun w => wordOperator S w x) v =
      wordOperator S v (operatorAverage S x) := by
  simp only [vectorAverage, wordOperator_step S hS, mul_apply_eq_comp,
    operatorAverage_apply, map_smul, map_sum]

theorem iterate_vectorAverage_wordOperator (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (x : H) (n : ℕ) :
    ((vectorAverage treeStep)^[n]) (fun w => wordOperator S w x) =
      fun w => wordOperator S w ((operatorAverage S ^ n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', ih, vectorAverage_wordOperator S hS]
    rw [pow_succ']
    rfl

theorem matrix_coefficient_power_bound (S : Fin d → H →L[ℝ] H)
    (hS : ∀ c, S c * S c = 1) (hd : 3 ≤ d) (x : H)
    {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ x (wordOperator S v x)| ≤ C * treeWeight d v)
    (n : ℕ) :
    |inner ℝ x ((operatorAverage S ^ n) x)| ≤ C * rate d ^ n := by
  let o : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have h := covariance_walk_bound hd (fun v => wordOperator S v x) o rfl hC
    (by simpa only [wordOperator, o, List.map_nil, List.prod_nil,
      one_apply_eq_self] using hcov) n
  rw [iterate_vectorAverage_wordOperator S hS] at h
  simpa only [wordOperator, o, List.map_nil, List.prod_nil,
    one_apply_eq_self] using h

end RadialWalk
end Problem367

end

end OAI
