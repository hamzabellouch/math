import OAI.Analysis.AncientFlat.Kernel.BilapNorm

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Laplacian
namespace FlatDuality
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
lemma norm_bilaplacian_smul_le (f : V → ℝ) (g : V → ℂ)
    (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g) (x : V) (A B : ℝ)
    (hA : 0≤A) (_hB : 0≤B)
    (hfj : ∀ n : ℕ, n≤4 → ‖iteratedFDeriv ℝ n f x‖≤A)
    (hgj : ∀ n : ℕ, n≤4 → ‖iteratedFDeriv ℝ n g x‖≤B) :
    ‖Δ (Δ (fun y => f y • g y)) x‖≤(Module.finrank ℝ V : ℝ)^2*16*A*B := by
  refine (norm_bilaplacian_le _ (hf.smul hg) x).trans ?_
  have he : ‖iteratedFDeriv ℝ 4 (fun y => f y • g y) x‖≤16*A*B := by
    refine (norm_iteratedFDeriv_smul_le hf hg x (by norm_num : (4:ℕ)≤(4:WithTop ℕ∞))).trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range 5,((4:ℕ).choose i : ℝ)*A*B := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i≤4 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hfj i hin) (Nat.cast_nonneg _))
          (hgj (4-i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = _ := by norm_num [Finset.sum_range_succ,Nat.choose]; ring
  calc
    _≤(Module.finrank ℝ V : ℝ)^2*(16*A*B) := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _=_ := by ring
end FlatDuality

end

end OAI
