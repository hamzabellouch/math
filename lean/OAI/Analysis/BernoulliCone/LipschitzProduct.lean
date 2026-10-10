import OAI.Analysis.BernoulliCone.MinimizerOuterVariation

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ}

lemma lipschitz_mul_compact {u φ : Space d → ℝ} {L K : ℝ≥0}
    (hu : LipschitzWith L u) (hφ : LipschitzWith K φ)
    (hc : HasCompactSupport φ) : ∃ C, LipschitzWith C (fun x => u x*φ x) := by
  obtain ⟨A,hA⟩ := hc.exists_bound_of_continuous hφ.continuous
  obtain ⟨B,hB⟩ := (hc.isCompact.image hu.continuous).isBounded.exists_norm_le
  let C : ℝ≥0 := ⟨|A| *L+|B| *K,by positivity⟩
  refine ⟨C,LipschitzWith.of_dist_le_mul ?_⟩
  have hbound (x : Space d) : |φ x| ≤ |A| := (hA x).trans (le_abs_self A)
  have hboundu {x : Space d} (hx : φ x ≠ 0) : |u x| ≤ |B| := by
    exact (hB _ (mem_image_of_mem u (subset_closure hx))).trans (le_abs_self B)
  have ht (x y : Space d) (hy : φ y ≠ 0) :
      |u x*φ x-u y*φ y| ≤ (C:ℝ)*dist x y := by
    calc
      _ = |φ x*(u x-u y)+u y*(φ x-φ y)| := by congr 1; ring
      _ ≤ |φ x*(u x-u y)|+|u y*(φ x-φ y)| := abs_add_le _ _
      _ = |φ x| *|u x-u y|+|u y| *|φ x-φ y| := by rw [abs_mul,abs_mul]
      _ ≤ |A| *(L*dist x y)+|B| *(K*dist x y) := by
        apply add_le_add
        · exact mul_le_mul (hbound x) (by simpa only [Real.norm_eq_abs,dist_eq_norm] using hu.norm_sub_le x y)
            (abs_nonneg _) (abs_nonneg _)
        · exact mul_le_mul (hboundu hy) (by simpa only [Real.norm_eq_abs,dist_eq_norm] using hφ.norm_sub_le x y)
            (abs_nonneg _) (abs_nonneg _)
      _ = _ := by change _=(|A| * (L:ℝ)+|B| * (K:ℝ))*dist x y; ring
  intro x y
  rw [Real.dist_eq]
  by_cases hy : φ y=0
  · by_cases hx : φ x=0
    · simp only [hx,hy,mul_zero,sub_self,abs_zero]; positivity
    · simpa only [abs_sub_comm,dist_comm] using ht y x hx
  · exact ht x y hy
end Bernoulli

end
end

end OAI
