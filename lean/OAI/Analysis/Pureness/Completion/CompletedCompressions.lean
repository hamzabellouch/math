import OAI.Analysis.Pureness.Completion.CornerCompletion
import OAI.Analysis.Pureness.Completion.CornerCompression
import Mathlib.Tactic.NoncommRing

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance cornerCompletionOrder : PartialOrder (CornerCompletion A) := CStarAlgebra.spectralOrder _
instance cornerCompletionStarOrdered : StarOrderedRing (CornerCompletion A) := CStarAlgebra.spectralOrderedRing _

lemma completedMatrixInclude_nonneg (k : ℕ) (a : MatrixStage A k) (ha : 0 ≤ a) :
    0 ≤ completedMatrixInclude A k a := by
  obtain ⟨x, rfl⟩ := positive_square_factor a ha
  rw [map_mul, map_star]
  exact star_mul_self_nonneg _

def completedProjection (k : ℕ) : CornerCompletion A := completedMatrixInclude A k 1

lemma completedProjection_star (k : ℕ) : star (completedProjection A k) = completedProjection A k := by
  change star (completedMatrixInclude A k 1) = completedMatrixInclude A k 1
  rw [← map_star, star_one]

lemma completedProjection_norm_le (k : ℕ) : ‖completedProjection A k‖ ≤ 1 := by
  change ‖completedMatrixInclude A k 1‖ ≤ 1
  rw [completedMatrixInclude_norm]
  cases subsingleton_or_nontrivial (MatrixStage A k)
  · rw [Subsingleton.elim (1 : MatrixStage A k) 0, norm_zero]; exact zero_le_one
  · exact le_of_eq norm_one

def completedCornerCut (k : ℕ) (a : CornerCompletion A) : CornerCompletion A :=
  completedProjection A k * a * completedProjection A k

lemma completedCornerCut_continuous (k : ℕ) : Continuous (completedCornerCut A k) := by
  unfold completedCornerCut
  fun_prop

lemma completedCornerCut_sub (k : ℕ) (a b : CornerCompletion A) :
    completedCornerCut A k (a - b) = completedCornerCut A k a - completedCornerCut A k b := by
  simp only [completedCornerCut, mul_sub, sub_mul]

lemma completedCornerCut_norm_le (k : ℕ) (a : CornerCompletion A) :
    ‖completedCornerCut A k a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖completedProjection A k‖ * ‖a‖ * ‖completedProjection A k‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖a‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (completedProjection_norm_le A k) (norm_nonneg _))
      (completedProjection_norm_le A k) (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by ring

lemma completedCornerCut_fixes {l k : ℕ} (h : l ≤ k) (a : MatrixStage A l) :
    completedCornerCut A k (completedMatrixInclude A l a) = completedMatrixInclude A l a := by
  rw [← completedMatrixInclude_corner A h a]
  change completedMatrixInclude A k 1 * completedMatrixInclude A k (corner h a) *
    completedMatrixInclude A k 1 = _
  rw [← map_mul, ← map_mul, one_mul, mul_one]

theorem completedCornerCut_tendsto (a : CornerCompletion A) :
    Tendsto (fun k : ℕ => completedCornerCut A k a) atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ha := completedMatrixInclude_dense A a
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.mp ha (ε / 2) (by positivity)
  obtain ⟨l, c, rfl⟩ := Set.mem_iUnion.mp hb
  refine ⟨l, fun k hk => ?_⟩
  have hfix := completedCornerCut_fixes A hk c
  have heq : completedCornerCut A k a - a =
      completedCornerCut A k (a - completedMatrixInclude A l c) +
        (completedMatrixInclude A l c - a) := by
    rw [completedCornerCut_sub, hfix]
    abel
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ‖completedCornerCut A k (a - completedMatrixInclude A l c)‖ +
        ‖completedMatrixInclude A l c - a‖ := norm_add_le _ _
    _ ≤ ‖a - completedMatrixInclude A l c‖ + ‖completedMatrixInclude A l c - a‖ :=
      add_le_add (completedCornerCut_norm_le A k _) le_rfl
    _ < ε := by
      rw [norm_sub_rev (completedMatrixInclude A l c)]
      rw [dist_eq_norm] at hab
      linarith

lemma completedCornerCut_nonneg (k : ℕ) (a : CornerCompletion A) (ha : 0 ≤ a) :
    0 ≤ completedCornerCut A k a := by
  simpa only [completedCornerCut, completedProjection_star] using star_left_conjugate_nonneg ha (completedProjection A k)

lemma completedCornerCut_cuntz (k : ℕ) (a : CornerCompletion A) :
    CuntzSubequiv (completedCornerCut A k a) a := by
  simpa only [completedCornerCut, completedProjection_star] using cuntzSubequiv_conjugate a (completedProjection A k)
end CuntzPureness

end

end OAI
