import OAI.Analysis.Pureness.Comparison.Fullness
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI
open scoped CStarAlgebra
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma star_add_mul_add_le (a b : A) :
    star (a + b) * (a + b) ≤ (2 : ℝ) • (star a * a + star b * b) := by
  have h := star_mul_self_nonneg (a - b)
  rw [← sub_nonneg]
  convert h using 1
  simp only [star_add, star_sub, two_smul]
  noncomm_ring

lemma list_square_sum_nonneg (l : List (A × A)) :
    0 ≤ (l.map fun v => star v.2 * v.2).sum := by
  induction l with
  | nil => simp
  | cons v l ih => simpa using add_nonneg (star_mul_self_nonneg v.2) ih

lemma finite_product_sum_bound (l : List (A × A)) :
    ∃ C : ℝ, 0 < C ∧
      star (l.map fun v => v.1 * v.2).sum * (l.map fun v => v.1 * v.2).sum ≤
        C • (l.map fun v => star v.2 * v.2).sum := by
  induction l with
  | nil => exact ⟨1, zero_lt_one, by simp⟩
  | cons v l ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let K := ‖star v.1 * v.1‖ + C
    have hK : 0 < K := add_pos_of_nonneg_of_pos (norm_nonneg _) hC
    have hsingle : star (v.1 * v.2) * (v.1 * v.2) ≤
        ‖star v.1 * v.1‖ • (star v.2 * v.2) := by
      simpa only [star_mul, mul_assoc] using
        (CStarAlgebra.star_left_conjugate_le_norm_smul
          (a := v.2) (b := star v.1 * v.1))
    refine ⟨2 * K, mul_pos (by norm_num) hK, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    calc
      _ ≤ (2 : ℝ) • (star (v.1 * v.2) * (v.1 * v.2) +
          star (l.map fun v => v.1 * v.2).sum * (l.map fun v => v.1 * v.2).sum) :=
        star_add_mul_add_le _ _
      _ ≤ (2 : ℝ) • (‖star v.1 * v.1‖ • (star v.2 * v.2) +
          C • (l.map fun v => star v.2 * v.2).sum) :=
        smul_le_smul_of_nonneg_left (add_le_add hsingle hbound) (by norm_num)
      _ ≤ (2 : ℝ) • (K • (star v.2 * v.2) +
          K • (l.map fun v => star v.2 * v.2).sum) := by
        apply smul_le_smul_of_nonneg_left _ (by norm_num)
        exact add_le_add
          (smul_le_smul_of_nonneg_right (by dsimp [K]; linarith) (star_mul_self_nonneg _))
          (smul_le_smul_of_nonneg_right (by dsimp [K]; linarith [norm_nonneg (star v.1 * v.1)])
            (list_square_sum_nonneg l))
      _ = _ := by rw [← smul_add, mul_smul]

theorem finite_gram_isUnit (l : List (A × A))
    (h : (l.map fun v => v.1 * v.2).sum = 1) :
    IsUnit (l.map fun v => star v.2 * v.2).sum := by
  obtain ⟨C, hC, hb⟩ := finite_product_sum_bound l
  rw [h, star_one, one_mul] at hb
  have hy : IsUnit (C • (l.map fun v => star v.2 * v.2).sum) :=
    CStarAlgebra.isUnit_of_le 1 hb
  have hs : IsUnit (algebraMap ℝ A C) := (isUnit_iff_ne_zero.mpr hC.ne').map _
  rw [Algebra.smul_def] at hy
  exact (hs.mul_left_iff).mp hy

theorem exists_positive_fullness_frame [IsSimpleCStarAlgebra A]
    {e : A} (he : 0 ≤ e) (hne : e ≠ 0) :
    ∃ x : List A, (x.map fun v => star v * e * v).sum = 1 := by
  obtain ⟨l, hl⟩ := exists_finite_fullness_identity hne
  let t := CFC.sqrt e
  have ht : IsSelfAdjoint t := .of_nonneg (CFC.sqrt_nonneg e)
  have ht2 : t * t = e := CFC.sqrt_mul_sqrt_self e
  let w : List (A × A) := l.map fun v => (v.1 * t, t * v.2)
  have hw : (w.map fun v => v.1 * v.2).sum = 1 := by
    simpa only [w, List.map_map, Function.comp_def, mul_assoc, ← mul_assoc t t, ht2] using hl
  let y := (w.map fun v => star v.2 * v.2).sum
  have hy : IsStrictlyPositive y :=
    IsStrictlyPositive.iff_of_unital.mpr ⟨list_square_sum_nonneg w, finite_gram_isUnit w hw⟩
  let z := CFC.rpow y (-(1 / 2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have hzyz : z * y * z = 1 := CFC.conjugate_rpow_neg_one_half y hy
  refine ⟨l.map (fun v => v.2 * z), ?_⟩
  have hysum : y = (l.map fun v => star v.2 * e * v.2).sum := by
    simp only [y, w, List.map_map, Function.comp_def, star_mul, ht.star_eq,
      mul_assoc, ← mul_assoc t t, ht2]
  rw [hysum] at hzyz
  rw [List.map_map]
  convert hzyz using 1
  have hdist (m : List (A × A)) :
      (m.map fun v => star (v.2 * z) * e * (v.2 * z)).sum =
        z * (m.map fun v => star v.2 * e * v.2).sum * z := by
    induction m with
    | nil => simp
    | cons v m ih =>
      simp only [List.map_cons, List.sum_cons, star_mul, hz.star_eq, mul_add, add_mul]
      simpa only [mul_assoc, star_mul, hz.star_eq] using
        congrArg (fun a => z * star v.2 * e * v.2 * z + a) ih
  exact hdist l

end CuntzComparison

end OAI
