import OAI.Analysis.Pureness.Comparison.FullnessFrame

namespace OAI
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in
lemma list_trace_compression (τ : TracialState A) (x : List A) (e t b : A)
    (ht : t * t = e) :
    τ.toPositiveLinearMap (x.map fun v => t * v * b * star v * t).sum =
      τ.toPositiveLinearMap (b * (x.map fun v => star v * e * v).sum) := by
  induction x with
  | nil => simp
  | cons v x ih =>
    simp only [List.map_cons, List.sum_cons, map_add, mul_add, ih]
    congr 1
    calc
      τ.toPositiveLinearMap (t * v * b * star v * t) =
          τ.toPositiveLinearMap (v * b * star v * (t * t)) := by
        simpa only [mul_assoc] using τ.tracial t (v * b * star v * t)
      _ = τ.toPositiveLinearMap (b * (star v * e * v)) := by
        rw [ht]
        simpa only [mul_assoc] using τ.tracial v (b * star v * e)

theorem exists_trace_compression [IsSimpleCStarAlgebra A]
    {e b : A} (he : 0 ≤ e) (hne : e ≠ 0) (hb : 0 ≤ b) :
    ∃ c a : A, 0 ≤ c ∧ 0 ≤ a ∧ c = CFC.sqrt e * a * CFC.sqrt e ∧
      ∀ τ : TracialState A, τ.toPositiveLinearMap c = τ.toPositiveLinearMap b := by
  obtain ⟨x, hx⟩ := exists_positive_fullness_frame he hne
  let t := CFC.sqrt e
  have ht : IsSelfAdjoint t := .of_nonneg (CFC.sqrt_nonneg e)
  let a := (x.map fun v => v * b * star v).sum
  have ha : 0 ≤ a := by
    dsimp [a]
    clear hx
    induction x with
    | nil => simp
    | cons v x ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (star_right_conjugate_nonneg hb v) ih
  have hc : 0 ≤ t * a * t := by
    simpa only [ht.star_eq] using star_left_conjugate_nonneg ha t
  refine ⟨t * a * t, a, hc, ha, rfl, fun τ => ?_⟩
  have hdist (m : List A) :
      (m.map fun v => t * v * b * star v * t).sum =
        t * (m.map fun v => v * b * star v).sum * t := by
    induction m with
    | nil => simp
    | cons v m ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, add_mul]
      simpa only [mul_assoc] using congrArg (fun z => t * v * b * star v * t + z) ih
  rw [← hdist x]
  rw [list_trace_compression τ x e t b (CFC.sqrt_mul_sqrt_self e he), hx, mul_one]

theorem exists_linking_positive_squares [IsSimpleCStarAlgebra A]
    {c d : A} (hc : 0 ≤ c) (hd : 0 ≤ d) (hcn : c ≠ 0) (hdn : d ≠ 0) :
    ∃ y z : A, z = c * y * d ∧ z ≠ 0 ∧
      0 ≤ star z * z ∧ star z * z ≠ 0 ∧
      0 ≤ z * star z ∧ z * star z ≠ 0 ∧
      star z * z = d * (star y * (c * c) * y) * d ∧
      z * star z = c * (y * (d * d) * star y) * c := by
  obtain ⟨y, hy⟩ := exists_nonzero_sandwich hcn hdn
  refine ⟨y, c * y * d, rfl, hy, star_mul_self_nonneg _, ?_,
    mul_star_self_nonneg _, ?_, ?_, ?_⟩
  · exact (CStarRing.star_mul_self_ne_zero_iff _).mpr hy
  · exact (CStarRing.mul_star_self_ne_zero_iff _).mpr hy
  · simp only [star_mul, hc.star_eq, hd.star_eq, mul_assoc]
  · simp only [star_mul, hc.star_eq, hd.star_eq, mul_assoc]

end CuntzComparison

end OAI
