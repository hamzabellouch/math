import OAI.Analysis.HyperbolicCones.DeformationCone
import OAI.Analysis.HyperbolicCones.DeformationFamily

namespace OAI

noncomputable section

open Set Polynomial

namespace Paper256

theorem intervalPolynomial_coeff_zero (a b : ℝ) :
    (intervalPolynomial a b).coeff 0 = 1 := by
  simp [intervalPolynomial]

theorem intervalPolynomial_coeff_two_neg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (intervalPolynomial a b).coeff 2 < 0 := by
  rw [intervalPolynomial_coeff_two]
  exact neg_neg_of_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hb))

theorem normalized_quadratic_iff (p : Polynomial ℝ) :
    (p.natDegree = 2 ∧ p.coeff 0 = 1 ∧ p.coeff 2 < 0) ↔
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ p = intervalPolynomial a b := by
  constructor
  · rintro ⟨hd, hz, hl⟩
    exact normalized_quadratic_representation p hd hz hl
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨intervalPolynomial_natDegree a b ha hb, intervalPolynomial_coeff_zero a b,
      intervalPolynomial_coeff_two_neg a b ha hb⟩

theorem deformedPencil_isSymm (a b η t x : ℝ) :
    (deformedPencil a b η t x).IsSymm :=
  Matrix.isSymm_diagonal _

theorem intervalPolynomial_root_set (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    {x : ℝ | (intervalPolynomial a b).IsRoot x} = {-b, a} := by
  ext x
  change (intervalPolynomial a b).IsRoot x ↔ x = -b ∨ x = a
  exact intervalPolynomial_isRoot_iff a b x ha.ne' hb.ne'

theorem intervalPolynomial_roots_compact (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsCompact {x : ℝ | (intervalPolynomial a b).IsRoot x} := by
  rw [intervalPolynomial_root_set a b ha hb]
  exact (Set.toFinite _).isCompact

theorem deformedPolynomial_roots_ordered (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    -b / timeScale η t < a / timeScale η t :=
  (div_lt_div_iff_of_pos_right (timeScale_positive η t hη)).mpr (by linarith)

theorem intervalPolynomial_tangent_product (a b x : ℝ) :
    (1 + x / b) * (1 - x / a) = (intervalPolynomial a b).eval x := by
  rw [intervalPolynomial_eval, mul_comm]

theorem normalized_affine_tangent (m r x : ℝ) (hm : m ≠ 0) (hr : r ≠ 0) :
    m * (x - r) / (m * -r) = 1 - x / r := by
  field_simp
  ring

theorem intervalPolynomial_tangent_negative (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((intervalPolynomial a b).derivative.eval (-b) * (x - -b)) /
        ((intervalPolynomial a b).derivative.eval (-b) * b) = 1 + x / b := by
  have hm := intervalPolynomial_roots_simple a b (-b) ha hb
    ((intervalPolynomial_isRoot_iff a b (-b) ha.ne' hb.ne').mpr (Or.inl rfl))
  simpa [div_neg] using normalized_affine_tangent
    ((intervalPolynomial a b).derivative.eval (-b)) (-b) x hm (neg_ne_zero.mpr hb.ne')

theorem intervalPolynomial_tangent_positive (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((intervalPolynomial a b).derivative.eval a * (x - a)) /
        ((intervalPolynomial a b).derivative.eval a * -a) = 1 - x / a := by
  have hm := intervalPolynomial_roots_simple a b a ha hb
    ((intervalPolynomial_isRoot_iff a b a ha.ne' hb.ne').mpr (Or.inr rfl))
  exact normalized_affine_tangent ((intervalPolynomial a b).derivative.eval a) a x hm ha.ne'

theorem deformedPolynomial_not_contains (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ¬ rigidlyConvexSet (intervalPolynomial a b) ⊆
      rigidlyConvexSet (deformedPolynomial a b η t) :=
  (deformedPolynomial_strict_subset a b η t ha hb hη ht).not_subset

theorem deformedPolynomial_endpoint_cofactor (a b η : ℝ) :
    deformedPolynomial a b η 1 = 1 * intervalPolynomial a b := by
  simpa using (deformedPolynomial_endpoints a b η).2

end Paper256

end

end OAI
