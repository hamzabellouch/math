import OAI.Analysis.LipschitzHilbert.Estimates.TopBoxPolynomial

namespace OAI

/-! Convert a weighted top bound to a decaying unweighted bound, using
one fixed polynomial degree independently of the moment order. -/

noncomputable section

namespace LipschitzHilbert

theorem weighted_bound_to_box_decay (A S w P : ℝ) (hS : 0 ≤ S) (hw : 0 < w)
    (q : ℕ) (hq : 1 ≤ q) (hP : (w⁻¹/256)^q ≤ P) (hbound : P*S ≤ A/w) :
    S ≤ 256^q*A*w^(q-1) := by
  have hL : 0 < (w⁻¹/256)^q := by positivity
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    ((w⁻¹/256)^q)*S ≤ P*S := mul_le_mul_of_nonneg_right hP hS
    _ ≤ A/w := hbound
    _ = ((w⁻¹/256)^q)*(256^q*A*w^(q-1)) := by
      obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      subst q
      simp only [Nat.succ_sub_one, pow_succ, div_pow, inv_pow]
      field_simp [hw.ne']

theorem topWeight_bound_to_box_decay (a b r R x z v A S : ℝ) (p : ℤ × ℤ)
    (q : ℕ) (hq : 1 ≤ q) (hS : 0 ≤ S) (hr : 0 < r) (hR : 0 < R)
    (hx : |x-(a+r*p.1)| ≤ r) (hz : |z-(b+R*p.2)| ≤ R) (hv : |v| ≤ R)
    (hbound : (polynomialWeight a r q x * polynomialWeight b R q (z+v))*S ≤
      A/boxVariationWeight p) :
    S ≤ 256^q*A*boxVariationWeight p^(q-1) :=
  weighted_bound_to_box_decay A S (boxVariationWeight p) _ hS (boxVariationWeight_pos p)
    q hq (topWeight_box_lower a b r R x z v p q hr hR hx hz hv) hbound

end LipschitzHilbert

end

end OAI
