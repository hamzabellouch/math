import OAI.MeasureTheory.Falconer.Geometry.RowTubeBalls

namespace OAI

/-! Quantitative 2s-regularity of the union of the tube pencils on one
regular row, as used in the product-structure projection argument. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem row_tube_union_regular {δ y s KP KT m M : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hy : |y| ≤ 1) (hKP : 0 ≤ KP) (hKT : 0 ≤ KT)
    (hm : 0 < m) (hM : 0 ≤ M)
    {P : Finset (Space 2)} (hsep : FiniteSeparatedAt δ P)
    (hrow : ∀ x ∈ P, x 0 = y) (hP : NormalizedFiniteBallBound δ s KP P)
    (T : Space 2 → Finset (Space 2))
    (hchart : ∀ x ∈ P, InBoundedLineChart (T x))
    (hT : ∀ x ∈ P, NormalizedFiniteBallBound δ s KT (T x))
    (hsize : ∀ x ∈ P, m ≤ ((T x).card : ℝ) ∧ ((T x).card : ℝ) ≤ M)
    (hinc : ∀ x ∈ P, ∀ l ∈ T x, TubeIncident δ x l) :
    NormalizedFiniteBallBound δ (2*s)
      ((4 : ℝ)^(2*s)+25*KP*KT*(M/m)*(4 : ℝ)^s) (P.biUnion T) := by
  classical
  let U := P.biUnion T
  have hmass : (P.card : ℝ)*m ≤ 25*(U.card : ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp
      _ ≤ ∑ x ∈ P, ((T x).card : ℝ) := Finset.sum_le_sum fun x hx => (hsize x hx).1
      _ ≤ _ := row_tube_union_count hδ hsep hrow T hchart hinc
  have hratio : (P.card : ℝ)*M ≤ (25*(M/m))*(U.card : ℝ) := by
    have hb := mul_le_mul_of_nonneg_right hmass (div_nonneg hM hm.le)
    have he : ((P.card : ℝ)*m)*(M/m) = (P.card : ℝ)*M := by field_simp
    rw [he] at hb
    exact hb.trans_eq (by ring)
  let D := 25*KP*KT*(M/m)*(4 : ℝ)^s
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro z r hδr hr1
  have hr0 : 0 < r := hδ.trans_le hδr
  have hrpow : 0 ≤ r^(2*s) := Real.rpow_nonneg hr0.le _
  by_cases hsmall : 4*r ≤ 1
  · have hb := row_tube_ball_count hδ hδr hsmall hy hKT hM hrow hP T hchart hT
      (fun x hx => (hsize x hx).2) hinc z
    have he : (KP*(4*r)^s*(P.card : ℝ))*(KT*r^s*M) =
        (KP*KT*(4 : ℝ)^s*r^(2*s))*((P.card : ℝ)*M) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr0.le]
      have hp : r^(2*s) = r^s*r^s := by rw [two_mul,Real.rpow_add hr0]
      rw [hp]
      ring
    rw [he] at hb
    have hb' := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ KP*KT*(4 : ℝ)^s*r^(2*s) by positivity)
    have he' : (KP*KT*(4 : ℝ)^s*r^(2*s))*((25*(M/m))*(U.card : ℝ)) =
        D*r^(2*s)*(U.card : ℝ) := by dsimp [D]; ring
    rw [he'] at hb'
    exact (hb.trans hb').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hrpow)
      (Nat.cast_nonneg _))
  · have hlarge : 1 ≤ 4*r := le_of_lt (lt_of_not_ge hsmall)
    have hp : 1 ≤ (4*r)^(2*s) := Real.one_le_rpow hlarge (by positivity)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hr0.le] at hp
    have hp' : 1 ≤ ((4 : ℝ)^(2*s)+D)*r^(2*s) :=
      hp.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hrpow)
    calc
      _ ≤ (U.card : ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ _ := by simpa only [D,U,one_mul,mul_assoc] using
        mul_le_mul_of_nonneg_right hp' (Nat.cast_nonneg U.card)

end Falconer

end OAI
