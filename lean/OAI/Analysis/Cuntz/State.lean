import OAI.Algebra.OrderedStates.Semigroup
import OAI.Analysis.Cuntz.Monoid

namespace OAI

noncomputable section

/-! Dimension states of the Cuntz monoid and positivity. -/

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

theorem normalizedCuntzState_exists
    (hf : ∀ k : ℕ, 0 < k → ¬ ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A)) :
    ∃ f : CuntzMonoid A →+ ℝ, Monotone f ∧ f (cuntzUnit A 1) = 1 := by
  apply positive_orderUnit_normalized_state (cuntzUnit A 1)
    cuntzMonoid_nonneg cuntzMonoid_orderUnit
  intro k hk h
  exact hf k hk (properlyInfinite_of_cuntzUnit_compression k h)

/-- A normalized dimension state on actual positive finite matrices.
This is a semigroup state, not yet a quasitrace or its regularization. -/
structure CuntzDimensionState (A : Type*) [CStarAlgebra A] where
  state : CuntzMonoid A →+ ℝ
  monotone : Monotone state
  normalized : state (cuntzUnit A 1) = 1

theorem cuntzDimensionState_nonempty
    (hf : ∀ k : ℕ, 0 < k → ¬ ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A)) :
    Nonempty (CuntzDimensionState A) := by
  obtain ⟨f, hm, hu⟩ := normalizedCuntzState_exists hf
  exact ⟨⟨f, hm, hu⟩⟩

namespace CuntzDimensionState

def value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : ℝ := d.state (cuntzClass a)

theorem value_mono (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzLE a.matrix b.matrix) : d.value a ≤ d.value b :=
  d.monotone ((cuntzClass_le a b).mpr h)

theorem value_eq (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzEquivalent a.matrix b.matrix) : d.value a = d.value b :=
  le_antisymm (d.value_mono h.1) (d.value_mono h.2)

theorem value_add (d : CuntzDimensionState A) (a b : CuntzPositiveMatrix A) :
    d.value (a.add b) = d.value a + d.value b := by
  simp only [value, cuntzClass_add, map_add]

theorem value_unit (d : CuntzDimensionState A) (n : ℕ) :
    d.value (.unit n) = (n : ℝ) := by
  change d.state (cuntzUnit A n) = _
  rw [← cuntzUnit_nsmul, map_nsmul, d.normalized]
  simp

theorem value_zero (d : CuntzDimensionState A) : d.value .zero = 0 := d.state.map_zero

theorem value_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : 0 ≤ d.value a := by
  simpa only [map_zero, value] using d.monotone (cuntzMonoid_nonneg (cuntzClass a))

theorem value_le_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.value a ≤ a.size := (d.value_mono a.le_unit).trans_eq (d.value_unit a.size)

end CuntzDimensionState
end Kaplansky

open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- Positive order gives actual approximate conjugation. An inverse
square-root of b+δ1 supplies a contraction and an error bounded by δ. -/
theorem exists_positiveOrder_approx {a b : A} (ha : 0 ≤ a) (hab : a ≤ b)
    (ε : ℝ) (hε : 0 < ε) : ∃ v : A, ‖a - v*b*star v‖ < ε := by
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hd0 : 0 ≤ δ • (1 : A) := smul_nonneg hδ.le zero_le_one
  have hd : IsStrictlyPositive (δ • (1 : A)) := by
    refine ⟨hd0, ?_⟩
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (isUnit_iff_ne_zero.mpr hδ.ne').map (algebraMap ℝ A)
  let Q := b + δ • (1 : A)
  have hQ : IsStrictlyPositive Q := IsStrictlyPositive.nonneg_add (ha.trans hab) hd
  let S := CFC.sqrt a
  let L := Q ^ (-(1/2) : ℝ)
  let v := S * L
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hL : star L = L := (CFC.rpow_nonneg (a := Q) (y := (-(1/2) : ℝ))).isSelfAdjoint.star_eq
  have hv : ‖v‖ ≤ 1 := (le_iff_norm_sqrt_mul_rpow a Q ha hQ).mp
    (hab.trans (le_add_of_nonneg_right hd0))
  have he : v * Q * star v = a := by
    calc
      v * Q * star v = S * (L * Q * L) * S := by simp only [v, star_mul, hS, hL, mul_assoc]
      _ = S * S := by rw [CFC.conjugate_rpow_neg_one_half Q hQ]; simp
      _ = a := CFC.sqrt_mul_sqrt_self a ha
  have herr : a - v*b*star v = δ • (v*star v) := by
    rw [← he]
    simp only [Q, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, add_sub_cancel_left]
  refine ⟨v, ?_⟩
  rw [herr, norm_smul, Real.norm_of_nonneg hδ.le]
  have hn := norm_nonneg v
  have hsq : ‖v‖ * ‖v‖ ≤ 1 := by nlinarith
  have hbound : δ * (‖v‖ * ‖v‖) ≤ δ := by nlinarith
  exact (mul_le_mul_of_nonneg_left (by simpa only [norm_star] using norm_mul_le v (star v)) hδ.le).trans_lt
    (hbound.trans_lt (half_lt_self hε))

theorem cuntzLE_of_nonneg_le {n : ℕ} {a b : CStarMatrix (Fin n) (Fin n) A}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    CuntzLE (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b) := by
  apply (CuntzLE.iff_approx _ _).mpr
  intro ε hε
  obtain ⟨v, hv⟩ := exists_positiveOrder_approx ha hab ε hε
  exact ⟨CStarMatrix.ofMatrix.symm v, hv⟩

theorem CuntzDimensionState.value_mono_positive (d : CuntzDimensionState A)
    (n : ℕ) (a b : CStarMatrix (Fin n) (Fin n) A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
    d.value ⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ ≤
      d.value ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ :=
  d.value_mono (cuntzLE_of_nonneg_le ha hab)

end Kaplansky

end

end OAI
