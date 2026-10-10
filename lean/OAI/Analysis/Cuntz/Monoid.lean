import OAI.Analysis.Cuntz.Comparison
import OAI.Analysis.Quasitrace.Infiniteness
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Order.Antisymmetrization

namespace OAI

/-! The ordered Cuntz monoid and compression by its order unit. -/

noncomputable section
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

/-- The ordered Cuntz monoid of actual positive finite matrices over A.
The order is rectangular norm comparison, not an assumed abstract relation. -/
abbrev CuntzMonoid (A : Type*) [CStarAlgebra A] :=
  Antisymmetrization (CuntzPositiveMatrix A) (· ≤ ·)

def cuntzClass (a : CuntzPositiveMatrix A) : CuntzMonoid A :=
  toAntisymmetrization (· ≤ ·) a

theorem cuntzClass_le (a b : CuntzPositiveMatrix A) :
    cuntzClass a ≤ cuntzClass b ↔ CuntzLE a.matrix b.matrix :=
  toAntisymmetrization_le_toAntisymmetrization_iff

theorem cuntzClass_eq (a b : CuntzPositiveMatrix A) :
    cuntzClass a = cuntzClass b ↔ CuntzEquivalent a.matrix b.matrix := by
  rw [le_antisymm_iff, cuntzClass_le, cuntzClass_le]
  rfl

instance : Zero (CuntzMonoid A) := ⟨cuntzClass .zero⟩
instance : Add (CuntzMonoid A) where
  add := Quotient.map₂ CuntzPositiveMatrix.add (fun _ _ ha _ _ hb =>
    ⟨CuntzPositiveMatrix.add_le_add ha.1 hb.1, CuntzPositiveMatrix.add_le_add ha.2 hb.2⟩)

@[simp] theorem cuntzClass_add (a b : CuntzPositiveMatrix A) :
    cuntzClass (a.add b) = cuntzClass a + cuntzClass b := rfl

instance : AddCommMonoid (CuntzMonoid A) where
  add_assoc a b c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv (a.add b) c).trans
      (((CuntzPositiveMatrix.add_equiv a b).block (.refl c.matrix)).trans
        ((cuntzEquivalent_block_assoc a.matrix b.matrix c.matrix).trans
          (((CuntzEquivalent.refl a.matrix).block (CuntzPositiveMatrix.add_equiv b c).symm).trans
            (CuntzPositiveMatrix.add_equiv a (b.add c)).symm)))
  add_comm a b := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv a b).trans
      ((cuntzEquivalent_block_comm a.matrix b.matrix).trans
        (CuntzPositiveMatrix.add_equiv b a).symm)
  add_zero a := by
    induction a using Quotient.inductionOn with | h a =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv a .zero).trans (cuntzEquivalent_block_zero a.matrix)
  zero_add a := by
    induction a using Quotient.inductionOn with | h a =>
    apply (cuntzClass_eq _ _).mpr
    exact (CuntzPositiveMatrix.add_equiv .zero a).trans
      ((cuntzEquivalent_block_comm _ _).trans (cuntzEquivalent_block_zero a.matrix))
  nsmul := nsmulRec

instance : IsOrderedAddMonoid (CuntzMonoid A) where
  add_le_add_left a b h c := by
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    induction c using Quotient.inductionOn with | h c =>
    exact (cuntzClass_le _ _).mpr
      (CuntzPositiveMatrix.add_le_add ((cuntzClass_le _ _).mp h) (le_refl c))

theorem cuntzMonoid_nonneg (x : CuntzMonoid A) : 0 ≤ x := by
  induction x using Quotient.inductionOn with | h x =>
  exact (cuntzClass_le _ _).mpr (CuntzPositiveMatrix.zero_le x)

/-- Class of the n-by-n identity. -/
def cuntzUnit (A : Type*) [CStarAlgebra A] (n : ℕ) : CuntzMonoid A :=
  cuntzClass (.unit n)

theorem cuntzUnit_zero : cuntzUnit A 0 = 0 := by
  apply (cuntzClass_eq _ _).mpr
  have h : (CuntzPositiveMatrix.unit (A := A) 0).matrix = 0 := by
    ext i
    exact Fin.elim0 i
  change CuntzEquivalent _ (0 : Matrix (Fin 0) (Fin 0) A)
  rw [h]
  exact .refl _

theorem cuntzUnit_add (m n : ℕ) : cuntzUnit A (m+n) = cuntzUnit A m + cuntzUnit A n := by
  apply (cuntzClass_eq _ _).mpr
  have h : (CuntzPositiveMatrix.add (CuntzPositiveMatrix.unit (A := A) m)
      (CuntzPositiveMatrix.unit n)).matrix = (1 : Matrix (Fin (m+n)) (Fin (m+n)) A) := by
    simp [CuntzPositiveMatrix.add, CuntzPositiveMatrix.unit, cuntzBlock,
      Matrix.fromBlocks_one]
  change CuntzEquivalent 1 _
  rw [h]
  exact .refl _

theorem cuntzUnit_nsmul (n : ℕ) : n • cuntzUnit A 1 = cuntzUnit A n := by
  induction n with
  | zero => simp [cuntzUnit_zero]
  | succ n ih => rw [succ_nsmul, ih, ← cuntzUnit_add]

/-- Every class is bounded by a natural multiple of [1_A]. -/
theorem cuntzMonoid_orderUnit (x : CuntzMonoid A) : ∃ n : ℕ, x ≤ n • cuntzUnit A 1 := by
  induction x using Quotient.inductionOn with | h x =>
  refine ⟨x.size, ?_⟩
  rw [cuntzUnit_nsmul]
  exact (cuntzClass_le _ _).mpr x.le_unit

end Kaplansky

end

noncomputable section
open scoped Matrix CStarAlgebra

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A coisometry supported on the first half of the columns gives two
orthogonal isometries in the undoubled algebra. -/
theorem properlyInfinite_of_coisometry_half
    (Y : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) (hY : Y * star Y = 1)
    (hzero : ∀ i j, Y i (Sum.inr j) = 0) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  let s : CStarMatrix ι ι A := CStarMatrix.ofMatrix fun i j => star (Y (Sum.inl j) (Sum.inl i))
  let t : CStarMatrix ι ι A := CStarMatrix.ofMatrix fun i j => star (Y (Sum.inr j) (Sum.inl i))
  have hs (i j : ι) : s i j = star (Y (Sum.inl j) (Sum.inl i)) := rfl
  have ht (i j : ι) : t i j = star (Y (Sum.inr j) (Sum.inl i)) := rfl
  have he (i j : ι ⊕ ι) : (∑ k : ι, Y i (Sum.inl k) * star (Y j (Sum.inl k))) =
      if i = j then 1 else 0 := by
    have h := congrArg (fun M : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A => M i j) hY
    simpa [CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Fintype.sum_sum_type, hzero, Matrix.one_apply, CStarMatrix.one_apply] using h
  refine ⟨s, t, ?_, ?_, ?_⟩
  · ext i j
    simpa [hs, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Matrix.one_apply, CStarMatrix.one_apply] using he (Sum.inl i) (Sum.inl j)
  · ext i j
    simpa [ht, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Matrix.one_apply, CStarMatrix.one_apply] using he (Sum.inr i) (Sum.inr j)
  · ext i j
    simpa [hs, ht, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply] using he (Sum.inl i) (Sum.inr j)

/-- Invertible rectangular row Gram gives a genuine coisometry by inverse
square-root normalization. The zero column block is retained. -/
theorem properlyInfinite_of_invertible_rectangular_gram
    (v : Matrix (ι ⊕ ι) ι A)
    (hv : IsUnit (CStarMatrix.ofMatrix (v * v.conjTranspose))) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  let : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : ContinuousFunctionalCalculus ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ (CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A) :=
    CStarAlgebra.instNonnegSpectrumClass'
  let X : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A := CStarMatrix.ofMatrix (Matrix.fromCols v 0)
  let Q : CStarMatrix (ι ⊕ ι) (ι ⊕ ι) A := X * star X
  have hQ : Q = CStarMatrix.ofMatrix (v * v.conjTranspose) := by
    apply CStarMatrix.ext
    intro i j
    change (∑ k : ι ⊕ ι,
      (Sum.elim (v i) (fun _ => 0) k) * star (Sum.elim (v j) (fun _ => 0) k)) =
      ∑ k : ι, v i k * star (v j k)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul,
      Finset.sum_const_zero, add_zero]
  have hpos : IsStrictlyPositive Q := (hQ.symm ▸ hv).isStrictlyPositive (mul_star_self_nonneg X)
  let L := Q ^ (-(1 / 2) : ℝ)
  have hL : star L = L := (CFC.rpow_nonneg (a := Q) (y := (-(1 / 2) : ℝ))).isSelfAdjoint.star_eq
  apply properlyInfinite_of_coisometry_half (L * X)
  · calc
      L * X * star (L * X) = L * Q * L := by simp only [star_mul, hL, Q, mul_assoc]
      _ = 1 := CFC.conjugate_rpow_neg_one_half Q hpos
  · intro i j
    have hX (k : ι ⊕ ι) : X k (Sum.inr j) = 0 := rfl
    simp only [CStarMatrix.mul_apply, hX, mul_zero, Finset.sum_const_zero]

/-- Approximate compression of a doubled identity already forces proper
infiniteness, using the radius-one invertibility criterion. -/
theorem properlyInfinite_of_cuntzLE_double_unit
    (h : CuntzLE (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) A) (1 : Matrix ι ι A)) :
    ProperlyInfinite (CStarMatrix ι ι A) := by
  obtain ⟨v, hv⟩ := (CuntzLE.iff_approx _ _).mp h 1 zero_lt_one
  simp only [Matrix.mul_one] at hv
  apply properlyInfinite_of_invertible_rectangular_gram v
  let Q := CStarMatrix.ofMatrix (v * v.conjTranspose)
  have hnorm : ‖1 - Q‖ < 1 := hv
  have hu := (Units.oneSub (1 - Q) hnorm).isUnit
  simpa only [Units.val_oneSub, sub_sub_cancel] using hu

theorem properlyInfinite_of_cuntzUnit_compression (k : ℕ)
    (h : (2*k) • cuntzUnit A 1 ≤ k • cuntzUnit A 1) :
    ProperlyInfinite (CStarMatrix (Fin k) (Fin k) A) := by
  rw [cuntzUnit_nsmul, cuntzUnit_nsmul] at h
  have hc : CuntzLE (1 : Matrix (Fin (2*k)) (Fin (2*k)) A) (1 : Matrix (Fin k) (Fin k) A) :=
    (cuntzClass_le _ _).mp h
  have hsum : CuntzLE (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) A)
      (1 : Matrix (Fin k) (Fin k) A) := by
    rw [two_mul] at hc
    have he := (cuntzEquivalent_submatrix_equiv
      (1 : Matrix (Fin (k+k)) (Fin (k+k)) A) finSumFinEquiv).1.trans hc
    simpa using he
  exact properlyInfinite_of_cuntzLE_double_unit hsum

end Kaplansky

end

end OAI
