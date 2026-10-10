import OAI.Analysis.BoundedHochschild.PositiveUnitBlocks

namespace OAI

/-! Normalize the two diagonal entries of a positive two-by-two block. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveBlock (p q x : A) : Mat A := diag p q + offdiag x (star x)

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_one (x : A) : positiveBlock 1 1 x = positiveUnitBlock x := by
  rw [positiveBlock, diag_one_one]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_conjugate (p q x u v : A) :
    star (diag u v) * positiveBlock p q x * diag u v =
      positiveBlock (star u * p * u) (star v * q * v) (star u * x * v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveBlock, diag, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two, star_mul, mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma diag_isUnit {u v : A} (hu : IsUnit u) (hv : IsUnit v) : IsUnit (diag u v) := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨v, rfl⟩ := hv
  refine ⟨⟨diag (u : A) (v : A), diag (↑u⁻¹) (↑v⁻¹), ?_, ?_⟩, rfl⟩
  · rw [diag_mul]
    simp
  · rw [diag_mul]
    simp

theorem positiveBlock_nonneg_iff (p q x : A)
    (hp : IsStrictlyPositive p) (hq : IsStrictlyPositive q) :
    0 ≤ positiveBlock p q x ↔
      ‖p ^ (-(1 / 2) : ℝ) * x * q ^ (-(1 / 2) : ℝ)‖ ≤ 1 := by
  let u := p ^ (-(1 / 2) : ℝ)
  let v := q ^ (-(1 / 2) : ℝ)
  have hu : IsStrictlyPositive u := IsStrictlyPositive.rpow p _ hp
  have hv : IsStrictlyPositive v := IsStrictlyPositive.rpow q _ hq
  have hsu : star u = u := hu.nonneg.isSelfAdjoint.star_eq
  have hsv : star v = v := hv.nonneg.isSelfAdjoint.star_eq
  have hup : star u * p * u = 1 := by
    rw [hsu]
    exact CFC.conjugate_rpow_neg_one_half p hp
  have hvq : star v * q * v = 1 := by
    rw [hsv]
    exact CFC.conjugate_rpow_neg_one_half q hq
  have he := positiveBlock_conjugate p q x u v
  rw [hup, hvq, hsu, positiveBlock_one] at he
  rw [← (diag_isUnit hu.isUnit hv.isUnit).star_left_conjugate_nonneg_iff,
    he, positiveUnitBlock_nonneg_iff]

end BoundedHochschild.KadisonRingrose

end

end OAI
