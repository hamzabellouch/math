import OAI.Analysis.KadisonKastler.SpatialProduct
import OAI.Analysis.KadisonKastler.HilbertMatrix
import OAI.Analysis.FactorGeneration.MatrixUnits

namespace OAI

/-! # Finite matrix amplification in a spatial tensor product

An actual matrix-unit system in the second tensor factor gives a star
representation of operator-valued matrices. Its norm is the C-star matrix
norm: multiplying on both sides by matrix units recovers each coefficient,
so the representation is faithful whenever the second Hilbert space is
nonzero. No assertion about amplification of an ordinary algebra gap is
used here.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator
open scoped BigOperators TensorProduct InnerProductSpace

noncomputable section

private def matrixEntryStarHom {A B : Type*} [Ring A] [StarRing A] [_root_.Algebra ℂ A]
    [Ring B] [StarRing B] [_root_.Algebra ℂ B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : A →⋆ₐ[ℂ] B) : Matrix ι ι A →⋆ₐ[ℂ] Matrix ι ι B where
  toAlgHom := φ.toAlgHom.mapMatrix
  map_star' X := by
    ext i j
    exact StarHomClass.map_star φ (X j i)

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance spatialMatrixOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialMatrixStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Matrix units on the second tensor leg. -/
def spatialMatrixUnits (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    MatrixUnitSystem ι (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  E.map (spatialRight (H := H))

@[simp]
theorem spatialMatrixUnits_entry (E : MatrixUnitSystem ι (K →L[ℂ] K)) (i j : ι) :
    (spatialMatrixUnits (H := H) E).entry i j = spatialRight (H := H) (E.entry i j) := rfl

private def spatialMatrixCoefficient (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (spatialMatrixUnits (H := H) E).commutant :=
  (spatialLeft (K := K)).codRestrict _ (by
    intro a i j
    exact (Pureness.spatialLeftRight_commute
      (StarAlgHom.id ℂ (H →L[ℂ] H)) (StarAlgHom.id ℂ (K →L[ℂ] K))
      a (E.entry i j)).symm)

/-- The actual finite spatial matrix representation. -/
def spatialMatrixHom (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    CStarMatrix ι ι (H →L[ℂ] H) →⋆ₐ[ℂ]
      (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  (spatialMatrixUnits (H := H) E).coefficientHom.comp
    ((matrixEntryStarHom (spatialMatrixCoefficient (H := H) E)).comp
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

theorem spatialMatrixHom_apply (E : MatrixUnitSystem ι (K →L[ℂ] K))
    (X : CStarMatrix ι ι (H →L[ℂ] H)) :
    spatialMatrixHom E X = ∑ i, ∑ j, spatialTensorOp (X i j) (E.entry i j) := by
  change (∑ i, ∑ j, spatialLeft (K := K) (X i j) *
    spatialRight (H := H) (E.entry i j)) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change spatialTensorOp (X i j) 1 * spatialTensorOp 1 (E.entry i j) = _
  rw [← spatialTensorOp_mul, mul_one, one_mul]

/-- Matrix-unit multiplication extracts a single spatial coefficient. -/
theorem spatialMatrixHom_sandwich (E : MatrixUnitSystem ι (K →L[ℂ] K))
    (X : CStarMatrix ι ι (H →L[ℂ] H)) (o i j : ι) :
    spatialRight (H := H) (E.entry o i) * spatialMatrixHom E X *
      spatialRight (H := H) (E.entry j o) = spatialTensorOp (X i j) (E.entry o o) := by
  have hterm (a b : ι) :
      (spatialTensorOp (1 : H →L[ℂ] H) (E.entry o i) *
        spatialTensorOp (X a b) (E.entry a b)) *
        spatialTensorOp 1 (E.entry j o) =
      if i = a then if b = j then spatialTensorOp (X a b) (E.entry o o) else 0 else 0 := by
    rw [← spatialTensorOp_mul, ← spatialTensorOp_mul]
    simp only [one_mul, mul_one, E.mul_entry]
    by_cases hia : i = a
    · subst a
      by_cases hbj : b = j
      · subst b
        simp [E.mul_entry]
      · simp [E.mul_entry, hbj]
    · simp [hia]
  rw [spatialMatrixHom_apply]
  change spatialTensorOp (1 : H →L[ℂ] H) (E.entry o i) * _ *
    spatialTensorOp 1 (E.entry j o) = _
  simp only [Finset.mul_sum, Finset.sum_mul, hterm]
  simp

variable [Nonempty ι] [Nontrivial K]

/-- A nonzero second tensor leg makes the finite matrix representation faithful. -/
theorem spatialMatrixHom_injective (E : MatrixUnitSystem ι (K →L[ℂ] K)) :
    Function.Injective (spatialMatrixHom (H := H) E) := by
  let o : ι := Classical.arbitrary ι
  obtain ⟨η, hη⟩ : ∃ η : K, E.entry o o η ≠ 0 := by
    by_contra h
    apply E.diagonal_ne_zero o
    ext η
    exact not_exists_not.mp h η
  apply (injective_iff_map_eq_zero _).mpr
  intro X hX
  apply CStarMatrix.ext
  intro i j
  apply ContinuousLinearMap.ext
  intro ξ
  have hs : spatialTensorOp (X i j) (E.entry o o) = 0 := by
    rw [← spatialMatrixHom_sandwich E X o i j, hX, mul_zero, zero_mul]
  have hn := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    ‖T ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)‖) hs
  have hz : ‖X i j ξ‖ * ‖E.entry o o η‖ = 0 := by
    simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul,
      UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul, zero_apply,
      norm_zero] using hn
  exact norm_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (norm_ne_zero_iff.mpr hη))

/-- The representation has exactly the operator-valued C-star matrix norm. -/
theorem norm_spatialMatrixHom (E : MatrixUnitSystem ι (K →L[ℂ] K))
    (X : CStarMatrix ι ι (H →L[ℂ] H)) : ‖spatialMatrixHom E X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map _ (spatialMatrixHom_injective E) X

omit [Nonempty ι] [Nontrivial K] in
/-- If both sets of coefficients belong to the original algebras, their
finite spatial sum belongs to the actual spatial product algebra. -/
theorem spatialMatrixHom_mem (M : VonNeumannAlgebra H) (D : VonNeumannAlgebra K)
    (E : MatrixUnitSystem ι (K →L[ℂ] K)) (hE : ∀ i j, E.entry i j ∈ D)
    (X : CStarMatrix ι ι (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ M) :
    spatialMatrixHom E X ∈ spatialProductAlgebra M D := by
  rw [spatialMatrixHom_apply]
  apply (spatialProductAlgebra M D).sum_mem
  intro i _
  apply (spatialProductAlgebra M D).sum_mem
  intro j _
  have hp := (spatialProductAlgebra M D).mul_mem
    (spatialLeft_mem_product M D (hX i j)) (spatialRight_mem_product M D (hE i j))
  change spatialTensorOp (X i j) 1 * spatialTensorOp 1 (E.entry i j) ∈ _ at hp
  simpa only [← spatialTensorOp_mul, mul_one, one_mul] using hp

end

end KadisonKastler

end OAI
