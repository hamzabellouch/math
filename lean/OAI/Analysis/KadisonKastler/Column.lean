import OAI.Analysis.KadisonKastler.PairedRepresentations
import OAI.Analysis.KadisonKastler.HilbertMatrix
import OAI.Analysis.KadisonKastler.CyclicRestriction
import OAI.Analysis.KadisonKastler.RectangularHilbert

namespace OAI

/-!
# The triangular representation for the column estimate

The triangular representation is constructed and bounded directly.
Haagerup's cyclic similarity theorem is isolated as the precise published
input at the cyclic restriction step.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance columnOperatorPartialOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance columnOperatorStarOrderedRing : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

omit [CompleteSpace H] in
theorem innerDerivation_mul (T x y : H →L[ℂ] H) :
    innerDerivation T (x * y) = x * innerDerivation T y + innerDerivation T x * y := by
  simp only [innerDerivation_apply]
  noncomm_ring

/-- The represented commutator, with its boundedness proved from multiplication. -/
def representedInnerDerivation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) :
    A →L[ℂ] (H →L[ℂ] H) :=
  ((innerDerivation h).comp ρ.toAlgHom.toLinearMap).mkContinuous (2 * ‖h‖) (fun a => by
    change ‖h * ρ a - ρ a * h‖ ≤ (2 * ‖h‖) * ‖a‖
    calc
      _ ≤ ‖h * ρ a‖ + ‖ρ a * h‖ := norm_sub_le _ _
      _ ≤ ‖h‖ * ‖ρ a‖ + ‖ρ a‖ * ‖h‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (2 * ‖h‖) * ‖ρ a‖ := by ring
      _ ≤ (2 * ‖h‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le ρ a) (by positivity))

@[simp]
theorem representedInnerDerivation_apply (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : H →L[ℂ] H) (a : A) :
    representedInnerDerivation ρ h a = innerDerivation h (ρ a) := rfl

def triangularMatrix (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) (δ : ℝ) (a : A) :
    CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) :=
  !![ρ a, ((δ⁻¹ : ℝ) : ℂ) • innerDerivation h (ρ a); 0, ρ a]

def triangularRepresentation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) (δ : ℝ) :
    A →ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H) where
  toFun := triangularMatrix ρ h δ
  map_one' := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [triangularMatrix, innerDerivation_apply]
  map_mul' a b := by
    apply CStarMatrix.ext
    intro i j
    simp only [CStarMatrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [triangularMatrix, map_mul, innerDerivation_apply,
        sub_mul, mul_sub, smul_sub, mul_assoc]
  map_zero' := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [triangularMatrix]
  map_add' a b := by
    apply CStarMatrix.ext
    intro i j
    simp only [CStarMatrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp [triangularMatrix, innerDerivation_apply, mul_add, add_mul, smul_add, smul_sub]
      ; module
  commutes' z := by
    have hz : ρ (algebraMap ℂ A z) = algebraMap ℂ (H →L[ℂ] H) z :=
      ρ.toAlgHom.commutes z
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [triangularMatrix, innerDerivation_apply, CStarMatrix.algebraMap_apply,
        hz, Algebra.commutes]

theorem triangularMatrix_decomposition (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : H →L[ℂ] H) (δ : ℝ) (a : A) :
    triangularMatrix ρ h δ a = blockDiagonal (ρ a) (ρ a) +
      blockOffDiagonal (((δ⁻¹ : ℝ) : ℂ) • innerDerivation h (ρ a)) 0 := by
  ext i j
  simp only [CStarMatrix.add_apply]
  fin_cases i <;> fin_cases j <;> simp [triangularMatrix, blockDiagonal, blockOffDiagonal]

theorem norm_triangularRepresentation_le_two
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ a, ‖innerDerivation h (ρ a)‖ ≤ δ * ‖a‖) (a : A) :
    ‖triangularRepresentation ρ h δ a‖ ≤ 2 * ‖a‖ := by
  have hentry : ‖((δ⁻¹ : ℝ) : ℂ) • innerDerivation h (ρ a)‖ ≤ ‖a‖ := by
    calc
      _ = δ⁻¹ * ‖innerDerivation h (ρ a)‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
      _ ≤ δ⁻¹ * (δ * ‖a‖) :=
        mul_le_mul_of_nonneg_left (hbound a) (inv_nonneg.mpr hδ.le)
      _ = ‖a‖ := by rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
  change ‖triangularMatrix ρ h δ a‖ ≤ 2 * ‖a‖
  rw [triangularMatrix_decomposition]
  calc
    _ ≤ ‖blockDiagonal (ρ a) (ρ a)‖ +
        ‖blockOffDiagonal (((δ⁻¹ : ℝ) : ℂ) • innerDerivation h (ρ a)) 0‖ := norm_add_le _ _
    _ = ‖ρ a‖ + ‖((δ⁻¹ : ℝ) : ℂ) • innerDerivation h (ρ a)‖ := by
      rw [norm_blockDiagonal, max_self, norm_blockOffDiagonal, norm_zero,
        max_eq_left (norm_nonneg _)]
    _ ≤ ‖a‖ + ‖a‖ := add_le_add (NonUnitalStarAlgHom.norm_apply_le ρ a) hentry
    _ = 2 * ‖a‖ := by ring

/-- The same triangular homomorphism on the actual Hilbert direct sum. -/
def triangularHilbertRepresentation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : H →L[ℂ] H) (δ : ℝ) :
    A →ₐ[ℂ] (Generator.FiniteHilbert (Fin 2) H →L[ℂ] Generator.FiniteHilbert (Fin 2) H) :=
  hilbertMatrixHom.toAlgHom.comp (triangularRepresentation ρ h δ)

theorem norm_triangularHilbertRepresentation_le_two
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ a, ‖innerDerivation h (ρ a)‖ ≤ δ * ‖a‖) (a : A) :
    ‖triangularHilbertRepresentation ρ h δ a‖ ≤ 2 * ‖a‖ := by
  change ‖hilbertMatrix (triangularRepresentation ρ h δ a)‖ ≤ 2 * ‖a‖
  rw [norm_hilbertMatrix]
  exact norm_triangularRepresentation_le_two ρ h hδ hbound a

theorem triangularHilbertRepresentation_apply_upper
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) (δ : ℝ) (a : A) (ξ : H) :
    triangularHilbertRepresentation ρ h δ a (Generator.tupleSingle (1 : Fin 2) ξ) 0 =
      ((δ⁻¹ : ℝ) : ℂ) • (innerDerivation h (ρ a) ξ) := by
  change hilbertMatrix (triangularMatrix ρ h δ a) (Generator.tupleSingle (1 : Fin 2) ξ) 0 = _
  rw [hilbertMatrix_apply]
  simp [Fin.sum_univ_two, triangularMatrix, Generator.tupleSingle_apply, Pi.single_apply]

variable [PartialOrder A] [StarOrderedRing A]

/-- Complete bound for a Hilbert-space algebra representation. -/
def RepresentationCompletelyBoundedBy {K : Type v} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (Φ : A →ₐ[ℂ] (K →L[ℂ] K)) (C : ℝ) : Prop :=
  letI : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (K →L[ℂ] K) := CStarAlgebra.spectralOrderedRing _
  CompletelyBoundedBy (A := A) (B := K →L[ℂ] K) Φ.toLinearMap C

/-- A complete bound controls the action of each column on a vector. -/
theorem RepresentationCompletelyBoundedBy.column_vector
    {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {Φ : A →ₐ[ℂ] (K →L[ℂ] K)} {C : ℝ} (hcb : RepresentationCompletelyBoundedBy Φ C)
    (p : ℕ) (X : CStarMatrix (Fin p) (Fin 1) A) (ξ : K) :
    ‖WithLp.toLp 2 (fun i => Φ (X i 0) ξ)‖ ≤ C * ‖X‖ * ‖ξ‖ := by
  let : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _
  have : StarOrderedRing (K →L[ℂ] K) := CStarAlgebra.spectralOrderedRing _
  let Y := CStarMatrix.mapₗ Φ.toLinearMap X
  have heq : rectangularHilbertMatrix Y (Generator.tupleSingle (0 : Fin 1) ξ) =
      WithLp.toLp 2 (fun i => Φ (X i 0) ξ) := by
    ext i
    simp [rectangularHilbertMatrix_apply, Y,
      Generator.tupleSingle_apply, Pi.single_apply]
  calc
    _ = ‖rectangularHilbertMatrix Y (Generator.tupleSingle (0 : Fin 1) ξ)‖ :=
      congrArg norm heq.symm
    _ ≤ ‖rectangularHilbertMatrix Y‖ * ‖Generator.tupleSingle (0 : Fin 1) ξ‖ :=
      (rectangularHilbertMatrix Y).le_opNorm _
    _ = ‖Y‖ * ‖ξ‖ := by rw [norm_rectangularHilbertMatrix, norm_tupleSingle]
    _ ≤ (C * ‖X‖) * ‖ξ‖ := mul_le_mul_of_nonneg_right (hcb p 1 X) (norm_nonneg _)

/-- Restricting to a cyclic orbit and then keeping one coordinate does not
increase a column bound. -/
theorem cyclic_column_coordinate_bound
    (Φ : A →ₐ[ℂ] (Generator.FiniteHilbert (Fin 2) H →L[ℂ]
      Generator.FiniteHilbert (Fin 2) H))
    (η : Generator.FiniteHilbert (Fin 2) H) {C : ℝ}
    (hcb : RepresentationCompletelyBoundedBy (restrictCyclicRepresentation Φ η) C)
    (p : ℕ) (X : CStarMatrix (Fin p) (Fin 1) A) :
    ‖WithLp.toLp 2 (fun i => Φ (X i 0) η 0)‖ ≤ C * ‖X‖ * ‖η‖ := by
  let W := representationCyclicSpace Φ η
  let v : W := representationCyclicVector Φ η
  let w : Generator.FiniteHilbert (Fin p) W :=
    WithLp.toLp 2 (fun i => restrictCyclicRepresentation Φ η (X i 0) v)
  have hp := norm_hilbertTuple_coordinate_le (0 : Fin 2) w
  exact hp.trans (RepresentationCompletelyBoundedBy.column_vector hcb p X v)

/-- Haagerup, *Solution of the similarity problem for cyclic
representations of C*-algebras*, Ann. of Math. 118 (1983), Theorem 1.1
and its proof, pp. 217 and 225: a cyclic representation bounded by `C`
is completely bounded by `C³`. This consequence is also stated explicitly
in Pitts, Proc. Amer. Math. Soc. 136 (2008), 1757–1768, Remark 2.12
(arXiv:math/0609604, p. 6). Only this consequence is assumed. -/
def PublishedCyclicSimilarity : Prop :=
  ∀ (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K],
    ∀ Φ : A →ₐ[ℂ] (K →L[ℂ] K),
      (∃ ξ : K, Dense (Set.range (fun a => Φ a ξ))) →
      ∀ C : ℝ, 1 ≤ C → (∀ a, ‖Φ a‖ ≤ C * ‖a‖) →
        RepresentationCompletelyBoundedBy Φ (C ^ 3)

theorem triangular_cyclic_completelyBoundedBy
    (hPublished : PublishedCyclicSimilarity.{u, v} (A := A))
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ a, ‖innerDerivation h (ρ a)‖ ≤ δ * ‖a‖) (ξ : H) :
    let Φ := triangularHilbertRepresentation ρ h δ
    let η := Generator.tupleSingle (1 : Fin 2) ξ
    RepresentationCompletelyBoundedBy (restrictCyclicRepresentation Φ η) 8 := by
  dsimp only
  have hcb := hPublished
    (representationCyclicSpace (triangularHilbertRepresentation ρ h δ)
      (Generator.tupleSingle (1 : Fin 2) ξ))
    (restrictCyclicRepresentation _ _)
    ⟨representationCyclicVector _ _, restrictCyclicRepresentation_cyclic _ _⟩
    2 (by norm_num) (fun a =>
      (norm_restrictCyclicRepresentation_le _ _ a).trans
        (norm_triangularHilbertRepresentation_le_two ρ h hδ hbound a))
  norm_num at hcb
  exact hcb

/-- Haagerup's cyclic bound controls the commutator column on every vector. -/
theorem commutator_column_vector_bound
    (hPublished : PublishedCyclicSimilarity.{u, v} (A := A))
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ a, ‖innerDerivation h (ρ a)‖ ≤ δ * ‖a‖)
    (p : ℕ) (X : CStarMatrix (Fin p) (Fin 1) A) (ξ : H) :
    ‖WithLp.toLp 2 (fun i => innerDerivation h (ρ (X i 0)) ξ)‖ ≤
      8 * δ * ‖X‖ * ‖ξ‖ := by
  let Φ := triangularHilbertRepresentation ρ h δ
  let η := Generator.tupleSingle (1 : Fin 2) ξ
  have hnorm := cyclic_column_coordinate_bound Φ η
    (triangular_cyclic_completelyBoundedBy hPublished ρ h hδ hbound ξ) p X
  have heq : WithLp.toLp 2 (fun i => Φ (X i 0) η 0) =
      ((δ⁻¹ : ℝ) : ℂ) • WithLp.toLp 2 (fun i => innerDerivation h (ρ (X i 0)) ξ) := by
    ext i
    exact triangularHilbertRepresentation_apply_upper ρ h δ (X i 0) ξ
  change ‖WithLp.toLp 2 (fun i => Φ (X i 0) η 0)‖ ≤ 8 * ‖X‖ * ‖η‖ at hnorm
  have hη : ‖η‖ = ‖ξ‖ := norm_tupleSingle (1 : Fin 2) ξ
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hδ), hη] at hnorm
  have hmul := mul_le_mul_of_nonneg_left hnorm hδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at hmul
  calc
    _ ≤ δ * (8 * ‖X‖ * ‖ξ‖) := hmul
    _ = 8 * δ * ‖X‖ * ‖ξ‖ := by ring

/-- The manuscript's column-commutator estimate, conditional only on
Haagerup's cyclic similarity theorem. -/
theorem commutator_column_bound
    (hPublished : PublishedCyclicSimilarity.{u, v} (A := A))
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ a, ‖innerDerivation h (ρ a)‖ ≤ δ * ‖a‖)
    (p : ℕ) (X : CStarMatrix (Fin p) (Fin 1) A) :
    ‖CStarMatrix.mapₗ ((innerDerivation h).comp ρ.toAlgHom.toLinearMap) X‖ ≤
      8 * δ * ‖X‖ := by
  obtain rfl | hδ := hδ.eq_or_lt
  · have hz (a : A) : innerDerivation h (ρ a) = 0 :=
      norm_eq_zero.mp (le_antisymm (by simpa using hbound a) (norm_nonneg _))
    have hmat : CStarMatrix.mapₗ ((innerDerivation h).comp ρ.toAlgHom.toLinearMap) X = 0 := by
      apply CStarMatrix.ext
      intro i j
      exact hz (X i j)
    simp [hmat]
  · rw [← norm_rectangularHilbertMatrix]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    have hy : rectangularHilbertMatrix
        (CStarMatrix.mapₗ ((innerDerivation h).comp ρ.toAlgHom.toLinearMap) X) y =
        WithLp.toLp 2 (fun i => innerDerivation h (ρ (X i 0)) (y 0)) := by
      ext i
      simp [rectangularHilbertMatrix_apply]
    rw [hy]
    exact (commutator_column_vector_bound hPublished ρ h hδ hbound p X (y 0)).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le y 0) (by positivity))

/-- The intrinsic scalar norm of the commutator controls every finite column. -/
theorem commutator_column_norm_bound
    (hPublished : PublishedCyclicSimilarity.{u, v} (A := A))
    (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (h : H →L[ℂ] H)
    (p : ℕ) (X : CStarMatrix (Fin p) (Fin 1) A) :
    ‖CStarMatrix.mapₗ (representedInnerDerivation ρ h).toLinearMap X‖ ≤
      8 * ‖representedInnerDerivation ρ h‖ * ‖X‖ := by
  exact commutator_column_bound hPublished ρ h (norm_nonneg _)
    (fun a => (representedInnerDerivation ρ h).le_opNorm a) p X

end

end KadisonKastler

end OAI
