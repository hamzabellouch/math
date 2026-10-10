import OAI.Analysis.KadisonKastler.SupportColumn
import OAI.Analysis.KadisonKastler.SupportBounds

namespace OAI

/-! # The clipped coefficient-column drift

Finite matrix averaging preserves the scalar derivation bound. The support
column estimate and the through-label square sum give `64δ` for the averaged
operator; its distance at most `δ` from the original operator costs `2δ`.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {n q : ℕ}

local instance clippedDriftOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance clippedDriftOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance clippedDriftAlgebraOrder (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance clippedDriftAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The matrix commutator acts as the ordinary commutator on the Hilbert direct sum. -/
theorem hilbertMatrix_matrixCommutator (h : H →L[ℂ] H)
    (K : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)) :
    hilbertMatrix (matrixCommutator h K) =
      hilbertMatrix (diagonalAmplification (n := Fin n) h) * hilbertMatrix K -
        hilbertMatrix K * hilbertMatrix (diagonalAmplification (n := Fin n) h) := by
  rw [matrixCommutator_eq_diagonal]
  change (hilbertMatrixHom (H := H) (n := Fin n))
    (diagonalAmplification (n := Fin n) h * K - K * diagonalAmplification (n := Fin n) h) = _
  rw [map_sub, map_mul, map_mul]
  rfl

/-- A support projection is the sum of its actual Hilbert-space diagonal atoms. -/
theorem hilbertMatrix_supportProjection
    (E : Generator.MatrixUnitSystem (Fin q) (H →L[ℂ] H))
    (S : Finset (Fin n × Fin q)) :
    hilbertMatrix (supportProjection E S) =
      ∑ a ∈ S, hilbertMatrix (supportAtom E a) := by
  rw [supportProjection_eq_sum]
  exact map_sum (hilbertMatrixHom (H := H)) (fun a => supportAtom E a) S

/-- The original implementing operator moves the contractive clipped
coefficient column by at most `66δ`. -/
theorem clipped_coefficient_drift_le_sixty_six {ω : Type*} [Fintype ω]
    (M : VonNeumannAlgebra H)
    (hPublished : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (E : Generator.MatrixUnitSystem (Fin q) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra)
    (S : ω → Finset (Fin n × Fin q)) (hS : ∀ w, (S w).card ≤ q)
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hKmem : ∀ w i j, K w i j ∈ M)
    (hKsupport : ∀ w, K w = K w * supportProjection E (S w))
    (β : ω → ℝ) (hKnorm : ∀ w, ‖K w‖ ≤ β w)
    (hKcontract : ∀ y : Generator.FiniteHilbert (Fin n) H,
      ‖WithLp.toLp 2 (fun w => hilbertMatrix (K w) y)‖ ≤ ‖y‖)
    (hβ : ∀ a : Fin n × Fin q, (∑ w : ω, if a ∈ S w then β w ^ 2 else 0) ≤ 64)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (z : Generator.FiniteHilbert (Fin n) H) :
    ‖WithLp.toLp 2 (fun w =>
      (hilbertMatrix (diagonalAmplification (n := Fin n) h) * hilbertMatrix (K w) -
        hilbertMatrix (K w) * hilbertMatrix (diagonalAmplification (n := Fin n) h)) z)‖ ≤
      66 * δ * ‖z‖ := by
  obtain ⟨h0, hcomm, hclose, hbound, _⟩ := exists_matrixUnitAverage M E hE h hδ hb
  let P : Fin n × Fin q → Generator.FiniteHilbert (Fin n) H →L[ℂ]
      Generator.FiniteHilbert (Fin n) H := fun a => hilbertMatrix (supportAtom E a)
  have hPself (a : Fin n × Fin q) : IsSelfAdjoint (P a) :=
    ((supportAtom_projection E a).map (hilbertMatrixHom (H := H))).isSelfAdjoint
  have hPorth (a b : Fin n × Fin q) (hab : a ≠ b) : P a * P b = 0 := by
    change (hilbertMatrixHom (H := H) (n := Fin n)) (supportAtom E a) * (hilbertMatrixHom (H := H) (n := Fin n)) (supportAtom E b) = 0
    rw [← map_mul, supportAtom_orthogonal E a b hab, map_zero]
  have hPtotal : ∑ a, P a = 1 := by
    change ∑ a, (hilbertMatrixHom (H := H) (n := Fin n)) (supportAtom E a) = 1
    rw [← map_sum, supportAtom_total, map_one]
  let h0n := hilbertMatrix (diagonalAmplification (n := Fin n) h0)
  let hn := hilbertMatrix (diagonalAmplification (n := Fin n) h)
  let KOp := fun w => hilbertMatrix (K w)
  have hind (w : ω) :
      ‖(h0n * KOp w - KOp w * h0n) z‖ ≤ 8 * δ * β w * ‖(∑ a ∈ S w, P a) z‖ := by
    have ht := small_support_commutator_bound M hPublished n q E hE (S w) (hS w)
      (K w) (hKmem w) (hKsupport w) h0 hδ hbound
      (fun a ha => (hcomm a ha).symm) z
    change ‖hilbertMatrix (matrixCommutator h0 (K w)) z‖ ≤
      8 * δ * ‖K w‖ * ‖hilbertMatrix (supportProjection E (S w)) z‖ at ht
    rw [hilbertMatrix_matrixCommutator, hilbertMatrix_supportProjection] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hKnorm w) (by positivity)) (norm_nonneg _))
  have havg : ‖WithLp.toLp 2 (fun w => (h0n * KOp w - KOp w * h0n) z)‖ ≤
      64 * δ * ‖z‖ :=
    support_drift_le_sixty_four P S β hPself hPorth hPtotal hβ hδ
      (fun w => (h0n * KOp w - KOp w * h0n) z) z hind
  have hcloseN : ‖hn - h0n‖ ≤ δ := by
    have heq : hn - h0n = hilbertMatrix (diagonalAmplification (n := Fin n) (h - h0)) := by
      rw [diagonalAmplification_sub]
      exact (map_sub (hilbertMatrixHom (H := H)) _ _).symm
    rw [heq, norm_hilbertMatrix]
    exact (norm_diagonalAmplification_le _).trans hclose
  exact coefficient_drift_le_sixty_six KOp hKcontract hn h0n hcloseN z havg

/-- The same estimate expressed entrywise in the original operator algebra. -/
theorem clipped_matrixCommutator_drift_le_sixty_six {ω : Type*} [Fintype ω]
    (M : VonNeumannAlgebra H)
    (hPublished : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
    (E : Generator.MatrixUnitSystem (Fin q) (H →L[ℂ] H))
    (hE : E.algebra ≤ M.toStarSubalgebra)
    (S : ω → Finset (Fin n × Fin q)) (hS : ∀ w, (S w).card ≤ q)
    (K : ω → CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hKmem : ∀ w i j, K w i j ∈ M)
    (hKsupport : ∀ w, K w = K w * supportProjection E (S w))
    (β : ω → ℝ) (hKnorm : ∀ w, ‖K w‖ ≤ β w)
    (hKcontract : ∀ y : Generator.FiniteHilbert (Fin n) H,
      ‖WithLp.toLp 2 (fun w => hilbertMatrix (K w) y)‖ ≤ ‖y‖)
    (hβ : ∀ a : Fin n × Fin q, (∑ w : ω, if a ∈ S w then β w ^ 2 else 0) ≤ 64)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (z : Generator.FiniteHilbert (Fin n) H) :
    ‖WithLp.toLp 2 (fun w => hilbertMatrix (matrixCommutator h (K w)) z)‖ ≤
      66 * δ * ‖z‖ := by
  simp_rw [hilbertMatrix_matrixCommutator]
  exact clipped_coefficient_drift_le_sixty_six M hPublished E hE S hS K hKmem
    hKsupport β hKnorm hKcontract hβ h hδ hb z

end

end KadisonKastler

end OAI
