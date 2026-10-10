import OAI.Analysis.KadisonKastler.RegularLocalizationNormal
import OAI.Analysis.KadisonKastler.CanonicalMatrixCorner
import OAI.Analysis.KadisonKastler.InflatedConjugacy

namespace OAI

/-! # Finite scalar-packet compressions

Scalar Hilbert coordinates give finite orthogonal projections on the
regular Hilbert space. Their compressions converge boundedly in the
weak operator topology and have the expected finite packet expansion.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

/-- Scalar coordinates after undoing the gauge in the packet inclusions. -/
def regularGaugedCoordinates : RegularCoreHilbert H ≃ₗᵢ[ℂ] CountableHilbertSum H :=
  (Unitary.linearIsometryEquiv (regularGauge U hU)).trans
    (regularHilbertCoordinates regularScalarBasis)

theorem regularGaugedCoordinates_symm_single (i : ℕ) (x : H) :
    (regularGaugedCoordinates U hU).symm (lp.single 2 i x) =
      regularGaugedPacket U hU (regularScalarBasis i) x := by
  change (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    ((regularHilbertCoordinates regularScalarBasis).symm (lp.single 2 i x)) = _
  have hs : (regularHilbertCoordinates (H := H) regularScalarBasis).symm
      (lp.single 2 i x) = regularTensorVector (regularScalarBasis i) x :=
    (regularHilbertSum regularScalarBasis).linearIsometryEquiv_symm_apply_single x
  rw [hs]
  rfl

theorem regularGaugedCoordinates_apply (f : RegularCoreHilbert H) (i : ℕ) :
    regularGaugedCoordinates U hU f i =
      (regularGaugedPacket U hU (regularScalarBasis i)).adjoint f := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h := (regularGaugedCoordinates U hU).inner_map_map
    ((regularGaugedCoordinates U hU).symm (lp.single 2 i x)) f
  rw [LinearIsometryEquiv.apply_symm_apply,
    regularGaugedCoordinates_symm_single, lp.inner_single_left] at h
  exact h

/-- Projection onto finitely many whole vector-valued scalar packets. -/
def regularPacketProjection (s : Finset ℕ) :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
  (regularGaugedCoordinates U hU).symm.conjStarAlgEquiv
    ((canonicalMatrixCorner H).partialDiagonal s)

private theorem canonical_partialDiagonal_apply (s : Finset ℕ)
    (f : CountableHilbertSum H) (i : ℕ) :
    (canonicalMatrixCorner H).partialDiagonal s f i = if i ∈ s then f i else 0 := by
  classical
  simp only [FullMatrixCorner.partialDiagonal, sum_apply,
    canonicalMatrixCorner_entry, canonicalMatrixUnit_apply, lp.coeFn_sum,
    Finset.sum_apply, lp.single_apply]
  simp

private theorem canonical_partialDiagonal_projection (s : Finset ℕ) :
    IsStarProjection ((canonicalMatrixCorner H).partialDiagonal s) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext i
    change (canonicalMatrixCorner H).partialDiagonal s
      ((canonicalMatrixCorner H).partialDiagonal s f) i = _
    simp only [canonical_partialDiagonal_apply]
    split_ifs <;> rfl
  · exact (canonicalMatrixCorner H).partialDiagonal_star s

theorem regularPacketProjection_isStarProjection (s : Finset ℕ) :
    IsStarProjection (regularPacketProjection U hU s) :=
  (canonical_partialDiagonal_projection (H := H) s).map
    (regularGaugedCoordinates U hU).symm.conjStarAlgEquiv

theorem norm_regularPacketProjection_le (s : Finset ℕ) :
    ‖regularPacketProjection U hU s‖ ≤ 1 :=
  IsStarProjection.norm_le _ (regularPacketProjection_isStarProjection U hU s)

theorem regularPacketProjection_apply (s : Finset ℕ) (f : RegularCoreHilbert H) :
    regularPacketProjection U hU s f =
      ∑ i ∈ s, regularGaugedPacket U hU (regularScalarBasis i)
        ((regularGaugedPacket U hU (regularScalarBasis i)).adjoint f) := by
  change (regularGaugedCoordinates U hU).symm
    ((canonicalMatrixCorner H).partialDiagonal s (regularGaugedCoordinates U hU f)) = _
  simp only [FullMatrixCorner.partialDiagonal, sum_apply,
    canonicalMatrixCorner_entry, canonicalMatrixUnit_apply, map_sum,
    regularGaugedCoordinates_symm_single, regularGaugedCoordinates_apply]

theorem regularPacketProjection_tendsto (f : RegularCoreHilbert H) :
    Tendsto (fun s : Finset ℕ => regularPacketProjection U hU s f) atTop (𝓝 f) := by
  have h := (regularGaugedCoordinates U hU).symm.continuous.continuousAt.tendsto.comp
    ((canonicalMatrixCorner H).partialDiagonal_tendsto (regularGaugedCoordinates U hU f))
  change Tendsto (fun s : Finset ℕ => (regularGaugedCoordinates U hU).symm
    ((canonicalMatrixCorner H).partialDiagonal s (regularGaugedCoordinates U hU f)))
      atTop (𝓝 f)
  simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using h

theorem regularPacketCompression_norm_le
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (s : Finset ℕ) :
    ‖regularPacketProjection U hU s * T * regularPacketProjection U hU s‖ ≤ ‖T‖ := by
  calc
    _ ≤ (‖regularPacketProjection U hU s‖ * ‖T‖) *
        ‖regularPacketProjection U hU s‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := by
      gcongr <;> exact norm_regularPacketProjection_le U hU s
    _ = _ := by ring

/-- The finite packet compressions converge weakly, with their original bound. -/
theorem regularPacketCompression_tendsto_weak
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (f g : RegularCoreHilbert H) :
    Tendsto (fun s : Finset ℕ => inner ℂ g
      ((regularPacketProjection U hU s * T * regularPacketProjection U hU s) f))
      atTop (𝓝 (inner ℂ g (T f))) := by
  have h := (regularPacketProjection_tendsto U hU g).inner (𝕜 := ℂ)
    (T.continuous.continuousAt.tendsto.comp (regularPacketProjection_tendsto U hU f))
  have he (s : Finset ℕ) :
      inner ℂ (regularPacketProjection U hU s g)
        (T (regularPacketProjection U hU s f)) =
      inner ℂ g ((regularPacketProjection U hU s * T *
        regularPacketProjection U hU s) f) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left (regularPacketProjection U hU s)
      (T (regularPacketProjection U hU s f)) g]
    rw [← ContinuousLinearMap.star_eq_adjoint,
      (regularPacketProjection_isStarProjection U hU s).isSelfAdjoint.star_eq]
  exact h.congr he

/-- A finite compression is the finite matrix of its packet coefficients. -/
theorem regularPacketCompression_apply
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (s : Finset ℕ) (f : RegularCoreHilbert H) :
    (regularPacketProjection U hU s * T * regularPacketProjection U hU s) f =
      ∑ i ∈ s, ∑ j ∈ s, regularGaugedPacket U hU (regularScalarBasis i)
        (regularPacketCoefficient U hU T (regularScalarBasis i) (regularScalarBasis j)
          ((regularGaugedPacket U hU (regularScalarBasis j)).adjoint f)) := by
  simp only [mul_apply_eq_comp, regularPacketProjection_apply, map_sum,
    regularPacketCoefficient, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_comm]

end

end KadisonKastler

end OAI
