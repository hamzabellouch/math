import OAI.AlgebraicGeometry.StableCoordinate.NormalizedDeterminantLift
import OAI.AlgebraicGeometry.StableCoordinate.FrameLiftCoassoc
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantLiftWeights
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantActionWeights
import OAI.AlgebraicGeometry.StableCoordinate.LNDAction
import OAI.AlgebraicGeometry.StableCoordinate.ObstructionPrincipalization

namespace OAI

/-!
# The actual weight-preserving locally nilpotent lift

This file completes source Proposition `prop:lift` for the exact rings `B` and
`C`.  There is no assumed action lift or line-bundle trivialization: the genuine
UFD structure of `C[T]` gives a determinant frame, its constant-unit
normalization gives a polynomial family, and normalized-frame uniqueness proves
the additive group law.  A second use of uniqueness proves fiber-scaling
equivariance.  Differentiation therefore gives a locally nilpotent derivation
that extends the given one and preserves the actual constructed fiber grading.

Finally, injectivity of `B → C`, the identity `IC = (v)`, and factorial closure
of an LND kernel transport a nonzero invariant in `I` to the condition `D(v)=0`.
All intermediate existence and equivariance interfaces are discharged here.
-/

noncomputable section

namespace StableCoordinate.Obstruction

open CoactionLND

variable {k : Type*} [Field k]

/-- The actual additive action on the determinant ring lifting a given action
on the quadric ring.  Its group law is a theorem of normalized-frame uniqueness. -/
def liftedAdditiveAction (α : PolynomialAdditiveAction k (B k)) :
    PolynomialAdditiveAction k (C k) :=
  FrameLiftCoassoc.actionOfNormalizedExtension α
    (NormalizedDeterminantLift.liftHom α)
    (NormalizedDeterminantLift.liftHom_identity α)
    (NormalizedDeterminantLift.liftHom_baseMap α)

@[simp] theorem liftedAdditiveAction_toAlgHom
    (α : PolynomialAdditiveAction k (B k)) :
    (liftedAdditiveAction α).toAlgHom = NormalizedDeterminantLift.liftHom α := rfl

/-- The constructed action is equivariant for the actual injective base map. -/
theorem liftedAdditiveAction_baseMap (α : PolynomialAdditiveAction k (B k))
    (b : B k) :
    (liftedAdditiveAction α).toAlgHom (baseMap k b) =
      (α.toAlgHom b).map (baseMap k).toRingHom :=
  NormalizedDeterminantLift.liftHom_baseMap α b

/-- Differentiation of the constructed action preserves every actual fiber
weight submodule.  The five coefficient laws are proved, not hypothesized. -/
theorem liftedAdditiveAction_derivation_preserves_fiberPiece
    (α : PolynomialAdditiveAction k (B k)) :
    ∀ (n : ℤ) (q : C k), q ∈ fiberPiece k n →
      (liftedAdditiveAction α).derivation q ∈ fiberPiece k n := by
  apply DeterminantActionWeights.derivation_preserves_fiberPiece k
    (NormalizedDeterminantLift.liftHom α)
  · exact DeterminantLiftWeights.generator_coefficient_weights_of_normalized_lift k
      (NormalizedDeterminantLift.liftHom α) α.toAlgHom
      (NormalizedDeterminantLift.liftHom_baseMap α)
      (NormalizedDeterminantLift.liftHom_identity α)
  · intro q
    rfl

variable [CharZero k]

/-- Every locally nilpotent derivation on the exact base quadric admits an
actual locally nilpotent extension preserving the source's fiber grading.
This is the unconditional existence part of source Proposition `prop:lift`. -/
theorem exists_weight_preserving_lnd_lift
    (E : Derivation k (B k) (B k)) (hE : IsLocallyNilpotent E) :
    ∃ D : Derivation k (C k) (C k), IsLocallyNilpotent D ∧
      (∀ b, D (baseMap k b) = baseMap k (E b)) ∧
      (∀ (n : ℤ) (q : C k), q ∈ fiberPiece k n → D q ∈ fiberPiece k n) := by
  let α := exponentialAction E hE
  let β := liftedAdditiveAction α
  refine ⟨β.derivation, β.locallyNilpotent, ?_,
    liftedAdditiveAction_derivation_preserves_fiberPiece α⟩
  intro b
  have h := α.derivation_naturality β (baseMap k)
    (liftedAdditiveAction_baseMap α) b
  simpa only [α, exponentialAction_derivation] using h

/-- Full source lift proposition, retaining the extension equation as well as
the nonzero invariant and grading conclusions required by rigidity. -/
theorem lift_invariant
    (E : Derivation k (B k) (B k)) (hE : IsLocallyNilpotent E) (hE0 : E ≠ 0)
    (hInv : ∃ h : B k, h ∈ I k ∧ h ≠ 0 ∧ E h = 0) :
    ∃ D : Derivation k (C k) (C k), IsLocallyNilpotent D ∧ D ≠ 0 ∧
      (∀ b, D (baseMap k b) = baseMap k (E b)) ∧
      (∀ (n : ℤ) (q : C k), q ∈ fiberPiece k n → D q ∈ fiberPiece k n) ∧
      D (v k) = 0 := by
  obtain ⟨D, hD, hExt, hWeight⟩ := exists_weight_preserving_lnd_lift E hE
  obtain ⟨hD0, hv⟩ := extension_nonzero_and_annihilates_v E D hE0 hD hExt hInv
  exact ⟨D, hD, hD0, hExt, hWeight, hv⟩

/-- The precise existence conclusion needed by the final weight contradiction. -/
theorem exists_nonzero_weight_preserving_lnd_killing_v
    (E : Derivation k (B k) (B k)) (hE : IsLocallyNilpotent E) (hE0 : E ≠ 0)
    (hInv : ∃ h : B k, h ∈ I k ∧ h ≠ 0 ∧ E h = 0) :
    ∃ D : Derivation k (C k) (C k), D ≠ 0 ∧ IsLocallyNilpotent D ∧
      (∀ (n : ℤ) (q : C k), q ∈ fiberPiece k n → D q ∈ fiberPiece k n) ∧
      D (v k) = 0 := by
  obtain ⟨D, hD, hD0, _, hWeight, hv⟩ := lift_invariant E hE hE0 hInv
  exact ⟨D, hD0, hD, hWeight, hv⟩

end StableCoordinate.Obstruction

end

end OAI
