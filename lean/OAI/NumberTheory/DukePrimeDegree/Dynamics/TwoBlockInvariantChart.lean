import OAI.NumberTheory.DukePrimeDegree.Dynamics.TwoBlockIndexTransport
import OAI.NumberTheory.DukePrimeDegree.Dynamics.NeutralBlockLocalInvariance
import OAI.NumberTheory.DukePrimeDegree.Geometry.RightHaarProduct

namespace OAI

/-!
# The two-block chart for the actual invariant lattice measure

The neutral subgroup here is the preimage of the actual measure
stabilizer. Its openness is deduced from within-block root invariance
and diagonal invariance, and covering-lift invariance supplies the
translation invariance in the parabolic coordinates.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

theorem isClosed_twoBlockNeutralGroup (a b : ℕ) :
    IsClosed (twoBlockNeutralGroup a b : Set (TwoBlockSL a b)) := by
  change IsClosed {g : TwoBlockSL a b |
    g.val * twoBlockProjection a b = twoBlockProjection a b * g.val}
  exact isClosed_eq (continuous_subtype_val.mul continuous_const)
    (continuous_const.mul continuous_subtype_val)

theorem twoBlockNeutralGroup_locallyCompact (a b : ℕ) :
    LocallyCompactSpace (twoBlockNeutralGroup a b) := by
  let : LocallyCompactSpace (Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℝ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin a ⊕ Fin b) → (Fin a ⊕ Fin b) → ℝ))
  let : LocallyCompactSpace (TwoBlockSL a b) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace
  exact (isClosed_twoBlockNeutralGroup a b).locallyCompactSpace

def twoBlockMeasureStabilizer {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (μ : Measure (X n)) : Subgroup (twoBlockNeutralGroup a b) :=
  (invariantRightSubgroup μ).comap
    ((twoBlockReindex e).symm.toMonoidHom.comp (twoBlockNeutralGroup a b).subtype)

theorem isOpen_twoBlockMeasureStabilizer {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (hn : n ≠ 0) (μ : Measure (X n))
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), (twoBlockIndexSetoid e) i j → ∀ t : ℝ,
      μ.map (fun x => rightAction x (SpecialLinearGroup.transvection hij t)) = μ)
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      μ.map (fun x => rightAction x (diagonalOneParameter v hv t)) = μ) :
    IsOpen (twoBlockMeasureStabilizer e μ : Set (twoBlockNeutralGroup a b)) := by
  have hB := open_block_stabilizer_of_roots_and_diagonals hn
    (twoBlockIndexSetoid e) μ hroot hdiag
  exact hB.preimage (twoBlockNeutralIndexHomeomorph e).symm.continuous

def twoBlockLiftMeasure {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (μ : Measure (X n)) (s : X n → G n) : Measure (TwoBlockSL a b) :=
  (quotientLiftMeasure n μ s).map (twoBlockReindexHomeomorph e)

theorem twoBlockLiftMeasure_right_invariant {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x) = x)
    (h : twoBlockMeasureStabilizer e μ) :
    (twoBlockLiftMeasure e μ s).map (fun g => g * h.val.val) =
      twoBlockLiftMeasure e μ s := by
  let c := (twoBlockReindex e).symm h.val.val
  have hc : μ.map (fun x => rightAction x c) = μ := h.property
  have he : (fun g : G n => twoBlockReindex e g * h.val.val) =
      (fun g : G n => twoBlockReindex e (g * c)) := by
    funext g
    rw [map_mul, MulEquiv.apply_symm_apply]
  change ((quotientLiftMeasure n μ s).map (twoBlockReindexHomeomorph e)).map
    (fun g => g * h.val.val) = _
  rw [Measure.map_map (by fun_prop) (twoBlockReindexHomeomorph e).measurable]
  change (quotientLiftMeasure n μ s).map (fun g => twoBlockReindex e g * h.val.val) = _
  rw [he]
  calc
    (quotientLiftMeasure n μ s).map (fun g => twoBlockReindex e (g * c)) =
        ((quotientLiftMeasure n μ s).map (fun g => g * c)).map
          (twoBlockReindexHomeomorph e) :=
      (Measure.map_map (twoBlockReindexHomeomorph e).measurable
        (continuous_mul_const c).measurable).symm
    _ = twoBlockLiftMeasure e μ s := by
      rw [quotientLiftMeasure_right_invariant n μ s hsm hs c hc]
      rfl

def actualTwoBlockCoordinateMeasure {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (μ : Measure (X n)) (s : X n → G n) :
    Measure (TwoBlockTransverse a b × twoBlockMeasureStabilizer e μ) :=
  twoBlockLocalNeutralMeasure (twoBlockMeasureStabilizer e μ) (twoBlockLiftMeasure e μ s)

theorem actualTwoBlockCoordinateMeasure_right_invariant {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (hn : n ≠ 0) (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x) = x)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), (twoBlockIndexSetoid e) i j → ∀ t : ℝ,
      μ.map (fun x => rightAction x (SpecialLinearGroup.transvection hij t)) = μ)
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      μ.map (fun x => rightAction x (diagonalOneParameter v hv t)) = μ)
    (h : twoBlockMeasureStabilizer e μ) :
    (actualTwoBlockCoordinateMeasure e μ s).map (fun z => (z.1, z.2 * h)) =
      actualTwoBlockCoordinateMeasure e μ s :=
  twoBlockLocalNeutralMeasure_right_invariant _
    (isOpen_twoBlockMeasureStabilizer e hn μ hroot hdiag) _ h
    (twoBlockLiftMeasure_right_invariant e μ s hsm hs h)

theorem actualTwoBlockCoordinateMeasure_finiteOnCompacts {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (hn : n ≠ 0) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x) = x)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), (twoBlockIndexSetoid e) i j → ∀ t : ℝ,
      μ.map (fun x => rightAction x (SpecialLinearGroup.transvection hij t)) = μ)
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      μ.map (fun x => rightAction x (diagonalOneParameter v hv t)) = μ) :
    IsFiniteMeasureOnCompacts (actualTwoBlockCoordinateMeasure e μ s) := by
  let := quotientLiftMeasure_locallyFinite n μ s hsm hs
  let : IsFiniteMeasureOnCompacts (twoBlockLiftMeasure e μ s) :=
    Measure.IsFiniteMeasureOnCompacts.map (quotientLiftMeasure n μ s) (twoBlockReindexHomeomorph e)
  exact twoBlockLocalNeutralMeasure_finiteOnCompacts _
    (isOpen_twoBlockMeasureStabilizer e hn μ hroot hdiag) _

/-- The neutral factor is right Haar on the actual open invariant subgroup.
There is no assertion that it is left Haar or that its modular character
vanishes. -/
theorem actualTwoBlockCoordinateMeasure_product {n a b : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (hn : n ≠ 0) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x) = x)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), (twoBlockIndexSetoid e) i j → ∀ t : ℝ,
      μ.map (fun x => rightAction x (SpecialLinearGroup.transvection hij t)) = μ)
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      μ.map (fun x => rightAction x (diagonalOneParameter v hv t)) = μ)
    (η : Measure (twoBlockMeasureStabilizer e μ)) [η.inv.IsHaarMeasure]
    (K : Set (twoBlockMeasureStabilizer e μ)) (hK : IsCompact K) (hηK : η K = 1) :
    actualTwoBlockCoordinateMeasure e μ s =
      (firstCoordinateSlice (actualTwoBlockCoordinateMeasure e μ s) K).prod η := by
  let : SecondCountableTopology (twoBlockNeutralGroup a b) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (Subtype.val : twoBlockNeutralGroup a b → TwoBlockSL a b)).secondCountableTopology
  let : SecondCountableTopology (twoBlockMeasureStabilizer e μ) :=
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
      (Subtype.val : twoBlockMeasureStabilizer e μ → twoBlockNeutralGroup a b)).secondCountableTopology
  let : LocallyCompactSpace (TwoBlockTransverse a b) :=
    inferInstanceAs (LocallyCompactSpace ((Fin b → Fin a → ℝ) × (Fin a → Fin b → ℝ)))
  let := twoBlockNeutralGroup_locallyCompact a b
  let := (isOpen_twoBlockMeasureStabilizer e hn μ hroot hdiag).locallyCompactSpace
  let := actualTwoBlockCoordinateMeasure_finiteOnCompacts e hn μ s hsm hs hroot hdiag
  exact rightInvariant_eq_product _
    (fun h => actualTwoBlockCoordinateMeasure_right_invariant e hn μ s hsm hs hroot hdiag h)
    η K hK hηK

end DukePrimeDegree

end

end OAI
