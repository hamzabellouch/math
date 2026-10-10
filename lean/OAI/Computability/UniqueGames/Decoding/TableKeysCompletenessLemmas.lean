import OAI.Computability.UniqueGames.Decoding.TableKeysAddressGameLemmas
import OAI.Computability.UniqueGames.Decoding.TableKeysGame
import OAI.Computability.UniqueGames.Reduction.ActualCompleteness

namespace OAI

section

/-!
Completeness of the v2 single-orbit matrix game. The generic finite-average
calculation is shared with the proved actual completeness calculation. Its
reuse is justified below by pointwise equality of restored answers under
diagonal labels; the output vertices themselves are never doubled.

No gadget existence, dispersion hypothesis, inverse theorem, or legacy
soundness theorem is a premise. The bound includes the exact fair-bit factor
`1 / 2`, and is a statement about the actual finite edge occurrence list.
-/

namespace UniqueGamesTheorem.Decoder.TableKeysCompleteness

open UniqueGamesTheorem.Integration.BinaryLinear UniqueGamesTheorem.Reduction
open ActualSource Foundations.Target
open TableKeysGame
open scoped BigOperators

noncomputable section

/-- Use a single label function on both auxiliary sides, solely to share the
already proved finite-average calculation. This does not change the v2 game. -/
def diagonalLabeling (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Fin (ActualGame.vertexCount S k s d) → Fin (2^s) :=
  ActualGame.labelingOf S k s d (fun _ => vertexLabel S k s d labeling)

theorem diagonal_unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (side : Bool) (q : Query S k s d) :
    ActualGame.unfolded S k s d (diagonalLabeling S k s d labeling) side q =
      unfolded S k s d labeling q := by
  simp only [diagonalLabeling, ActualGame.unfolded,
    ActualGame.sideLabel_labelingOf, unfolded, canonical]

/-- Pointwise-identical matrix tests have exactly the same acceptance average. -/
theorem acceptanceProbability_eq_diagonal (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      ActualGame.acceptanceProbability S k g (diagonalLabeling S k s d labeling) := by
  rw [acceptanceProbability_eq_test, ActualGame.acceptanceProbability_eq_test]
  simp only [diagonal_unfolded, leftQuery, rightQuery]

def honestLabeling (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (A : Fin S.variables → Bool) : Fin (vertexCount S k s d) → Fin (2^s) :=
  labelingOf S k s d (ActualCompleteness.honestVertexLabel S k g A)

theorem diagonal_honestLabeling (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    diagonalLabeling S k s d (honestLabeling S k g A) =
      ActualCompleteness.honestLabeling S k g A := by
  simp only [diagonalLabeling, honestLabeling, vertexLabel_labelingOf,
    ActualCompleteness.honestLabeling]

/-- The removed affine intercept is recovered by gadget equivariance. -/
theorem honest_unfolded (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) (q : Query S k s d) :
    unfolded S k s d (honestLabeling S k g A) q =
      g.f (ActualCompleteness.evaluate (ActualGame.names S) (fun n => ofBit (A n))
        (canonical S k s d q)) := by
  rw [← diagonal_unfolded S k s d _ false q, diagonal_honestLabeling]
  exact ActualCompleteness.honest_unfolded S k g A false q

/-- On a satisfied tuple, every sampled table evaluates the same homogeneous
answer with first coordinate one. -/
theorem honest_unfolded_valid (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) (q : Query S k s d)
    (hgood : ∀ j, S.satisfied A (q.1 j) = true) :
    unfolded S k s d (honestLabeling S k g A) q =
      g.f (q.2 (ActualCompleteness.sourcePoint S k A q.1)) := by
  rw [← diagonal_unfolded S k s d _ false q, diagonal_honestLabeling]
  exact ActualCompleteness.honest_unfolded_valid S k g A false q hgood

theorem honest_acceptance_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      acceptanceProbability S k g (honestLabeling S k g A) := by
  rw [acceptanceProbability_eq_diagonal, diagonal_honestLabeling]
  exact ActualCompleteness.honest_acceptance_bound S k g A

theorem honest_acceptance_of_bounds (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) (ξ p ε : ℚ)
    (hsource : S.failure A ≤ ξ) (hstable : g.stabilityError ≤ p)
    (hbudget : (k : ℚ) * ξ + p / 2 ≤ ε) :
    1 - ε ≤ acceptanceProbability S k g (honestLabeling S k g A) := by
  have hm := mul_le_mul_of_nonneg_left hsource (show (0 : ℚ) ≤ k by positivity)
  have hactual := honest_acceptance_bound S k g A
  linarith

/-- Completeness is measured on the generated single-orbit edge occurrences. -/
theorem honest_satisfied_fraction_bound (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) :
    1 - (k : ℚ) * S.failure A - g.stabilityError / 2 ≤
      (countSatisfied (honestLabeling S k g A)
        (outputInstance S k g).constraints : ℚ) /
        (outputInstance S k g).constraints.length := by
  rw [← acceptanceProbability_eq_count]
  exact honest_acceptance_bound S k g A

theorem completeAt (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (A : Fin S.variables → Bool) (error : RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    CompleteAt error (outputInstance S k g) := by
  apply (Integration.GapSemantics.completeAt_iff error _).2
  refine ⟨honestLabeling S k g A, ?_⟩
  change 1 - Integration.GapSemantics.errorValue error ≤
    (countSatisfied (honestLabeling S k g A)
      (outputInstance S k g).constraints : ℚ) /
      (outputInstance S k g).constraints.length
  have h := honest_satisfied_fraction_bound S k g A
  linarith

theorem completeAt_withEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (A : Fin S.variables → Bool) (error : RationalError)
    (hbudget : (k : ℚ) * S.failure A + g.stabilityError / 2 ≤
      Integration.GapSemantics.errorValue error) :
    CompleteAt error (outputInstanceWithEnumeration S k g en) := by
  apply (completeAt_outputInstanceWithEnumeration_iff error S k g en).2
  exact completeAt S k g A error hbudget

end

end UniqueGamesTheorem.Decoder.TableKeysCompleteness

end

section

/-!
Completeness on the actual single-orbit address output. An honest semantic
labeling is extended over unused addresses, with its satisfied fraction
unchanged. The two rational error bounds need no packaged error parameter.
-/

namespace UniqueGamesTheorem.Decoder.MatrixGap

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Reduction UniqueGamesTheorem.Foundations.Target
open UniqueGamesTheorem.Integration
open ActualSource

noncomputable section

/-- Every semantic labeling extends to a labeling of the padded address space.
The generated edge list retains its exact acceptance fraction. -/
theorem semantic_acceptance_le_address_value (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s)) :
    (TableKeysGame.acceptanceProbability S k g labeling : ℝ) ≤
      InstanceValue.value (TableKeysAddressGame.outputInstance S k g en) := by
  let e := TableKeysGame.semanticToExplicitVertices S k s d
  let addressLabel := VertexEmbedding.extendLabeling
    (TableKeysAddressGame.explicitToAddress S k s d) (labeling ∘ e.symm)
      (⟨0, by positivity⟩ : Fin (2 ^ s))
  have hrestrict : addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d =
      labeling ∘ e.symm :=
    VertexEmbedding.extendLabeling_comp _
      (TableKeysAddressGame.explicitToAddress_injective S k s d) _ _
  have hpullback : (addressLabel ∘ TableKeysAddressGame.explicitToAddress S k s d) ∘
      TableKeysGame.semanticToExplicitVertices S k s d = labeling := by
    rw [hrestrict]
    funext v
    exact congrArg labeling (e.symm_apply_apply v)
  have hrate := address_rate_eq_semantic_acceptance S k g en addressLabel
  rw [hpullback] at hrate
  have hvalue := InstanceValue.satisfactionRate_le_value
    (TableKeysAddressGame.outputInstance S k g en) addressLabel
  rw [hrate] at hvalue
  exact hvalue

/-- The exact near-assignment loss and fair-bit factor one half, measured on
the generated address instance and then cast to its real optimum value. -/
theorem address_value_ge_of_near_assignment (S : Source) (k : Nat) {s d : Nat}
    (T : NoiseTables.Table s d) (f : Ambient s d → Alphabet s)
    (hf : ∀ x c, f (x + (c, 0)) = f x + c)
    (assignment : Fin S.variables → Bool) (ξ p : ℚ)
    (hfailure : S.failure assignment ≤ ξ)
    (hstable : (T.gadget f hf).stabilityError ≤ p) :
    (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      InstanceValue.value (TableKeysAddressGame.tableOutput S k T) := by
  let g := T.gadget f hf
  have hrat := TableKeysCompleteness.honest_acceptance_of_bounds S k g assignment
    ξ p ((k : ℚ) * ξ + p / 2) hfailure hstable (le_refl _)
  have hreal : (1 : ℝ) - ((k : ℝ) * (ξ : ℝ) + (p : ℝ) / 2) ≤
      (TableKeysGame.acceptanceProbability S k g
        (TableKeysCompleteness.honestLabeling S k g assignment) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).2 hrat
    simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_add, Rat.cast_mul,
      Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] using h
  rw [TableKeysAddressGame.tableOutput_eq_with_witness S k T f hf]
  exact hreal.trans (semantic_acceptance_le_address_value S k g
    (TableReduction.tableEnumeration T f hf)
    (TableKeysCompleteness.honestLabeling S k g assignment))

end
end UniqueGamesTheorem.Decoder.MatrixGap

end

end OAI
