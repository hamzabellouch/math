import OAI.Analysis.KadisonKastler.ConcreteClippedDrift
import OAI.Analysis.KadisonKastler.UltrapowerExpectation

namespace OAI

/-! # The restored 66- and 68-delta coefficient estimates

The concrete support estimate and the trace quotient give the two
coefficient bounds used in phase averaging. In the moving-vector
estimate, the only extra term is the `2δ` commutator of the free lift.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

universe u


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k : ℕ} {W : Type*} [Fintype W]
variable {B : Type*} [CStarAlgebra B] {σ : FaithfulTracialState B} {ω : Ultrafilter ℕ}
variable {τ : FaithfulTracialState (Algebra (matrixVonNeumann (ι := Fin n) M))}

local instance coefficientOriginalOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance coefficientOriginalStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

local instance coefficientSourceOrder :
    PartialOrder (Algebra (matrixVonNeumann (ι := Fin n) M)) := CStarAlgebra.spectralOrder _
local instance coefficientSourceStarOrder :
    StarOrderedRing (Algebra (matrixVonNeumann (ι := Fin n) M)) :=
  CStarAlgebra.spectralOrderedRing _
local instance coefficientTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder _
local instance coefficientTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _

variable (R : TraceQuotientMap τ σ ω) (hτ : FiniteVectorTrace τ)
variable (hPublished : PublishedCyclicSimilarity.{u, u} (A := Algebra M))
variable (E : Generator.MatrixUnitSystem (Fin k) (H →L[ℂ] H))
variable (hE : E.algebra ≤ M.toStarSubalgebra)
variable (S : W → Finset (Fin n × Fin k)) (hS : ∀ w, (S w).card ≤ k)
variable (K : W → BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M)))
variable (hKsupport : ∀ j w, concreteMatrixEntries (M := M) (n := n) (K w j) =
  concreteMatrixEntries (M := M) (n := n) (K w j) * supportProjection E (S w))
variable (β : W → ℝ) (hβpos : ∀ w, 0 < β w)
variable (hKcontract : ∀ (j : ℕ) (z : Generator.FiniteHilbert (Fin n) H),
  ‖WithLp.toLp 2 (fun w => (K w j).val z)‖ ≤ ‖z‖)
variable (hβ : ∀ a : Fin n × Fin k, (∑ w : W, if a ∈ S w then β w ^ 2 else 0) ≤ 64)
variable (hbound : ∀ w, ‖R.quotient (K w)‖ ≤ β w)
variable (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
variable (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)

include R hτ hPublished E hE S hS hKsupport β hβpos hKcontract hβ hbound hδ hb in
/-- Restoring the finite coefficient column on a fixed vector retains
its `66δ` estimate in the ultrafilter limit. -/
theorem concrete_coefficient_drift_fixed (z : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖WithLp.toLp 2 (fun w => (T * (K w j).val - (K w j).val * T) z)‖ ≤
        66 * δ * ‖z‖ + ε := by
  apply R.isTraceQuotient.eventually_coefficient_drift hτ.strongContinuous K β hβpos hbound
  intro j
  exact concrete_spectralClipped_drift_le hPublished E hE S hS
    (fun w => K w j) (hKsupport j) β hβpos (hKcontract j) hβ h hδ hb z

include R hτ hPublished E hE S hS hKsupport β hβpos hKcontract hβ hbound hδ hb in
/-- A unitary lift with coordinate commutator bound `2δ` gives the
`68δ` estimate on its moving vectors. -/
theorem concrete_coefficient_drift_moving
    (s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (hs : ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val - ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ)
    (y : Generator.FiniteHilbert (Fin n) H) :
    ∀ ε > 0, ∀ᶠ j in (ω : Filter ℕ),
      let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
      ‖WithLp.toLp 2 (fun w => (T * (K w j).val - (K w j).val * T)
        (((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val y))‖ ≤ 68 * δ * ‖y‖ + ε := by
  let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
  have hsnorm (j : ℕ) : ‖((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val y‖ = ‖y‖ := by
    let u := Unitary.map (StarMonoidHom.ofClass
      ((matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype.comp
        (boundedSequenceEval (B := Algebra (matrixVonNeumann (ι := Fin n) M)) j))) s
    exact Unitary.norm_map u y
  have hclip (j : ℕ) : ‖WithLp.toLp 2 (fun w =>
      (T * (spectralClip (β w) (K w j)).val -
        (spectralClip (β w) (K w j)).val * T)
          (((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val y))‖ ≤ 66 * δ * ‖y‖ := by
    simpa only [hsnorm] using concrete_spectralClipped_drift_le hPublished E hE S hS
      (fun w => K w j) (hKsupport j) β hβpos (hKcontract j) hβ h hδ hb
      (((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val y)
  have hcomm (j : ℕ) :
      ‖(T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val - ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T) y‖ ≤
        2 * δ * ‖y‖ :=
    ((T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
      ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T).le_opNorm y).trans
        (mul_le_mul_of_nonneg_right (hs j) (norm_nonneg y))
  have ht := R.isTraceQuotient.eventually_moving_coefficient_drift hτ.strongContinuous
    K β hβpos hbound hKcontract (s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) T y hclip hcomm
  have hnum : 66 * δ * ‖y‖ + 2 * δ * ‖y‖ = 68 * δ * ‖y‖ := by ring
  rw [hnum] at ht
  exact ht

end

end KadisonKastler

end OAI
