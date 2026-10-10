import OAI.Analysis.KadisonKastler.ControlledFreeHaar
import OAI.Analysis.KadisonKastler.MatrixLiftBounds

namespace OAI

/-! # Free Haar representatives with the scalar commutator bound

The finite-matrix representatives constructed by the two independence
applications retain the dimension-free `2δ` commutator estimate in the
original normal representation.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n j : ℕ} [NeZero n]

local instance controlledCommutatorScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance controlledCommutatorScalarStarOrder : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing _
local instance controlledCommutatorSourceOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance controlledCommutatorSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance controlledCommutatorOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance controlledCommutatorOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

omit [NeZero n] in
theorem finiteMatrixEmbedding_operator
    (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (x : FiniteMatrixModel n j) :
    (finiteMatrixEmbedding E x).val = hilbertMatrix (finiteMatrixAmbientEmbedding E x) := by
  change hilbertMatrix
    (coefficientMatrixMap M.toStarSubalgebra.subtype
      (coefficientMatrixMap (matrixUnitsEmbedding E) x)) = _
  apply congrArg hilbertMatrix
  apply CStarMatrix.ext
  intro a b
  exact (matrixUnitsEmbedding_map E M.toStarSubalgebra.subtype (x a b)).symm

omit [NeZero n] in
/-- The estimate is in the operator norm on the actual amplified
Hilbert space, not merely in the quotient. -/
theorem finiteMatrixEmbedding_commutator_le
    (E : Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (v : unitary (FiniteMatrixModel n j)) :
    let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
    ‖T * (finiteMatrixEmbedding E (v : FiniteMatrixModel n j)).val -
      (finiteMatrixEmbedding E (v : FiniteMatrixModel n j)).val * T‖ ≤ 2 * δ := by
  dsimp only
  rw [finiteMatrixEmbedding_operator]
  have he : hilbertMatrix (diagonalAmplification (n := Fin n) h) *
      hilbertMatrix (finiteMatrixAmbientEmbedding E (v : FiniteMatrixModel n j)) -
      hilbertMatrix (finiteMatrixAmbientEmbedding E (v : FiniteMatrixModel n j)) *
      hilbertMatrix (diagonalAmplification (n := Fin n) h) =
      hilbertMatrix (diagonalAmplification h * finiteMatrixAmbientEmbedding E v -
        finiteMatrixAmbientEmbedding E v * diagonalAmplification h) := by
    change _ = (hilbertMatrixHom (H := H)) _
    rw [map_sub, map_mul, map_mul]
    rfl
  rw [he, norm_hilbertMatrix]
  exact finiteMatrix_unitary_commutator_le E h hδ hb v

/-- The actual bounded sequence of finite-matrix representatives. -/
def finiteModelUnitaryLift
    (E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (v : unitary (VaryingBoundedSequence (FiniteMatrixModel n))) :
    unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) :=
  Unitary.map (StarMonoidHom.ofClass
    (varyingSequenceMap (fun j => finiteMatrixEmbedding (n := n) (E j)))) v

theorem finiteModelUnitaryLift_commutator
    (E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)))
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) (j : ℕ) :
    let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
    let s := finiteModelUnitaryLift E v
    ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
      ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ :=
  finiteMatrixEmbedding_commutator_le (E j) h hδ hb
    (Unitary.map (StarMonoidHom.ofClass (varyingSequenceEval (FiniteMatrixModel n) j)) v)

private theorem exists_image_models {E V S : Type*} {P : E → V → Prop} {Q : S → Prop}
    (f : E → V → S) (h : ∀ e v, P e v → Q (f e v))
    (hp : ∃ e, ∃ v, P e v) : ∃ s, Q s := by
  obtain ⟨e, v, hv⟩ := hp
  exact ⟨f e v, h e v hv⟩

variable {C : Type*} [CStarAlgebra C] {σ : FaithfulTracialState C} {ω : Ultrafilter ℕ}

/-- The coordinate norm estimates can be attached to the free model
before choosing a concrete representation for its quotient. -/
theorem exists_freeHaar_commutator_lift_of_models
    (τ : FaithfulTracialState (Algebra M))
    (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖)
    (hmodels : ∃ E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M),
      ∃ v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)),
        FreeHaarMoments σ R.constant.range (finiteModelQuotientUnitary τ R E v)) :
    ∃ s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))),
      FreeHaarMoments σ R.constant.range (Unitary.map (StarMonoidHom.ofClass R.quotient) s) ∧
      ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
        ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
          ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ := by
  apply exists_image_models finiteModelUnitaryLift _ hmodels
  intro E v hv
  exact ⟨hv, finiteModelUnitaryLift_commutator E v h hδ hb⟩

variable [TopologicalSpace.SeparableSpace H]

/-- The free unitary and all its coordinate `2δ` bounds, with exactly the
three published structural hypotheses of the two-stage construction. -/
theorem exists_freeHaar_commutator_lift
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop)
    (h : H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hb : ∀ a ∈ M, ‖h * a - a * h‖ ≤ δ * ‖a‖) :
    ∃ P : TracialUltrapower (matrixVonNeumannTrace (ι := Fin n) M (concreteFactorTrace hM)) ω,
      ∃ s : unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))),
        FreeHaarMoments P.trace P.traceQuotient.constant.range
          (Unitary.map (StarMonoidHom.ofClass P.quotient) s) ∧
        ∀ j, let T := hilbertMatrix (diagonalAmplification (n := Fin n) h)
          ‖T * ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val -
            ((s : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) j).val * T‖ ≤ 2 * δ := by
  apply Exists.imp _ (exists_controlled_freeHaar (n := n) hpub hmat hind hM ω hω)
  intro P hP
  exact exists_freeHaar_commutator_lift_of_models (concreteFactorTrace hM) P.traceQuotient
    h hδ hb hP

end

end KadisonKastler

end OAI
