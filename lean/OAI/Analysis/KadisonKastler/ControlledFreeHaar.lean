import OAI.Analysis.KadisonKastler.MatrixQuotientLifts
import OAI.Analysis.KadisonKastler.FiniteBaseConjugation
import OAI.Analysis.KadisonKastler.QuotientSeparability
import OAI.Analysis.KadisonKastler.MatrixUnitsExistence
import OAI.Analysis.KadisonKastler.NormalizedUltrapower

namespace OAI

/-! # Free Haar unitaries with finite-matrix representatives

The two independence applications are combined with the actual quotient
embedding and diagonal unitary lifts. The output keeps the finite matrix
units in each coordinate, so the scalar derivation controls every lift.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
variable {n : ℕ} [NeZero n] {ω : Ultrafilter ℕ}
variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
variable {σB : FaithfulTracialState B} {σ : FaithfulTracialState C}

local instance controlledScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance controlledScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _
local instance controlledSourceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance controlledSourceStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

variable (τ : FaithfulTracialState (Algebra M))
variable (R : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)

private def controlledScalarBase : StarSubalgebra ℂ C :=
  (R.constant.comp (concreteScalarMatrixHom (M := M) (n := n))).range

private instance controlledScalarBaseFinite : FiniteDimensional ℂ (controlledScalarBase τ R) := by
  let : FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.of_surjective CStarMatrix.ofMatrixₗ.toLinearMap
      CStarMatrix.ofMatrixₗ.surjective
  exact FiniteDimensional.of_surjective
    (R.constant.comp (concreteScalarMatrixHom (M := M) (n := n))).toAlgHom.rangeRestrict.toLinearMap
    (R.constant.comp (concreteScalarMatrixHom (M := M) (n := n))).toAlgHom.rangeRestrict_surjective

/-- The represented unitary associated with a finite-model lift. -/
def finiteModelQuotientUnitary
    (E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (v : unitary (VaryingBoundedSequence (FiniteMatrixModel n))) : unitary C :=
  Unitary.map (StarMonoidHom.ofClass R.quotient)
    (Unitary.map (StarMonoidHom.ofClass
      (varyingSequenceMap (fun j => finiteMatrixEmbedding (n := n) (E j)))) v)

omit [TopologicalSpace.SeparableSpace H] in
/-- Diagonal conjugation of the matrix units gives the exact conjugation
of the represented model unitary. -/
theorem finiteModelQuotientUnitary_conjugate
    (E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)))
    (z : unitary (BoundedSequence (Algebra M))) (w : unitary C)
    (hz : R.quotient (concreteDiagonalSequence (n := n) (z : BoundedSequence _)) = (w : C)) :
    finiteModelQuotientUnitary τ R (conjugatedMatrixUnitsSequence E z) v =
      w * finiteModelQuotientUnitary τ R E v * star w := by
  apply Subtype.ext
  change R.quotient (varyingSequenceMap
    (fun j => finiteMatrixEmbedding (n := n) (conjugatedMatrixUnitsSequence E z j))
      (v : VaryingBoundedSequence _)) = _
  have he := finiteMatrixSequence_conjugatedMatrixUnits_quotient R.quotient E z
    (v : VaryingBoundedSequence _)
  have hz' := congrArg (fun a : C => a *
    R.quotient (varyingSequenceMap
      (fun j => finiteMatrixEmbedding (n := n) (E j))
      (v : VaryingBoundedSequence _)) * star a) hz
  exact he.trans hz'

/-- The second independence application and the scalar commutant lift,
with a fixed first model. -/
theorem exists_freeHaar_conjugated_model
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (hτ : FiniteVectorTrace τ)
    (Qbase : TraceQuotientMap τ σB ω) (hindR : FiniteBaseIndependence σ)
    (E₀ : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M))
    (v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)))
    (hv : FreeHaarMoments σ (controlledScalarBase τ R) (finiteModelQuotientUnitary τ R E₀ v)) :
    ∃ E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M),
      FreeHaarMoments σ R.constant.range (finiteModelQuotientUnitary τ R E v) := by
  have hDA : controlledScalarBase τ R ≤ R.constant.range := by
    rintro x ⟨a, rfl⟩
    exact ⟨concreteScalarMatrixHom (M := M) a, rfl⟩
  have hsep : TraceSeparable σ (R.constant.range : Set C) :=
    R.constant_traceSeparable (matrixVonNeumannTrace_finiteVector M τ hτ)
  obtain ⟨w, hw, hfree⟩ := hindR.exists_conjugated_freeHaar
    (controlledScalarBase τ R) R.constant.range hDA hsep
    (finiteModelQuotientUnitary τ R E₀ v) hv
  have hw' : ∀ a : CStarMatrix (Fin n) (Fin n) ℂ,
      R.constant (concreteScalarMatrixHom (M := M) a) * (w : C) =
        (w : C) * R.constant (concreteScalarMatrixHom (M := M) a) := by
    intro a
    exact (hw _ ⟨a, rfl⟩).eq.symm
  obtain ⟨z, hz⟩ := exists_concrete_scalar_commutant_lift hM Qbase R w hw'
  refine ⟨conjugatedMatrixUnitsSequence E₀ z, ?_⟩
  rwa [finiteModelQuotientUnitary_conjugate τ R E₀ v z w hz]

/-- Eliminate the first lift in an abstract existential proposition, so
no concrete finite-matrix representation is expanded by the eliminator. -/
private theorem swap_exists_models {V : Type*} {E : Type*} {P : V → Prop}
    {F : E → V → Prop} (hv : ∃ v, P v)
    (hf : ∀ v, P v → ∃ e, F e v) : ∃ e, ∃ v, F e v := by
  obtain ⟨v, hv⟩ := hv
  obtain ⟨e, he⟩ := hf v hv
  exact ⟨e, v, he⟩

/-- The two-stage construction, with the independence inputs specialized
to the two quotient algebras actually used. -/
theorem exists_controlled_freeHaar_from_model
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (hτ : FiniteVectorTrace τ)
    (Qbase : TraceQuotientMap τ σB ω) (Q : FiniteMatrixUltraproduct n ω)
    (hindQ : FiniteBaseIndependence (concreteFactorTrace Q.factor))
    (hindR : FiniteBaseIndependence σ) :
    ∃ E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M),
      ∃ v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)),
        FreeHaarMoments σ R.constant.range
          (finiteModelQuotientUnitary τ R E v) := by
  exact swap_exists_models
    (Q.exists_embedded_freeHaar_lift τ R (factorMatrixUnits hM) hindQ)
    (fun v hv => exists_freeHaar_conjugated_model τ R hM hτ Qbase hindR
      (factorMatrixUnits hM) v hv)

/-- The complete finite-matrix free lift, conditional only on the three
specified published ultraproduct/independence inputs. All matrix units,
embeddings, separability, scalar freeness, and unitary lifts are constructed. -/
theorem exists_controlled_freeHaar
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.atTop) :
    ∃ P : TracialUltrapower (matrixVonNeumannTrace (ι := Fin n) M (concreteFactorTrace hM)) ω,
      ∃ E : ∀ j, Generator.MatrixUnitSystem (Fin (j + 1)) (Algebra M),
        ∃ v : unitary (VaryingBoundedSequence (FiniteMatrixModel n)),
          FreeHaarMoments P.trace P.traceQuotient.constant.range
            (finiteModelQuotientUnitary (concreteFactorTrace hM) P.traceQuotient E v) := by
  let τM := concreteFactorTrace hM
  let P₀ := matrixVonNeumann (ι := Fin n) M
  have hP₀ : Generator.IsII1Factor P₀.toStarSubalgebra :=
    matrixVonNeumann_isII1Factor M hM τM
  let Qbase := Classical.choice (hpub H M hM ω hω)
  let P := Classical.choice (publishedTracialUltrapower_for_trace hpub hP₀
    (matrixVonNeumannTrace (ι := Fin n) M τM) ω hω)
  let Q := Classical.choice (hmat n ω hω)
  have hindP : FiniteBaseIndependence P.trace :=
    hind.1 (Generator.FiniteHilbert (Fin n) H) P₀ hP₀
      (matrixVonNeumannTrace (ι := Fin n) M τM) ω hω P
  have hresult := exists_controlled_freeHaar_from_model τM P.traceQuotient hM
    (concreteFactorTrace_finiteVector hM) Qbase.traceQuotient Q (hind.2 n ω hω Q) hindP
  exact ⟨P, hresult⟩

end

end KadisonKastler

end OAI
