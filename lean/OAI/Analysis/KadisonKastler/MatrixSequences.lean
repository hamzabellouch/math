import OAI.Analysis.KadisonKastler.MatrixTrace
import OAI.Analysis.KadisonKastler.ClippedCoefficients
import OAI.Analysis.KadisonKastler.UltrapowerExpectation

namespace OAI

/-! # Finite matrices and bounded sequences

Entrywise evaluation identifies bounded sequences of finite matrices
with finite matrices of bounded sequences. Applying a tracial quotient
to the entries gives the normalized matrix trace formula.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {B C ι : Type*} [CStarAlgebra B] [CStarAlgebra C] [Fintype ι] [DecidableEq ι]

local instance matrixSequencesOrder : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixSequencesStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _
local instance matrixSequencesTargetOrder : PartialOrder C := CStarAlgebra.spectralOrder _
local instance matrixSequencesTargetStarOrder : StarOrderedRing C := CStarAlgebra.spectralOrderedRing _
local instance matrixSequencesBoundedOrder : PartialOrder (BoundedSequence B) := CStarAlgebra.spectralOrder _
local instance matrixSequencesBoundedStarOrder : StarOrderedRing (BoundedSequence B) :=
  CStarAlgebra.spectralOrderedRing _

/-- A matrix entry of a bounded sequence is itself a bounded sequence. -/
def matrixEntrySequence (x : BoundedSequence (CStarMatrix ι ι B)) (i j : ι) :
    BoundedSequence B :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun k => x k i j)
    continuous_of_discreteTopology ‖x‖
    (fun k => CStarMatrix.norm_entry_le_norm.trans (x.norm_coe_le_norm k))

@[simp]
theorem matrixEntrySequence_apply (x : BoundedSequence (CStarMatrix ι ι B))
    (i j : ι) (k : ℕ) : matrixEntrySequence x i j k = x k i j := rfl

/-- Assemble finitely many bounded entries into a bounded matrix sequence. -/
def matrixSequenceOfEntries (x : CStarMatrix ι ι (BoundedSequence B)) :
    BoundedSequence (CStarMatrix ι ι B) where
  toFun k := CStarMatrix.ofMatrix fun i j => x i j k
  continuous_toFun := continuous_of_discreteTopology
  map_bounded' := by
    apply Metric.isBounded_range_iff.mp
    change Bornology.IsBounded (Set.range (fun k : ℕ => fun i j : ι => x i j k))
    apply Bornology.forall_isBounded_image_eval_iff.mp
    intro i
    rw [← Set.range_comp]
    apply Bornology.forall_isBounded_image_eval_iff.mp
    intro j
    simpa only [← Set.range_comp, Function.comp_def] using (x i j).isBounded_range

@[simp]
theorem matrixSequenceOfEntries_apply (x : CStarMatrix ι ι (BoundedSequence B))
    (k : ℕ) (i j : ι) : matrixSequenceOfEntries x k i j = x i j k := rfl

omit [DecidableEq ι] in
theorem boundedSequence_sum_apply (x : ι → BoundedSequence B) (k : ℕ) :
    (∑ i, x i) k = ∑ i, x i k :=
  map_sum (boundedSequenceEval k) x Finset.univ

/-- Entrywise transposition of the sequence index and matrix indices. -/
def sequenceMatrixHom : BoundedSequence (CStarMatrix ι ι B) →⋆ₐ[ℂ]
    CStarMatrix ι ι (BoundedSequence B) where
  toFun x := CStarMatrix.ofMatrix fun i j => matrixEntrySequence x i j
  map_one' := by
    ext i j k
    change (1 : CStarMatrix ι ι B) i j = (1 : CStarMatrix ι ι (BoundedSequence B)) i j k
    rw [CStarMatrix.one_apply, CStarMatrix.one_apply]
    split_ifs <;> rfl
  map_mul' x y := by
    ext i j k
    change (x k * y k) i j =
      (∑ l, matrixEntrySequence x i l * matrixEntrySequence y l j) k
    rw [boundedSequence_sum_apply]
    simp only [BoundedContinuousFunction.mul_apply, matrixEntrySequence_apply, CStarMatrix.mul_apply]
  map_zero' := by
    ext i j k
    rfl
  map_add' x y := by
    ext i j k
    rfl
  commutes' z := by
    ext i j k
    change (algebraMap ℂ (CStarMatrix ι ι B) z) i j =
      (algebraMap ℂ (CStarMatrix ι ι (BoundedSequence B)) z) i j k
    rw [CStarMatrix.algebraMap_apply, CStarMatrix.algebraMap_apply]
    split_ifs <;> rfl
  map_star' x := by
    ext i j k
    rfl

@[simp]
theorem sequenceMatrixHom_apply (x : BoundedSequence (CStarMatrix ι ι B))
    (i j : ι) (k : ℕ) : sequenceMatrixHom x i j k = x k i j := rfl

theorem sequenceMatrixHom_bijective : Function.Bijective (sequenceMatrixHom (ι := ι) (B := B)) := by
  constructor
  · intro x y h
    ext k i j
    exact congrArg (fun z : CStarMatrix ι ι (BoundedSequence B) => z i j k) h
  · intro x
    refine ⟨matrixSequenceOfEntries x, ?_⟩
    ext i j k
    rfl

/-- The actual star-algebra equivalence between the two bounded-sequence constructions. -/
def sequenceMatrixEquiv : BoundedSequence (CStarMatrix ι ι B) ≃⋆ₐ[ℂ]
    CStarMatrix ι ι (BoundedSequence B) :=
  StarAlgEquiv.ofBijective sequenceMatrixHom sequenceMatrixHom_bijective

@[simp]
theorem sequenceMatrixEquiv_apply (x : BoundedSequence (CStarMatrix ι ι B))
    (i j : ι) (k : ℕ) : sequenceMatrixEquiv x i j k = x k i j := rfl

theorem norm_sequenceMatrixEquiv (x : BoundedSequence (CStarMatrix ι ι B)) :
    ‖sequenceMatrixEquiv x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map sequenceMatrixHom sequenceMatrixHom_bijective.1 x

variable [Nonempty ι] {τ : FaithfulTracialState B} {σ : FaithfulTracialState C}
  {ω : Ultrafilter ℕ}

/-- Apply a tracial quotient to each finite matrix entry. -/
def matrixSequenceQuotient (Q : TraceQuotientMap τ σ ω) :
    BoundedSequence (CStarMatrix ι ι B) →⋆ₐ[ℂ] CStarMatrix ι ι C :=
  (coefficientMatrixMap Q.quotient).comp sequenceMatrixHom

omit [Nonempty ι] in
@[simp]
theorem matrixSequenceQuotient_apply (Q : TraceQuotientMap τ σ ω)
    (x : BoundedSequence (CStarMatrix ι ι B)) (i j : ι) :
    matrixSequenceQuotient Q x i j = Q.quotient (matrixEntrySequence x i j) := rfl

omit [Nonempty ι] in
theorem matrixSequenceQuotient_surjective (Q : TraceQuotientMap τ σ ω) :
    Function.Surjective (matrixSequenceQuotient (ι := ι) Q) := by
  classical
  intro x
  choose y hy using fun i j => Q.surjective (x i j)
  refine ⟨matrixSequenceOfEntries (CStarMatrix.ofMatrix y), ?_⟩
  apply CStarMatrix.ext
  intro i j
  change Q.quotient (matrixEntrySequence (matrixSequenceOfEntries (CStarMatrix.ofMatrix y)) i j) = _
  have he : matrixEntrySequence (matrixSequenceOfEntries (CStarMatrix.ofMatrix y)) i j = y i j := by
    ext k
    rfl
  rw [he, hy]

theorem matrixSequenceQuotient_trace_limit (Q : TraceQuotientMap τ σ ω)
    (x : BoundedSequence (CStarMatrix ι ι B)) :
    Tendsto (fun k => (matrixTrace τ).toLinearMap (x k)) (ω : Filter ℕ)
      (𝓝 ((matrixTrace σ).toLinearMap (matrixSequenceQuotient Q x))) := by
  have h := tendsto_finsetSum Finset.univ
    (fun i _ => Q.trace_limit (matrixEntrySequence x i i))
  have hm := (tendsto_const_nhds
    (x := (((Fintype.card ι : ℝ)⁻¹ : ℝ) : ℂ))).mul h
  simpa only [matrixTrace_apply, matrixSequenceQuotient_apply, matrixEntrySequence_apply] using hm

/-- The entrywise quotient is itself a tracial quotient of finite matrix algebras. -/
def TraceQuotientMap.matrix (Q : TraceQuotientMap τ σ ω) :
    TraceQuotientMap (matrixTrace (ι := ι) τ) (matrixTrace (ι := ι) σ) ω where
  quotient := matrixSequenceQuotient Q
  surjective := matrixSequenceQuotient_surjective Q
  trace_limit := matrixSequenceQuotient_trace_limit Q

end

end KadisonKastler

end OAI
