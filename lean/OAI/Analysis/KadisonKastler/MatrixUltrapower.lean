import OAI.Analysis.KadisonKastler.MatrixSequences
import OAI.Analysis.KadisonKastler.VaryingQuotient

namespace OAI

/-! # Entrywise identification of matrix tracial ultrapowers

Two surjective trace quotients of the same bounded-sequence algebra have
identical kernels, by faithfulness of their traces. Applying this to the
entrywise matrix quotient gives the finite-matrix ultrapower identity.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable {τ : FaithfulTracialState A} {σ : FaithfulTracialState B}
  {ρ : FaithfulTracialState C} {ω : Ultrafilter ℕ}

namespace TraceQuotientMap

variable (D : TraceQuotientMap τ σ ω) (E : TraceQuotientMap τ ρ ω)

theorem same_source_trace (x : BoundedSequence A) :
    σ.toLinearMap (D.quotient x) = ρ.toLinearMap (E.quotient x) :=
  tendsto_nhds_unique (D.trace_limit x) (E.trace_limit x)

theorem same_source_kernel (x : BoundedSequence A) (hx : D.quotient x = 0) :
    E.quotient x = 0 := by
  apply ρ.faithful
  rw [← StarHomClass.map_star E.quotient, ← map_mul E.quotient, ← D.same_source_trace E,
    map_mul D.quotient, StarHomClass.map_star D.quotient, hx, star_zero, zero_mul, map_zero]

/-- The canonical comparison between faithful trace quotients of the
same bounded-sequence algebra. -/
def comparison : B →⋆ₐ[ℂ] C :=
  starAlgHomDescend D.quotient D.surjective E.quotient (D.same_source_kernel E)

@[simp]
theorem comparison_quotient (x : BoundedSequence A) :
    D.comparison E (D.quotient x) = E.quotient x :=
  starAlgHomDescend_apply_map _ _ _ _ x

theorem comparison_trace (x : B) :
    ρ.toLinearMap (D.comparison E x) = σ.toLinearMap x := by
  obtain ⟨y, rfl⟩ := D.surjective x
  rw [comparison_quotient]
  exact (D.same_source_trace E y).symm

theorem comparison_bijective : Function.Bijective (D.comparison E) := by
  refine ⟨injective_of_trace_preserving σ ρ _ (D.comparison_trace E), ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := E.surjective y
  exact ⟨D.quotient x, D.comparison_quotient E x⟩

/-- Uniqueness, up to a trace-preserving star equivalence, of faithful
tracial quotients with the same coordinate trace formula. -/
def comparisonEquiv : B ≃⋆ₐ[ℂ] C :=
  StarAlgEquiv.ofBijective (D.comparison E) (D.comparison_bijective E)

@[simp]
theorem comparisonEquiv_quotient (x : BoundedSequence A) :
    D.comparisonEquiv E (D.quotient x) = E.quotient x :=
  D.comparison_quotient E x

theorem comparisonEquiv_trace (x : B) :
    ρ.toLinearMap (D.comparisonEquiv E x) = σ.toLinearMap x :=
  D.comparison_trace E x

end TraceQuotientMap

local instance matrixUltrapowerSourceOrder : PartialOrder A := CStarAlgebra.spectralOrder _
local instance matrixUltrapowerSourceStarOrder : StarOrderedRing A := CStarAlgebra.spectralOrderedRing _
local instance matrixUltrapowerTargetOrder : PartialOrder B := CStarAlgebra.spectralOrder _
local instance matrixUltrapowerTargetStarOrder : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The represented quotient of matrices is the matrix algebra over
the scalar represented quotient, with its normalized matrix trace. -/
def matrixUltrapowerEquiv (Q : TraceQuotientMap τ σ ω)
    (P : TraceQuotientMap (matrixTrace (ι := ι) τ) ρ ω) :
    C ≃⋆ₐ[ℂ] CStarMatrix ι ι B :=
  P.comparisonEquiv Q.matrix

@[simp]
theorem matrixUltrapowerEquiv_quotient (Q : TraceQuotientMap τ σ ω)
    (P : TraceQuotientMap (matrixTrace (ι := ι) τ) ρ ω)
    (x : BoundedSequence (CStarMatrix ι ι A)) (i j : ι) :
    matrixUltrapowerEquiv Q P (P.quotient x) i j =
      Q.quotient (matrixEntrySequence x i j) := by
  change (P.comparisonEquiv Q.matrix (P.quotient x)) i j = _
  rw [P.comparisonEquiv_quotient]
  rfl

theorem matrixUltrapowerEquiv_trace (Q : TraceQuotientMap τ σ ω)
    (P : TraceQuotientMap (matrixTrace (ι := ι) τ) ρ ω) (x : C) :
    (matrixTrace σ).toLinearMap (matrixUltrapowerEquiv Q P x) = ρ.toLinearMap x :=
  P.comparisonEquiv_trace Q.matrix x

/-- Scalar matrix entries descend to the same constant entries under
the matrix-ultrapower identification. -/
theorem matrixUltrapowerEquiv_constant (Q : TraceQuotientMap τ σ ω)
    (P : TraceQuotientMap (matrixTrace (ι := ι) τ) ρ ω)
    (x : CStarMatrix ι ι A) (i j : ι) :
    matrixUltrapowerEquiv Q P (P.quotient (boundedSequenceConst x)) i j =
      Q.quotient (boundedSequenceConst (x i j)) := by
  rw [matrixUltrapowerEquiv_quotient]
  congr 1

end

end KadisonKastler

end OAI
