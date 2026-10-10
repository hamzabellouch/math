import OAI.Analysis.KadisonKastler.FiniteTraceMatrix

namespace OAI

/-! # The common remainder of rounded spectral pieces -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

variable (Q : CornerPartition (identityProjection M))
  (q : Fin Q.size → AlgebraProjection M) (hq : ∀ i, q i ≤ Q.piece i)

/-- All discarded pieces are supported in the complement of the rounded pieces. -/
def partitionRemainder : AlgebraProjection M :=
  ⟨1 - ∑ i, (q i).val,
    (orthogonal_family_sum_projection q (fun i j hij =>
      orthogonal_subprojections (Q.orthogonal i j hij) (hq i) (hq j))).one_sub⟩

def partitionResidual (i : Fin Q.size) : AlgebraProjection M :=
  ⟨(Q.piece i).val - (q i).val,
    (q i).property.sub_of_mul_eq_right (Q.piece i).property (hq i)⟩

theorem partitionResidual_le_piece (i : Fin Q.size) :
    partitionResidual Q q hq i ≤ Q.piece i := by
  change (Q.piece i).val * ((Q.piece i).val - (q i).val) = (Q.piece i).val - (q i).val
  rw [mul_sub, (Q.piece i).property.isIdempotentElem.eq, hq i]

theorem partitionResidual_total :
    (∑ i, (partitionResidual Q q hq i).val) = (partitionRemainder Q q hq).val := by
  change (∑ i, ((Q.piece i).val - (q i).val)) = 1 - ∑ i, (q i).val
  rw [Finset.sum_sub_distrib, Q.total]
  rfl

theorem partitionResidual_le_remainder (i : Fin Q.size) :
    partitionResidual Q q hq i ≤ partitionRemainder Q q hq := by
  classical
  change (partitionRemainder Q q hq).val * (partitionResidual Q q hq i).val = _
  rw [← partitionResidual_total, Finset.sum_mul, Finset.sum_eq_single i]
  · exact (partitionResidual Q q hq i).property.isIdempotentElem.eq
  · intro j _ hji
    exact orthogonal_subprojections (Q.orthogonal j i hji)
      (partitionResidual_le_piece Q q hq j) (partitionResidual_le_piece Q q hq i)
  · simp

theorem partitionRemainder_mem (B : StarSubalgebra ℂ (Algebra M))
    (hmem : ∀ i, (q i).val ∈ B) : (partitionRemainder Q q hq).val ∈ B :=
  B.sub_mem B.one_mem (B.sum_mem (fun i _ => hmem i))

/-- The trace of the common remainder is the sum of the discarded traces. -/
theorem partitionRemainder_trace (τ : TracialRepresentation M) :
    (τ.trace (partitionRemainder Q q hq).val).re =
      ∑ i, τ.norm₂ ((Q.piece i).val - (q i).val) ^ 2 := by
  rw [← partitionResidual_total]
  change ((coordinateTraceLinear τ) (∑ i, (partitionResidual Q q hq i).val)).re = _
  rw [map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact projection_trace_sq τ _ (partitionResidual Q q hq i).property

theorem partitionRemainder_trace_le (τ : TracialRepresentation M) (δ : ℝ)
    (hδ : ∀ i, τ.norm₂ ((Q.piece i).val - (q i).val) ^ 2 ≤ δ) :
    (τ.trace (partitionRemainder Q q hq).val).re ≤ Q.size * δ := by
  rw [partitionRemainder_trace]
  simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hδ i)

end

end KadisonKastler

end OAI
