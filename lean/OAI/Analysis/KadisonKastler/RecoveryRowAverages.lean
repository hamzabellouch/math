import OAI.Analysis.KadisonKastler.RecoveryRows
import OAI.Analysis.KadisonKastler.ConcreteRecoveryWeakLimit

namespace OAI

/-! # The actual finite recovery-row average

The coordinate row sandwich identifies the random row product with the
sequence-level recovery observable. The constructed trace expectation and
scalar recovery bound therefore give its weak scalar limit.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators

noncomputable section

/-- Repeating a finite average along an independent nonempty finite index
leaves it unchanged. -/
theorem finiteAverage_repeat_snd {I A V : Type*} [Fintype I] [Nonempty I] [Fintype A]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (f : A → V) :
    finiteAverage (fun ia : I × A => f ia.2) = finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  simp [Fintype.card_prod, mul_inv_rev, Fintype.card_ne_zero]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n N : ℕ} {I : Type*} [Fintype I]

/-- Forward polynomial rows for the unitary at a sequence coordinate. -/
def recoverySequenceForwardRows (M : VonNeumannAlgebra H) (N : ℕ)
    (v : I → unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (j : ℕ) (ia : I × Fin n) : Generator.FiniteHilbert (Fin n) H →L[ℂ] H :=
  recoveryForwardRow M N ia.2 (sequenceUnitaryEval (v ia.1) j)

/-- Backward polynomial rows at the same sequence coordinate. -/
def recoverySequenceBackwardRows (M : VonNeumannAlgebra H) (N : ℕ)
    (v : I → unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (j : ℕ) (ia : I × Fin n) : Generator.FiniteHilbert (Fin n) H →L[ℂ] H :=
  recoveryBackwardRow M N ia.2 (sequenceUnitaryEval (v ia.1) j)

/-- The corner entries are actual elements of the original algebra. -/
def recoverySequenceContractions (M : VonNeumannAlgebra H) (N : ℕ)
    (v : I → unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (j : ℕ) (ia : I × Fin n) : Algebra M :=
  recoveryCornerContraction M ia.2 (unitaryHaarPolynomial N (sequenceUnitaryEval (v ia.1) j))

omit [Fintype I] in
theorem recoverySequenceContractions_norm_le (M : VonNeumannAlgebra H) (hn : 0 < n)
    (N : ℕ)
    (v : I → unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (j : ℕ) (ia : I × Fin n) : ‖recoverySequenceContractions M N v j ia‖ ≤ 1 :=
  recoveryCornerContraction_norm_le M hn ia.2 _

/-- The row product is the actual finite average of the recovery observable,
not merely a scalar trace identity. -/
theorem recoveryRows_average_eq (M : VonNeumannAlgebra H) (hn : 0 < n) (N : ℕ)
    (v : I → unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (j : ℕ) :
    averageRowProduct (recoverySequenceForwardRows M N v j)
      (recoverySequenceBackwardRows M N v j)
      (fun ia => (recoverySequenceContractions M N v j ia).val) =
    ((finiteAverage (fun ia : I × Fin n => recoveryObservable n N
      (boundedSequenceConst (matrixDiagonalProjection M ia.2)) (v ia.1))) j).val := by
  rw [recoveryAverage_sequence_apply hn]
  change _ = (matrixVonNeumann (ι := Fin n) M).toStarSubalgebra.subtype
    (finiteAverage (fun ia : I × Fin n => recoveryObservable n N
      (matrixDiagonalProjection M ia.2) (sequenceUnitaryEval (v ia.1) j)))
  rw [map_finiteAverage]
  unfold averageRowProduct finiteAverage
  congr 1
  apply Finset.sum_congr rfl
  intro ia _
  exact recoveryRows_product M hn N ia.2 (sequenceUnitaryEval (v ia.1) j)

variable [Nonempty I]

/-- The repeated outer coordinate partition has normalized scalar average. -/
theorem finiteAverage_repeated_matrixDiagonalProjection (M : VonNeumannAlgebra H) :
    finiteAverage (fun ia : I × Fin n => matrixDiagonalProjection M ia.2) =
      (((n : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Algebra (matrixVonNeumann (ι := Fin n) M)) := by
  rw [finiteAverage_repeat_snd]
  simpa only [Fintype.card_fin] using finiteAverage_matrixDiagonalProjection (ι := Fin n) M

variable [NeZero n]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {P : VonNeumannAlgebra K} {τ : FaithfulTracialState (Algebra M)}
variable {σ : FaithfulTracialState (Algebra P)} {ω : Ultrafilter ℕ}

/-- The actual recovery rows have a scalar weak limit with real part at least
one half, using only the free quotient unitaries and the finite trace formulas. -/
theorem TraceQuotientMap.exists_recoveryRows_weak_scalar
    (D : TraceQuotientMap (matrixVonNeumannTrace (ι := Fin n) M τ) σ ω)
    (hτ : FiniteVectorTrace τ) (hσ : FiniteVectorTrace σ)
    (v : I → unitary (BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))))
    (u : I → unitary (Algebra P))
    (hu : ∀ i, D.quotient (v i : BoundedSequence (Algebra (matrixVonNeumann (ι := Fin n) M))) =
      (u i : Algebra P))
    (hfree : ∀ i, FreeHaarMoments σ D.constant.range (u i))
    (hn : 2 ≤ n) (hsize : 100 * (n : ℝ) * (100 * Real.pi) ^ 3 ≤ N) :
    ∃ c : ℂ, 1 / 2 ≤ c.re ∧
      WeakOperatorConverges (ω : Filter ℕ)
        (fun j => averageRowProduct (recoverySequenceForwardRows M N v j)
          (recoverySequenceBackwardRows M N v j)
          (fun ia => (recoverySequenceContractions M N v j ia).val))
        (c • ContinuousLinearMap.id ℂ (Generator.FiniteHilbert (Fin n) H)) := by
  have hn0 : 0 < n := by omega
  obtain ⟨c, hc, hlim⟩ := D.exists_recovery_weak_scalar
    (matrixVonNeumannTrace_finiteVector M τ hτ) hσ
    (fun ia : I × Fin n => matrixDiagonalProjection M ia.2)
    (fun ia => v ia.1) (fun ia => u ia.1) (fun ia => hu ia.1)
    (fun ia => matrixDiagonalProjection_isStarProjection M ia.2)
    (fun ia => hfree ia.1) hn
    (fun ia => by simpa only [Fintype.card_fin] using
      matrixVonNeumannTrace_diagonal (ι := Fin n) M τ ia.2)
    (finiteAverage_repeated_matrixDiagonalProjection (I := I) M) hsize
  refine ⟨c, hc, ?_⟩
  intro ξ η
  simpa only [recoveryRows_average_eq M hn0 N v] using hlim ξ η

end

end KadisonKastler

end OAI
