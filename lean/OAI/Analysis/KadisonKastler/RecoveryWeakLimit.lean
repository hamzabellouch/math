import OAI.Analysis.KadisonKastler.UltrapowerExpectation
import OAI.Analysis.KadisonKastler.RecoveryExpectation
import OAI.Analysis.KadisonKastler.RowPairing

namespace OAI

/-! # The recovery average converges weakly to its scalar expectation

The average is formed from actual bounded coordinate sequences. Its
quotient is computed by continuous functional calculus; the constructed
expectation and free-word trace identities then identify its weak limit.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

/-- Naturality of the whole observable, including its continuous cutoff. -/
theorem map_recoveryObservable (π : B →⋆ₐ[ℂ] C) {n : ℕ} (hn : 0 < n)
    (N : ℕ) (p : B) (u : unitary B) (v : unitary C)
    (huv : π (u : B) = (v : C)) :
    π (recoveryObservable n N p u) = recoveryObservable n N (π p) v := by
  simp only [recoveryObservable, map_smul, map_mul, map_recoveryContraction π hn,
    map_unitaryHaarPolynomial π N u v huv]

/-- Scalar identities are preserved without any choice of representation. -/
theorem map_complex_smul_one (π : B →⋆ₐ[ℂ] C) (c : ℂ) :
    π (c • (1 : B)) = c • (1 : C) := by
  rw [map_smul, map_one]

/-- A star homomorphism commutes with the finite uniform average. -/
theorem map_finiteAverage {ι : Type*} [Fintype ι]
    (π : B →⋆ₐ[ℂ] C) (x : ι → B) :
    π (finiteAverage x) = finiteAverage (fun i => π (x i)) := by
  simp only [finiteAverage, map_smul, map_sum]

/-- The unitary represented by one coordinate of a bounded unitary sequence. -/
def sequenceUnitaryEval (v : unitary (BoundedSequence B)) (j : ℕ) : unitary B :=
  Unitary.map (StarMonoidHom.ofClass (boundedSequenceEval (B := B) j)) v

@[simp]
theorem sequenceUnitaryEval_coe (v : unitary (BoundedSequence B)) (j : ℕ) :
    (sequenceUnitaryEval v j : B) = (v : BoundedSequence B) j := rfl

/-- The sequence-level continuous cutoff evaluates to the actual
coordinate contraction. -/
theorem recoveryObservable_sequence_apply {n : ℕ} (hn : 0 < n) (N : ℕ)
    (p : B) (v : unitary (BoundedSequence B)) (j : ℕ) :
    recoveryObservable n N (boundedSequenceConst p) v j =
      recoveryObservable n N p (sequenceUnitaryEval v j) :=
  map_recoveryObservable (boundedSequenceEval j) hn N _ _ _ rfl

/-- Evaluation also respects the actual finite averaging operation. -/
theorem recoveryAverage_sequence_apply {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 0 < n) (N : ℕ) (p : ι → B)
    (v : ι → unitary (BoundedSequence B)) (j : ℕ) :
    (finiteAverage (fun i => recoveryObservable n N (boundedSequenceConst (p i)) (v i))) j =
      finiteAverage (fun i => recoveryObservable n N (p i) (sequenceUnitaryEval (v i) j)) := by
  have h := map_finiteAverage (boundedSequenceEval j)
    (fun i => recoveryObservable n N (boundedSequenceConst (p i)) (v i))
  simpa only [boundedSequenceEval_apply, recoveryObservable_sequence_apply hn] using h

namespace TraceQuotientMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable {σ : FaithfulTracialState C} {ω : Ultrafilter ℕ}
variable (D : TraceQuotientMap τ σ ω) (hτ : FiniteVectorTrace τ)

include hτ

/-- Scalar expectation determines the weak operator limit in the given
representation, rather than only in the tracial representation. -/
theorem weak_scalar_limit (s : BoundedSequence (Algebra M)) (c : ℂ)
    (hs : D.baseExpectationCLM hτ (D.quotient s) = c • (1 : C)) :
    WeakOperatorConverges (ω : Filter ℕ)
      (fun j => (s j : H →L[ℂ] H)) (c • ContinuousLinearMap.id ℂ H) := by
  have he : D.expectation hτ (D.quotient s) = c • (1 : Algebra M) := by
    apply D.constant_injective
    change D.baseExpectationCLM hτ (D.quotient s) = D.constant (c • (1 : Algebra M))
    simpa only [map_complex_smul_one] using hs
  intro ξ η
  have ht := (D.weak_limit_expectation hτ s ξ η).star
  have hstar (a b : H) : star (inner ℂ a b) = inner ℂ b a := inner_conj_symm _ _
  simp only [hstar] at ht
  have hop : (D.expectation hτ (D.quotient s) : H →L[ℂ] H) =
      c • ContinuousLinearMap.id ℂ H := by rw [he]; rfl
  rw [hop] at ht
  exact ht

/-- The weak scalar limit of the actual sequence-level recovery average. -/
theorem recovery_average_weak_limit
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → Algebra M) (v : ι → unitary (BoundedSequence (Algebra M)))
    (u : ι → unitary C)
    (hu : ∀ i, D.quotient (v i : BoundedSequence (Algebra M)) = (u i : C))
    (hp : ∀ i, IsStarProjection (p i))
    (hfree : ∀ i, FreeHaarMoments σ D.constant.range (u i))
    {t : ℂ} (hptrace : ∀ i, τ.toLinearMap (p i) = t)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hpavg : finiteAverage p = t • (1 : Algebra M))
    {n : ℕ} (hn : 0 < n) (N : ℕ) (i₀ : ι) :
    WeakOperatorConverges (ω : Filter ℕ)
      (fun j => ((finiteAverage (fun i => recoveryObservable n N
        (boundedSequenceConst (p i)) (v i))) j : H →L[ℂ] H))
      (σ.toLinearMap (recoveryObservable n N (D.constant (p i₀)) (u i₀)) •
        ContinuousLinearMap.id ℂ H) := by
  apply D.weak_scalar_limit hτ
  have hq : ∀ i, D.quotient (recoveryObservable n N
      (boundedSequenceConst (p i)) (v i)) =
      recoveryObservable n N (D.constant (p i)) (u i) := by
    intro i
    exact map_recoveryObservable D.quotient hn N _ _ _ (hu i)
  rw [map_finiteAverage]
  simp only [hq]
  apply expectation_finiteAverage_recoveryObservable σ D.constant.range
    (D.baseExpectationCLM hτ)
  · exact D.baseExpectation_mem hτ
  · intro b hb x
    exact D.baseExpectation_pairing hτ x b hb
  · intro i
    exact (hp i).map D.constant
  · intro i
    exact ⟨p i, rfl⟩
  · exact hfree
  · intro i
    rw [D.trace_constant, hptrace i]
  · exact ht0
  · exact ht1
  · calc
      finiteAverage (fun i => D.constant (p i)) = D.constant (finiteAverage p) :=
        (map_finiteAverage D.constant p).symm
      _ = t • (1 : C) := by
        rw [hpavg, map_complex_smul_one]
  · exact hn

end TraceQuotientMap

end

end KadisonKastler

end OAI
