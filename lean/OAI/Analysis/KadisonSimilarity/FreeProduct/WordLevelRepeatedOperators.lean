import OAI.Analysis.KadisonSimilarity.FreeProduct.OrthogonalWordLevels

namespace OAI

/-!
# Canonical multiplicity operators on repeated-letter words

Compression to one normalized repeated word defines the degree-wise operator.
The invariant-intertwiner classification proves that this same operator acts
on every repeated-letter word. Adjoint compatibility follows from the concrete
compression formula.
-/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)

/-- The canonical degree-wise operator is a concrete compression to one unit
repeated word. Its independence of that word is proved below. -/
def wordLevelRepeatedOperator (Y : H →L[ℂ] H) (n : ℕ) : G n →L[ℂ] G n :=
  multiplicityCompression (U.block Y n n)
    (endpointWord T.traceVector (fun _ : Fin n => T.realOrthonormal 0))

omit [∀ s, Nonempty (A s)] in
theorem norm_wordLevelRepeatedOperator_le (Y : H →L[ℂ] H) (n : ℕ) :
    ‖wordLevelRepeatedOperator T U Y n‖ ≤ ‖Y‖ := by
  apply le_trans (norm_multiplicityCompression_le (U.block Y n n) _ ?_) (U.norm_block_le Y n n)
  exact norm_endpointWord_constant T.traceVector (T.realOrthonormal 0)
    T.norm_traceVector (T.realOrthonormal_orthonormal.norm_eq_one 0)

omit [∀ s, Nonempty (A s)] in
/-- The canonical compression commutes with taking the adjoint, for every
bounded ambient operator, before any invariant-theory hypotheses are imposed. -/
theorem wordLevelRepeatedOperator_adjoint (Y : H →L[ℂ] H) (n : ℕ) :
    wordLevelRepeatedOperator T U Y.adjoint n = (wordLevelRepeatedOperator T U Y n).adjoint := by
  simp only [wordLevelRepeatedOperator, multiplicityCompression,
    OrthogonalWordLevels.block, OrthogonalWordLevels.coordinate,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc]

variable (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)

/-- On a diagonal block the cross-multiplicity word covariance is exactly the
existing same-multiplicity covariance. -/
def WordLevelMatrixActions.diagonalCovariance (s n : ℕ) :
    MultiplicityMatrixCovariance (T.stage s) T.conjugation T.traceVector (U.block Y n n) where
  sourceAction := C.wordAction s n
  testAction := C.wordAction s n
  intertwine u := U.block_intertwines Y (C.unitaryAction s u) _ _ (hunitary s u)
    (C.unitary_inclusion s u n) (C.unitary_adjoint_inclusion s u n)
  source_covariance u v := C.source_word s n u (fun i => v (some (.inl i)))
  test_covariance u v := C.test_word s n u (v none) (fun i => v (some (.inr i)))

include hleft hunitary in
/-- The degree-wise compression acts on every repeated-letter vector in its
full diagonal block. -/
theorem wordLevelRepeatedOperator_block_apply (n : ℕ)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin n ⊕ Fin n)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin n ⊕ Fin n))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin n ⊕ Fin n) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (a : G n) (d : E) (r : F) :
    U.block Y n n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))) =
      hilbertTensorInsert (wordLevelRepeatedOperator T U Y n a)
        (endpointWord d (fun _ : Fin n => r)) := by
  obtain ⟨B, _, hB⟩ := exists_multiplicity_repeated_operator_of_schurWeyl T (U.block Y n n)
    (fun s c => U.block_intertwines Y (C.leftAction s c) _ _ (hleft s c)
      (C.left_inclusion s c n) (C.left_adjoint_inclusion s c n))
    (fun s => WordLevelMatrixActions.diagonalCovariance T U C Y hunitary s n)
    spanning hcontraction labels hlabels
  have heq : wordLevelRepeatedOperator T U Y n = B :=
    multiplicityCompression_eq_of_repeated_action (U.block Y n n) B hB
      T.traceVector T.norm_traceVector (T.realOrthonormal 0)
      (T.realOrthonormal_orthonormal.norm_eq_one 0)
  rw [heq]
  exact hB a d r

include hleft hunitary in
/-- Combining the two degree cases gives the actual ambient repeated-word
action, with its canonical bounded multiplicity operator. -/
theorem wordLevelRepeatedOperator_apply
    (spanning : ∀ k l s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ k l s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ k l s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ k l s, Function.Injective (labels k l s))
    (n : ℕ) (a : G n) (d : E) (r : F) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (wordLevelRepeatedOperator T U Y n a)
        (endpointWord d (fun _ : Fin n => r))) := by
  have hp := word_levels_preserved_of_schurWeyl T U C Y hleft hunitary
    spanning hcontraction labels hlabels n
  have h := congrArg (fun f : MultiplicityWordSpace G E F n →L[ℂ] H =>
    f (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) hp
  change Y (U.inclusion n _) = U.inclusion n (U.block Y n n _) at h
  rw [h]
  congr 1
  exact wordLevelRepeatedOperator_block_apply T U C Y hleft hunitary n
    (spanning n n) (hcontraction n n) (labels n n) (hlabels n n) a d r

include hleft hunitary in
/-- Any normalized repeated tail gives the same compression, so the operator
is independent of the reference unit letter used in its definition. -/
theorem wordLevelRepeatedOperator_reference_independent (n : ℕ)
    (spanning : ∀ s, SchurWeylMultilinearSpanning (Option (Fin n ⊕ Fin n)) (A s))
    (hcontraction : ∀ s (π : Equiv.Perm (Option (Fin n ⊕ Fin n))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ s, Option (Fin n ⊕ Fin n) → A s)
    (hlabels : ∀ s, Function.Injective (labels s)) (r : F) (hr : ‖r‖ = 1) :
    multiplicityCompression (U.block Y n n)
      (endpointWord T.traceVector (fun _ : Fin n => r)) = wordLevelRepeatedOperator T U Y n :=
  multiplicityCompression_eq_of_repeated_action (U.block Y n n)
    (wordLevelRepeatedOperator T U Y n)
    (wordLevelRepeatedOperator_block_apply T U C Y hleft hunitary n
      spanning hcontraction labels hlabels) T.traceVector T.norm_traceVector r hr

/-- Commutation with an adjoint yields the required commutation for the
adjoint of the ambient operator. -/
theorem adjoint_commutes_of_adjoint_commutes (Y Q : H →L[ℂ] H)
    (h : Y.comp Q.adjoint = Q.adjoint.comp Y) : Y.adjoint.comp Q = Q.comp Y.adjoint := by
  have h' := congrArg ContinuousLinearMap.adjoint h
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h'.symm

include hleft hunitary in
/-- Star closure of the actual global action families supplies the adjoint
repeated-word action, with precisely the adjoint canonical multiplicity map. -/
theorem wordLevelRepeatedOperator_adjoint_apply
    (hleftStar : ∀ s a, (C.leftAction s a).adjoint = C.leftAction s (star a))
    (hunitaryStar : ∀ s u, (C.unitaryAction s u).adjoint = C.unitaryAction s u⁻¹)
    (spanning : ∀ k l s, SchurWeylMultilinearSpanning (Option (Fin k ⊕ Fin l)) (A s))
    (hcontraction : ∀ k l s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
      normalizedPermutationContraction π (fun i => T.inclusion s (v i)) =
        normalizedPermutationContraction π v)
    (labels : ∀ k l s, Option (Fin k ⊕ Fin l) → A s)
    (hlabels : ∀ k l s, Function.Injective (labels k l s))
    (n : ℕ) (a : G n) (d : E) (r : F) :
    Y.adjoint (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((wordLevelRepeatedOperator T U Y n).adjoint a)
        (endpointWord d (fun _ : Fin n => r))) := by
  have hl : ∀ s a, Y.adjoint.comp (C.leftAction s a) = (C.leftAction s a).comp Y.adjoint := by
    intro s a
    apply adjoint_commutes_of_adjoint_commutes
    rw [hleftStar]
    exact hleft s (star a)
  have hu : ∀ s u, Y.adjoint.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y.adjoint := by
    intro s u
    apply adjoint_commutes_of_adjoint_commutes
    rw [hunitaryStar]
    exact hunitary s u⁻¹
  simpa only [wordLevelRepeatedOperator_adjoint] using
    wordLevelRepeatedOperator_apply T U C Y.adjoint hl hu spanning hcontraction labels hlabels n a d r

end KadisonSimilarity

end

end OAI
