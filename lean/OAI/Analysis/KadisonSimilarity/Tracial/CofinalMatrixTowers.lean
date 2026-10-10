import OAI.Analysis.KadisonSimilarity.Tensor.TensorStableSpanning
import OAI.Analysis.KadisonSimilarity.FreeProduct.WordLevelRepeatedOperators
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixTower

namespace OAI

/-! Word degrees are fixed before the matrix stage is chosen. Cofinal tails
let each degree start in its own stable range; no single finite stage must
accommodate every number of tensor slots. -/

noncomputable section
namespace KadisonSimilarity

open Filter

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

private theorem iUnion_nat_tail {X : Type*} (S : ℕ → Set X) (hS : Monotone S) (b : ℕ) :
    (⋃ s, S (b + s)) = ⋃ s, S s := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_mono' (fun s => ⟨b + s, Set.Subset.refl _⟩)
  · apply Set.iUnion_subset
    intro s
    exact (hS (Nat.le_add_left s b)).trans (Set.subset_iUnion (fun s => S (b + s)) s)

/-- Discarding finitely many matrix stages preserves every geometric field of
the tower and its dense union. -/
def TracialMatrixTower.tail
    (T : TracialMatrixTower (E := E) (F := F) (A := A)) (b : ℕ) :
    TracialMatrixTower (E := E) (F := F) (A := fun s => A (b + s)) where
  stage s := T.stage (b + s)
  traceVector := T.traceVector
  norm_traceVector := T.norm_traceVector
  unit_realization s := T.unit_realization (b + s)
  conjugation := T.conjugation
  conjugation_involutive := T.conjugation_involutive
  pairing := T.pairing
  pairing_conjugation := T.pairing_conjugation
  pairing_matrix s := T.pairing_matrix (b + s)
  inclusion s := T.transition b (b + s) (Nat.le_add_right b s)
  full_compatible s a := T.full_transition b (b + s) _ a
  center_compatible s a := T.center_transition b (b + s) _ a
  transition s t h := T.transition (b + s) (b + t) (Nat.add_le_add_left h b)
  full_transition s t h := T.full_transition (b + s) (b + t) _
  center_transition s t h := T.center_transition (b + s) (b + t) _
  full_mono := T.full_mono.comp (fun _ _ h => Nat.add_le_add_left h b)
  center_mono := T.center_mono.comp (fun _ _ h => Nat.add_le_add_left h b)
  full_dense := by
    change Dense (⋃ s, fullMatrixStage T.stage (b + s))
    rw [iUnion_nat_tail _ T.full_mono]
    exact T.full_dense
  center_dense := by
    change Dense (⋃ s, centeredMatrixStage T.stage (b + s))
    rw [iUnion_nat_tail _ T.center_mono]
    exact T.center_dense
  size_tendsto := T.size_tendsto.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat b)
  realOrthonormal := T.realOrthonormal
  realOrthonormal_orthonormal := T.realOrthonormal_orthonormal
  realOrthonormal_fixed := T.realOrthonormal_fixed

omit [∀ s, Nonempty (A s)] in
/-- Every fixed finite set of tensor slots has injective labels at all stages
of a sufficiently late tail. -/
theorem TracialMatrixTower.exists_tail_labels
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (ι : Type*) [Fintype ι] :
    ∃ b : ℕ, ∃ labels : ∀ s, ι → A (b + s), ∀ s, Function.Injective (labels s) := by
  classical
  have he := (tendsto_atTop.mp T.size_tendsto) (Fintype.card ι : ℝ)
  obtain ⟨b, hb⟩ := eventually_atTop.mp he
  have hc (s : ℕ) : Fintype.card ι ≤ Fintype.card (A (b + s)) := by
    exact_mod_cast hb (b + s) (Nat.le_add_right b s)
  let labels (s : ℕ) : ι ↪ A (b + s) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hc s))
  exact ⟨b, fun s => labels s, fun s => (labels s).injective⟩

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Ambient actions restrict to the same cofinal sequence of matrix stages. -/
def WordLevelMatrixActions.tail
    (T : TracialMatrixTower (E := E) (F := F) (A := A))
    (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)
    (C : WordLevelMatrixActions T U) (b : ℕ) : WordLevelMatrixActions (T.tail b) U where
  leftAction s := C.leftAction (b + s)
  unitaryAction s := C.unitaryAction (b + s)
  wordAction s := C.wordAction (b + s)
  left_inclusion s := C.left_inclusion (b + s)
  left_adjoint_inclusion s := C.left_adjoint_inclusion (b + s)
  unitary_inclusion s := C.unitary_inclusion (b + s)
  unitary_adjoint_inclusion s := C.unitary_adjoint_inclusion (b + s)
  source_word s := C.source_word (b + s)
  test_word s := C.test_word (b + s)

variable (T : TracialMatrixTower (E := E) (F := F) (A := A))
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E F) H)
  (C : WordLevelMatrixActions T U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s u, Y.comp (C.unitaryAction s u) = (C.unitaryAction s u).comp Y)
  (hcontraction : ∀ k l b s (π : Equiv.Perm (Option (Fin k ⊕ Fin l))) v,
    normalizedPermutationContraction π
      (fun i => T.transition b (b + s) (Nat.le_add_right b s) (v i)) =
      normalizedPermutationContraction π v)

omit [∀ n, CompleteSpace (G n)] in
include hleft hunitary hcontraction in
/-- Each off-diagonal degree pair uses its own cofinal stable range. In
particular no fixed finite matrix algebra needs infinitely many labels. -/
theorem cofinal_word_levels_preserved (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) := by
  apply U.preserves_of_offDiagonal_zero Y
  intro l k hkl
  obtain ⟨b, labels, hlabels⟩ := T.exists_tail_labels (Option (Fin k ⊕ Fin l))
  exact crossMultiplicity_intertwiner_zero_of_schurWeyl (T.tail b) (U.block Y l k)
    (fun s a => U.block_intertwines Y (C.leftAction (b + s) a) _ _ (hleft (b + s) a)
      (C.left_inclusion (b + s) a k) (C.left_adjoint_inclusion (b + s) a l))
    (fun s => WordLevelMatrixActions.blockCovariance (T.tail b) U (C.tail T U b) Y
      (fun s a => hunitary (b + s) a) s k l)
    (fun s => schurWeylMultilinearSpanning_of_labels (labels s) (hlabels s)) (hcontraction k l b) labels hlabels (Ne.symm hkl)

include hleft hunitary hcontraction in
/-- Repeated-word action with the finite-label requirement discharged using
the matrix-size limit, separately for each word degree. -/
theorem cofinal_wordLevelRepeatedOperator_apply (n : ℕ) (a : G n) (d : E) (r : F) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (wordLevelRepeatedOperator T U Y n a)
        (endpointWord d (fun _ : Fin n => r))) := by
  obtain ⟨b, labels, hlabels⟩ := T.exists_tail_labels (Option (Fin n ⊕ Fin n))
  have hb := wordLevelRepeatedOperator_block_apply (T.tail b) U (C.tail T U b) Y
    (fun s a => hleft (b + s) a) (fun s a => hunitary (b + s) a) n
    (fun s => schurWeylMultilinearSpanning_of_labels (labels s) (hlabels s)) (hcontraction n n b) labels hlabels a d r
  have hp := congrArg (fun f : MultiplicityWordSpace G E F n →L[ℂ] H =>
    f (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r))))
    (cofinal_word_levels_preserved T U C Y hleft hunitary hcontraction n)
  change Y (U.inclusion n _) = U.inclusion n (U.block Y n n _) at hp
  rw [hp]
  exact congrArg (U.inclusion n) hb

end KadisonSimilarity

end

end OAI
