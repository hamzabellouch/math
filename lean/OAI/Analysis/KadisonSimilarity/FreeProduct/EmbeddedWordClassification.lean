import OAI.Analysis.KadisonSimilarity.Representation.NormalizedContractions
import OAI.Analysis.KadisonSimilarity.Tracial.CofinalMatrixTowers

namespace OAI

/-! The cofinal invariant-word classification for actual tracial matrix
embeddings. Finite labels and contraction compatibility are both derived. -/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hmul : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (S : RealTracialSequence τ)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop)


/-- Raw compatible matrix inclusions supply the contractions on every
cofinal tail and for every fixed pair of word degrees. -/
theorem embedded_word_contractions
    (k l b s : ℕ) (p : Equiv.Perm (Option (Fin k ⊕ Fin l)))
    (a : Option (Fin k ⊕ Fin l) → Matrix (A b) (A b) ℂ) :
    normalizedPermutationContraction p
      (fun i => (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize).transition b (b + s) (Nat.le_add_right b s) (a i)) =
      normalizedPermutationContraction p a :=
  NestedTracialMatrices.normalizedPermutationContraction_inclusion M b (b + s) (Nat.le_add_right b s) p a

variable {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)]
  [∀ n, InnerProductSpace ℂ (G n)] [∀ n, CompleteSpace (G n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : OrthogonalWordLevels (MultiplicityWordSpace G E (centeredSubspace (V 1))) H)
  (C : WordLevelMatrixActions (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U) (Y : H →L[ℂ] H)
  (hleft : ∀ s a, Y.comp (C.leftAction s a) = (C.leftAction s a).comp Y)
  (hunitary : ∀ s a, Y.comp (C.unitaryAction s a) = (C.unitaryAction s a).comp Y)

omit [∀ n, CompleteSpace (G n)] in
include hleft hunitary in
/-- Actual tracial matrix embeddings imply preservation of every word degree,
using the proved stable Schur--Weyl theorem on each cofinal tail. -/
theorem embedded_word_levels_preserved (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) :=
  cofinal_word_levels_preserved (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U C Y hleft hunitary
    (embedded_word_contractions τ V L hinner hmul M htrace S hsize) n

include hleft hunitary in
/-- The canonical bounded multiplicity operator acts on all repeated words. -/
theorem embedded_wordLevelRepeatedOperator_apply (n : ℕ) (a : G n) (d : E)
    (r : centeredSubspace (V 1)) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (wordLevelRepeatedOperator (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U Y n a)
        (endpointWord d (fun _ : Fin n => r))) :=
  cofinal_wordLevelRepeatedOperator_apply (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U C Y hleft hunitary
    (embedded_word_contractions τ V L hinner hmul M htrace S hsize) n a d r

include hleft hunitary in
/-- Bundled star and unitary representations give the adjoint repeated-word
identity, with the adjoint of the same canonical multiplicity operator. -/
theorem embedded_wordLevelRepeatedOperator_adjoint_apply
    (leftRep : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
    (left_eq : ∀ s a, C.leftAction s a = leftRep s a)
    (unitaryRep : ∀ s, Matrix.unitaryGroup (A s) ℂ →* unitary (H →L[ℂ] H))
    (unitary_eq : ∀ s a, C.unitaryAction s a = (unitaryRep s a : H →L[ℂ] H))
    (n : ℕ) (a : G n) (d : E) (r : centeredSubspace (V 1)) :
    Y.adjoint (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((wordLevelRepeatedOperator (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U Y n).adjoint a)
        (endpointWord d (fun _ : Fin n => r))) := by
  have hls (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
      (C.leftAction s a).adjoint = C.leftAction s (star a) := by
    rw [left_eq, left_eq, ← ContinuousLinearMap.star_eq_adjoint, map_star]
  have hus (s : ℕ) (a : Matrix.unitaryGroup (A s) ℂ) :
      (C.unitaryAction s a).adjoint = C.unitaryAction s a⁻¹ := by
    rw [unitary_eq, unitary_eq, ← ContinuousLinearMap.star_eq_adjoint,
      ← Unitary.coe_star, Unitary.star_eq_inv, map_inv]
  have hl (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
      Y.adjoint.comp (C.leftAction s a) = (C.leftAction s a).comp Y.adjoint := by
    apply adjoint_commutes_of_adjoint_commutes
    rw [hls]
    exact hleft s (star a)
  have hu (s : ℕ) (a : Matrix.unitaryGroup (A s) ℂ) :
      Y.adjoint.comp (C.unitaryAction s a) = (C.unitaryAction s a).comp Y.adjoint := by
    apply adjoint_commutes_of_adjoint_commutes
    rw [hus]
    exact hunitary s a⁻¹
  simpa only [wordLevelRepeatedOperator_adjoint] using
    cofinal_wordLevelRepeatedOperator_apply (tracialMatrixTowerOfEmbeddings τ V L hinner hmul M htrace S hsize) U C Y.adjoint hl hu
      (embedded_word_contractions τ V L hinner hmul M htrace S hsize) n a d r

end KadisonSimilarity

end

end OAI
