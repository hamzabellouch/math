import OAI.Analysis.KadisonSimilarity.FreeProduct.EmbeddedWordActions

namespace OAI

/-! Word-level structure from actual tracial matrix actions. The application
interface has no abstract covariance record: it contains only represented
matrix actions, their raw word formulas, and commutation. -/

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
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (S : RealTracialSequence τ)
  (hsize : Filter.Tendsto (fun s => (Fintype.card (A s) : ℝ)) Filter.atTop Filter.atTop)
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)] [∀ n, InnerProductSpace ℂ (J n)]
  [∀ n, CompleteSpace (J n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : OrthogonalWordLevels (MultiplicityWordSpace J E (centeredSubspace (V 1))) H)
  (leftRep : ∀ s, Matrix (A s) (A s) ℂ →⋆ₐ[ℂ] (H →L[ℂ] H))
  (unitaryRep : ∀ s, Matrix.unitaryGroup (A s) ℂ →* unitary (H →L[ℂ] H))
  (hL : ∀ s a n, (leftRep s a).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (endpointHeadAction (n := n)
        (((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left a))))
  (hU : ∀ s u n, (unitaryRep s u : H →L[ℂ] H).comp (U.inclusion n).toContinuousLinearMap =
    (U.inclusion n).toContinuousLinearMap.comp
      (hilbertTensorLift (tracialMatrixWordAction τ V L (M.embedding s) hinner hleft htrace
        (NestedTracialMatrices.denseRange_vector τ V M) u n).toContinuousLinearMap))
  (Y : H →L[ℂ] H)
  (hYL : ∀ s a, Y.comp (leftRep s a) = (leftRep s a).comp Y)
  (hYU : ∀ s u, Y.comp (unitaryRep s u : H →L[ℂ] H) =
    (unitaryRep s u : H →L[ℂ] H).comp Y)

include hL hU hYL hYU in
omit [∀ n, CompleteSpace (J n)] in
/-- Actual represented matrix symmetries force preservation of every word
level; the covariance and finite labels are derived in the proof. -/
theorem embedded_actions_word_levels_preserved (n : ℕ) :
    Y.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (U.block Y n n) :=
  embedded_word_levels_preserved τ V L hinner hleft M htrace S hsize U
    (embeddedWordMatrixActions τ V L hinner hleft M htrace S hsize U leftRep unitaryRep hL hU)
    Y hYL hYU n

include hL hU hYL hYU in
/-- The canonical multiplicity compression acts on every repeated word. -/
theorem embedded_actions_repeated_word (n : ℕ) (a : J n) (d : E)
    (r : centeredSubspace (V 1)) :
    Y (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert
        (wordLevelRepeatedOperator (tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize)
          U Y n a) (endpointWord d (fun _ : Fin n => r))) :=
  embedded_wordLevelRepeatedOperator_apply τ V L hinner hleft M htrace S hsize U
    (embeddedWordMatrixActions τ V L hinner hleft M htrace S hsize U leftRep unitaryRep hL hU)
    Y hYL hYU n a d r

include hL hU hYL hYU in
/-- Taking adjoints gives the same repeated-word action with the adjoint of
the canonical multiplicity operator; no second covariance input is needed. -/
theorem embedded_actions_adjoint_repeated_word (n : ℕ) (a : J n) (d : E)
    (r : centeredSubspace (V 1)) :
    Y.adjoint (U.inclusion n (hilbertTensorInsert a (endpointWord d (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert
        ((wordLevelRepeatedOperator (tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize)
          U Y n).adjoint a) (endpointWord d (fun _ : Fin n => r))) :=
  embedded_wordLevelRepeatedOperator_adjoint_apply τ V L hinner hleft M htrace S hsize U
    (embeddedWordMatrixActions τ V L hinner hleft M htrace S hsize U leftRep unitaryRep hL hU)
    Y hYL hYU leftRep (fun _ _ => rfl) unitaryRep (fun _ _ => rfl) n a d r

end KadisonSimilarity

end

end OAI
