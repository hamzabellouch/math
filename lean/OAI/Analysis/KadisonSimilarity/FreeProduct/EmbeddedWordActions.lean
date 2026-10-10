import OAI.Analysis.KadisonSimilarity.FreeProduct.EmbeddedWordClassification
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixCovariance

namespace OAI

/-! Actual embedded matrix actions supply the action record used by the
invariant-word classification. Adjoint covariance follows from the represented
star and inverse laws, and the source/test formulas from tracial word covariance. -/

noncomputable section
namespace KadisonSimilarity

section TensorAdjoints
variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem hilbertTensorLift_adjoint (T : K →L[ℂ] K) :
    (hilbertTensorLift (G := F) T).adjoint = hilbertTensorLift T.adjoint := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro a x
  apply hilbertTensor_ext_inner_insert
  intro b y
  simp only [ContinuousLinearMap.adjoint_inner_right, hilbertTensorLift_insert,
    inner_hilbertTensorInsert]

theorem endpointHeadAction_adjoint {n : ℕ} (p : E →L[ℂ] E) :
    (endpointHeadAction (F := F) (n := n) p).adjoint = endpointHeadAction p.adjoint := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro d x
  apply hilbertTensor_ext_inner_insert
  intro c y
  change inner ℂ (endpointInsert c y)
      ((endpointHeadAction p).adjoint (endpointInsert d x)) =
    inner ℂ (endpointInsert c y) (endpointHeadAction p.adjoint (endpointInsert d x))
  rw [ContinuousLinearMap.adjoint_inner_right, endpointHeadAction_insert,
    endpointHeadAction_insert, inner_endpointInsert, inner_endpointInsert,
    ContinuousLinearMap.adjoint_inner_right]

end TensorAdjoints

section TracialInverses
universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {α : Type*} [Fintype α] [DecidableEq α]
  (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a)) (hdense : DenseRange V)

include hleft in
/-- Inverse matrix conjugations cancel on the entire tracial Hilbert space,
by their algebraic action on its dense represented vectors. -/
theorem tracialUnitaryConjugation_mul_inv (u : Matrix.unitaryGroup α ℂ) (x : E) :
    tracialUnitaryConjugation τ V L ι hinner htrace hdense u
      (tracialUnitaryConjugation τ V L ι hinner htrace hdense u⁻¹ x) = x := by
  refine hdense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense,
    tracialUnitaryConjugation_apply_vector τ V L ι hinner hleft htrace hdense]
  have hinv : ι (↑u⁻¹ : Matrix α α ℂ) = star (ι (u : Matrix α α ℂ)) := by
    rw [← Unitary.star_eq_inv, Unitary.coe_star, map_star]
  have hunit : ι (u : Matrix α α ℂ) * star (ι (u : Matrix α α ℂ)) = 1 := by
    have hu : (u : Matrix α α ℂ) * star (u : Matrix α α ℂ) = 1 := u.property.2
    rw [← map_star, ← map_mul, hu, map_one]
  rw [hinv, star_star]
  congr 1
  calc
    ι (u : Matrix α α ℂ) * (star (ι (u : Matrix α α ℂ)) * a *
        ι (u : Matrix α α ℂ)) * star (ι (u : Matrix α α ℂ)) =
      (ι (u : Matrix α α ℂ) * star (ι (u : Matrix α α ℂ))) * a *
        (ι (u : Matrix α α ℂ) * star (ι (u : Matrix α α ℂ))) := by noncomm_ring
    _ = a := by rw [hunit, one_mul, mul_one]

theorem centeredUnitaryConjugation_mul_inv (u : Matrix.unitaryGroup α ℂ)
    (x : centeredSubspace (V 1)) :
    centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u
      (centeredUnitaryConjugation τ V L ι hinner hleft htrace hdense u⁻¹ x) = x := by
  apply Subtype.ext
  exact tracialUnitaryConjugation_mul_inv τ V L ι hinner hleft htrace hdense u x

/-- The inverse word action is obtained by inverting the actual matrix unitary. -/
theorem tracialMatrixWordAction_mul_inv (u : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u n).toContinuousLinearMap.comp
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u⁻¹ n).toContinuousLinearMap =
        ContinuousLinearMap.id ℂ (EndpointTensor E (centeredSubspace (V 1)) n) := by
  apply continuousLinearMap_ext_endpointWords
  intro d x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    tracialMatrixWordAction, endpointTensorIsometry_apply,
    tracialUnitaryConjugation_mul_inv τ V L ι hinner hleft htrace hdense,
    centeredUnitaryConjugation_mul_inv τ V L ι hinner hleft htrace hdense]

/-- The adjoint action on completed words is the inverse matrix action. -/
theorem tracialMatrixWordAction_adjoint (u : Matrix.unitaryGroup α ℂ) (n : ℕ) :
    (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u n).toContinuousLinearMap.adjoint =
      (tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u⁻¹ n).toContinuousLinearMap := by
  let W := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u n
  let Z := tracialMatrixWordAction τ V L ι hinner hleft htrace hdense u⁻¹ n
  have hW : W.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ := W.adjoint_comp_self
  have hZ : W.toContinuousLinearMap.comp Z.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ _ :=
    tracialMatrixWordAction_mul_inv τ V L ι hinner hleft htrace hdense u n
  change W.toContinuousLinearMap.adjoint = Z.toContinuousLinearMap
  calc
    W.toContinuousLinearMap.adjoint =
        W.toContinuousLinearMap.adjoint.comp (ContinuousLinearMap.id ℂ _) := by simp
    _ = W.toContinuousLinearMap.adjoint.comp (W.toContinuousLinearMap.comp Z.toContinuousLinearMap) := by rw [hZ]
    _ = (W.toContinuousLinearMap.adjoint.comp W.toContinuousLinearMap).comp Z.toContinuousLinearMap :=
      (ContinuousLinearMap.comp_assoc _ _ _).symm
    _ = Z.toContinuousLinearMap := by rw [hW, ContinuousLinearMap.id_comp]

end TracialInverses

section EmbeddedActions
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

/-- The action record for the invariant classification, obtained from actual
representations and the two raw word inclusion formulas alone. -/
def embeddedWordMatrixActions :
    WordLevelMatrixActions (tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize) U where
  leftAction s a := leftRep s a
  unitaryAction s u := unitaryRep s u
  wordAction s n u := tracialMatrixWordAction τ V L (M.embedding s) hinner hleft htrace
    (NestedTracialMatrices.denseRange_vector τ V M) u n
  left_inclusion := hL
  left_adjoint_inclusion s a n := by
    have hstar :
        ((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left (star a) =
          (((tracialMatrixTowerOfEmbeddings τ V L hinner hleft M htrace S hsize).stage s).left a).adjoint := by
      change L (M.embedding s (star a)) = (L (M.embedding s a)).adjoint
      rw [map_star, map_star, ContinuousLinearMap.star_eq_adjoint]
    simpa only [map_star, ContinuousLinearMap.star_eq_adjoint, hstar,
      hilbertTensorLift_adjoint, endpointHeadAction_adjoint] using hL s (star a) n
  unitary_inclusion := hU
  unitary_adjoint_inclusion s u n := by
    have hstar : (unitaryRep s u⁻¹ : H →L[ℂ] H) = (unitaryRep s u : H →L[ℂ] H).adjoint := by
      rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star, ContinuousLinearMap.star_eq_adjoint]
    simpa only [hstar, hilbertTensorLift_adjoint,
      tracialMatrixWordAction_adjoint] using hU s u⁻¹ n
  source_word s n u v := by
    let C := tracialMatrixWordCovariance τ V L (M.embedding s) hinner hleft htrace
      (NestedTracialMatrices.denseRange_vector τ V M) (NestedTracialMatrices.trace_one τ V M)
      (M.trace_embedding s) (Y := (0 : EndpointTensor E (centeredSubspace (V 1)) n →L[ℂ]
        EndpointTensor E (centeredSubspace (V 1)) n)) (by intro w; simp)
    exact C.source_covariance u (fun x => match x with
      | none => 0
      | some (.inl i) => v i
      | some (.inr _) => 0)
  test_word s n u a v := by
    let C := tracialMatrixWordCovariance τ V L (M.embedding s) hinner hleft htrace
      (NestedTracialMatrices.denseRange_vector τ V M) (NestedTracialMatrices.trace_one τ V M)
      (M.trace_embedding s) (Y := (0 : EndpointTensor E (centeredSubspace (V 1)) n →L[ℂ]
        EndpointTensor E (centeredSubspace (V 1)) n)) (by intro w; simp)
    exact C.test_covariance u (fun x => match x with
      | none => a
      | some (.inl _) => 0
      | some (.inr i) => v i)

end EmbeddedActions
end KadisonSimilarity

end

end OAI
