import Mathlib
import OAI.Analysis.Commutator.FreeActualCovariance

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (hij : i≠j) (hcolors : ∀ c : ι, c=i ∨ c=j)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))

variable (hDgen : ∀ a : D, (factorTrace t f hf).gnsStarAlgHom a ∈
  Set.centralizer (Set.centralizer
    (TracialGNS.stageAlgebra (factorTrace t f hf) I φ : Set _)))

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G.comp (t.functional.gnsStarAlgHom (f a))=
  (t.functional.gnsStarAlgHom (f a)).comp G)

variable (hGW : ∀ n u, G.comp
  (innerRepresentation t ht f S i hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap =
  (innerRepresentation t ht f S i hS hfree hgen (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap.comp G)

private abbrev embeddedSourceWord (level : ℕ) (scalar : factorFull t f hf)
    (centered : factorZero t f hf) (coefficient : multiplicityLevel t S j level) :
    t.functional.GNS :=
  sourceLevelEmbedding t f hf S i j hS hfree hij level
    (HilbertTensor.pair (E := sourceScalar t f hf level) (J := multiplicityLevel t S j level)
      (PreHilbert.word (factorFull t f hf) (factorZero t f hf) level scalar
        (fun _ => centered)) coefficient)

private structure WordActions (algebra : Type) [CStarAlgebra algebra] where
  full : PreHilbert
  centered : PreHilbert
  left : algebra → full →L[ℂ] full
  conjugation : unitary algebra → full →ₗᵢ[ℂ] full
  centeredConjugation : unitary algebra → centered →ₗᵢ[ℂ] centered

private def tracialWordActions (functional : D →ₚ[ℂ] ℂ)
    (tracial : ∀ first second : D, functional (first * second) =
      functional (second * first)) : WordActions D where
  full := TracialGNS.fullSpace functional
  centered := TracialGNS.zeroSpace functional
  left := functional.gnsStarAlgHom
  conjugation := TracialGNS.conjugation functional tracial
  centeredConjugation unitary := centeredIsometry (TracialGNS.vacuum functional)
    (TracialGNS.conjugation functional tracial unitary)
    (TracialGNS.conjugation_vacuum functional tracial unitary)

private def faithfulWordActions (state : FaithfulState D)
    (tracial : ∀ first second : D, state.functional (first * second) =
      state.functional (second * first)) : WordActions D where
  full := ⟨state.functional.GNS⟩
  centered := ⟨HilbertCompletion.centered
    ((state.functional.toPreGNS 1 : preSpace state) : state.functional.GNS)⟩
  left := state.functional.gnsStarAlgHom
  conjugation := TracialGNS.conjugation state.functional tracial
  centeredConjugation unitary := centeredIsometry (TracialGNS.vacuum state.functional)
    (TracialGNS.conjugation state.functional tracial unitary)
    (TracialGNS.conjugation_vacuum state.functional tracial unitary)

private theorem faithfulWordActions_eq (state : FaithfulState D)
    (tracial : ∀ first second : D, state.functional (first * second) =
      state.functional (second * first)) :
    faithfulWordActions state tracial = tracialWordActions state.functional tracial := by
  rfl

private abbrev wordLevel (actions : WordActions D) (multiplicity : ℕ → Type*)
    [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)] (level : ℕ) :=
  Completion (PreHilbert.wordSpace actions.full actions.centered level ⊗[ℂ] multiplicity level)

private abbrev wordLeftAction (actions : WordActions D) (multiplicity : ℕ → Type*)
    [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)] (element : D) (level : ℕ) :
    wordLevel actions multiplicity level →L[ℂ] wordLevel actions multiplicity level :=
  HilbertTensor.map (HilbertTensor.map (actions.left element)
    (1 : PreHilbert.power actions.centered level →L[ℂ] PreHilbert.power actions.centered level))
    (1 : multiplicity level →L[ℂ] multiplicity level)

private abbrev wordConjugationAction (actions : WordActions D) (multiplicity : ℕ → Type*)
    [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)] (unitary : unitary D) (level : ℕ) :
    wordLevel actions multiplicity level →L[ℂ] wordLevel actions multiplicity level :=
  HilbertTensor.map (PreHilbert.wordMap actions.full actions.centered
    (actions.conjugation unitary) (actions.centeredConjugation unitary) level).toContinuousLinearMap
    (1 : multiplicity level →L[ℂ] multiplicity level)

private abbrev wordStructure (full centered : PreHilbert)
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient]
    (embedding : ∀ level, Completion
      (PreHilbert.wordSpace full centered level ⊗[ℂ] multiplicity level) →ₗᵢ[ℂ] ambient)
    (operator : ambient →L[ℂ] ambient) : Prop :=
  ∃ coefficient : ∀ level, multiplicity level →L[ℂ] multiplicity level,
    (∀ level, ‖coefficient level‖ ≤ ‖operator‖) ∧
    (∀ level (scalar : full) (letter : centered) (vector : multiplicity level),
      operator (embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter)) vector)) =
      embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter)) (coefficient level vector))) ∧
    (∀ level (scalar : full) (letter : centered) (vector : multiplicity level),
      operator.adjoint (embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter)) vector)) =
      embedding level (HilbertTensor.pair
        (PreHilbert.word full centered level scalar (fun _ => letter))
        ((coefficient level).adjoint vector)))

private def wordStructureRule (actions : WordActions D)
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient]
    : Prop :=
  ∀ (embedding : ∀ level, wordLevel actions multiplicity level →ₗᵢ[ℂ] ambient),
    IsHilbertSum ℂ (wordLevel actions multiplicity) embedding →
    ∀ (left : D → ambient →L[ℂ] ambient)
    (symmetries : ∀ stage, unitary (Matrix (I stage) (I stage) ℂ) → ambient →L[ℂ] ambient)
    (operator : ambient →L[ℂ] ambient),
    (∀ element level, (left element).comp (embedding level).toContinuousLinearMap =
      (embedding level).toContinuousLinearMap.comp
        (wordLeftAction actions multiplicity element level)) →
    (∀ stage unitary level,
      (symmetries stage unitary).comp (embedding level).toContinuousLinearMap =
      (embedding level).toContinuousLinearMap.comp
        (wordConjugationAction actions multiplicity
          (TracialGNS.stageUnitary (φ stage) unitary) level)) →
    (∀ element, operator.comp (left element) = (left element).comp operator) →
    (∀ stage unitary, operator.comp (symmetries stage unitary) =
      (symmetries stage unitary).comp operator) →
    wordStructure actions.full actions.centered multiplicity ambient embedding operator

include he hsize in
private theorem tracial_word_structure (functional : D →ₚ[ℂ] ℂ)
    (tracial : ∀ first second : D, functional (first * second) =
      functional (second * first)) (normalized : functional 1 = 1)
    (generation : ∀ element : D, functional.gnsStarAlgHom element ∈
      Set.centralizer (Set.centralizer (TracialGNS.stageAlgebra functional I φ : Set _)))
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient] :
    wordStructureRule I φ (tracialWordActions functional tracial) multiplicity ambient := by
  intro embedding total left symmetries operator left_covariant symmetries_covariant
    commutes_left commutes_symmetries
  exact TracialGNS.actual_word_structure functional tracial normalized multiplicity embedding total
    I φ e he hsize generation left symmetries left_covariant symmetries_covariant operator
    commutes_left commutes_symmetries

include he hsize in
private theorem faithful_word_structure (state : FaithfulState D)
    (tracial : ∀ first second : D, state.functional (first * second) =
      state.functional (second * first))
    (generation : ∀ element : D, state.functional.gnsStarAlgHom element ∈
      Set.centralizer (Set.centralizer
        (TracialGNS.stageAlgebra state.functional I φ : Set _)))
    (multiplicity : ℕ → Type*) [∀ level, NormedAddCommGroup (multiplicity level)]
    [∀ level, InnerProductSpace ℂ (multiplicity level)]
    [∀ level, CompleteSpace (multiplicity level)]
    (ambient : Type*) [NormedAddCommGroup ambient] [InnerProductSpace ℂ ambient] [CompleteSpace ambient] :
    wordStructureRule I φ (faithfulWordActions state tracial) multiplicity ambient := by
  rw [faithfulWordActions_eq]
  exact tracial_word_structure I φ e he hsize state.functional tracial state.normalized generation
    multiplicity ambient

private lemma faithful_left_level (a : D) (n : ℕ) :
    (t.functional.gnsStarAlgHom (f a)).comp
      (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap =
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
      (wordLeftAction (faithfulWordActions (pullbackState t f hf)
        (factorTrace_tracial t f hf ht)) (multiplicityLevel t S j) a n) := by
  exact (sourceLevelEmbedding_left t f hf S i j hS hfree hij a n).symm

private lemma faithful_conjugation_level (u : unitary D) (n : ℕ) :
    (innerRepresentation t ht f S i hS hfree hgen u).toLinearIsometry.toContinuousLinearMap.comp
      (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap =
    (sourceLevelEmbedding t f hf S i j hS hfree hij n).toContinuousLinearMap.comp
      (wordConjugationAction (faithfulWordActions (pullbackState t f hf)
        (factorTrace_tracial t f hf ht)) (multiplicityLevel t S j) u n) := by
  exact innerRepresentation_level t ht f hf S i j hS hfree hgen hij u n

include hgen hcolors he hsize hDgen hGL hGW in
theorem free_word_structure : ∃ B : ∀ k, multiplicityLevel t S j k →L[ℂ] multiplicityLevel t S j k,
    (∀ k, ‖B k‖ ≤ ‖G‖) ∧
    (∀ k (d : factorFull t f hf)
      (x : factorZero t f hf) (a : multiplicityLevel t S j k),
      G (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
        embeddedSourceWord t f hf S i j hS hfree hij k d x (B k a)) ∧
    (∀ k (d : factorFull t f hf)
      (x : factorZero t f hf) (a : multiplicityLevel t S j k),
      G.adjoint (embeddedSourceWord t f hf S i j hS hfree hij k d x a) =
        embeddedSourceWord t f hf S i j hS hfree hij k d x ((B k).adjoint a)) := by
  have hcov (stage : ℕ) (u : unitary (Matrix (I stage) (I stage) ℂ)) (level : ℕ) :=
    faithful_conjugation_level t ht f hf S i j hS hfree hgen hij
      (by exact TracialGNS.stageUnitary (φ stage) u) level
  have rule := faithful_word_structure I φ e he hsize (pullbackState t f hf)
    (factorTrace_tracial t f hf ht) hDgen (multiplicityLevel t S j) t.functional.GNS
  have embedded := rule (sourceLevelEmbedding t f hf S i j hS hfree hij)
    (sourceLevelIsHilbertSum t f hf S i j hS hfree hij hcolors hgen)
  have h := embedded (fun a => t.functional.gnsStarAlgHom (f a))
    (fun n u => (innerRepresentation t ht f S i hS hfree hgen
      (TracialGNS.stageUnitary (φ n) u)).toLinearIsometry.toContinuousLinearMap)
    G (faithful_left_level t ht f hf S i j hS hfree hij) hcov hGL hGW
  exact h

end Kadison.FreeBlocks

end

end OAI
