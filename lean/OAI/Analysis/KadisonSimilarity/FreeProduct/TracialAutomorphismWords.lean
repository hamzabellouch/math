import OAI.Analysis.KadisonSimilarity.Tracial.TracialAutomorphisms
import OAI.Analysis.KadisonSimilarity.FreeProduct.ReducedWordModel
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialWordDensity
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMatrixCovariance
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeProductAutomorphisms

namespace OAI

/-! The matrix-unitary word formula is derived from the algebraic product
formula and the actual implementation of a trace-preserving automorphism. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

/-- The genuine endpoint action on the tracial Hilbert space of the other factor. -/
def baseMatrixWordAction (n : ℕ) :
    EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n →ₗᵢ[ℂ]
      EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n :=
  tracialMatrixWordAction (G.baseGeometry D).trace (G.baseGeometry D).vector
    (G.baseGeometry D).left ι (G.baseGeometry D).inner_vector
    (G.baseGeometry D).left_vector (G.baseGeometry D).tracial
    (G.baseGeometry D).dense_vector u n

theorem centeredMatrixConjugation_letter (c : D) (hc : G.trace (c : P) = 0) :
    centeredUnitaryConjugation (G.baseGeometry D).trace (G.baseGeometry D).vector
      (G.baseGeometry D).left ι (G.baseGeometry D).inner_vector
      (G.baseGeometry D).left_vector (G.baseGeometry D).tracial
      (G.baseGeometry D).dense_vector u (G.baseSymmetryLetter D c hc) =
    G.baseSymmetryLetter D (matrixConjugateLetter D ι u c)
      ((G.trace_matrixConjugateLetter D ι u c).trans hc) := by
  apply Subtype.ext
  exact tracialUnitaryConjugation_apply_vector (G.baseGeometry D).trace
    (G.baseGeometry D).vector (G.baseGeometry D).left ι
    (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
    (G.baseGeometry D).tracial (G.baseGeometry D).dense_vector u c

/-- The completed endpoint action sends every bounded tensor word to the
word whose other-factor letters have been conjugated. -/
theorem baseMatrixWordAction_endpoint (n : ℕ) (d : D) (c : Fin n → D)
    (hc : ∀ i, G.trace (c i : P) = 0) :
    G.baseMatrixWordAction D ι u n (tracialEndpointWord G D n d c hc) =
      tracialEndpointWord G D n (matrixConjugateLetter D ι u d)
        (fun i => matrixConjugateLetter D ι u (c i))
        (fun i => (G.trace_matrixConjugateLetter D ι u (c i)).trans (hc i)) := by
  simp only [baseMatrixWordAction, tracialMatrixWordAction, tracialEndpointWord]
  refine (endpointTensorIsometry_apply
    (tracialUnitaryConjugation (G.baseGeometry D).trace (G.baseGeometry D).vector
      (G.baseGeometry D).left ι (G.baseGeometry D).inner_vector
      (G.baseGeometry D).tracial (G.baseGeometry D).dense_vector u)
    (centeredUnitaryConjugation (G.baseGeometry D).trace (G.baseGeometry D).vector
      (G.baseGeometry D).left ι (G.baseGeometry D).inner_vector
      (G.baseGeometry D).left_vector (G.baseGeometry D).tracial
      (G.baseGeometry D).dense_vector u)
    (G.baseVector D d) (fun i => G.baseSymmetryLetter D (c i) (hc i))).trans ?_
  apply congrArg₂ (fun d (x : Fin n → centeredSubspace (G.baseVector D 1)) =>
    endpointWord d x)
  · exact tracialUnitaryConjugation_apply_vector (G.baseGeometry D).trace
      (G.baseGeometry D).vector (G.baseGeometry D).left ι
      (G.baseGeometry D).inner_vector (G.baseGeometry D).left_vector
      (G.baseGeometry D).tracial (G.baseGeometry D).dense_vector u d
  · funext i
    exact G.centeredMatrixConjugation_letter D ι u (c i) (hc i)

variable (A : StarSubalgebra ℂ P) [IsClosed (A : Set P)]

/-- The multiplicity letters are fixed, and the endpoint letters are
conjugated by the represented matrix unitary. -/
theorem baseMatrixWordAction_tensor (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap
      (tracialWordTensor G A D n d b a c ha hc) =
    tracialWordTensor G A D n (matrixConjugateLetter D ι u d) b a
      (fun i => matrixConjugateLetter D ι u (c i)) ha
      (fun i => (G.trace_matrixConjugateLetter D ι u (c i)).trans (hc i)) := by
  simp only [tracialWordTensor, hilbertTensorLift_insert,
    LinearIsometry.coe_toContinuousLinearMap, G.baseMatrixWordAction_endpoint]

end TracialCornerGeometry

/-- A star-algebra automorphism transports a finite alternating product letterwise. -/
theorem automorphism_alternatingProduct (θ : P ≃⋆ₐ[ℂ] P) {n : ℕ}
    (a c : Fin n → P) :
    θ (alternatingProduct a c) =
      alternatingProduct (fun i => θ (a i)) (fun i => θ (c i)) := by
  simp only [alternatingProduct, map_list_prod, List.map_ofFn, Function.comp_def, map_mul]

namespace TracialWordFormula

open TracialCornerGeometry

variable {G : TracialCornerGeometry P H} {A D : StarSubalgebra ℂ P}
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (θ : P ≃⋆ₐ[ℂ] P) (hθ : ∀ x, G.trace (θ x) = G.trace x)
  (hA : ∀ a : A, θ (a : P) = (a : P))
  (hD : ∀ d : D, θ (d : P) = (matrixConjugateLetter D ι u d : P))

local instance automorphismMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance automorphismMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

variable
  {U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H}

include hA hD in
/-- On bounded tracial words, automorphism covariance is a consequence of
multiplicativity, factor fixation, and the reduced-word product formula. -/
theorem automorphism_word (hU : TracialWordFormula G A D U)
    (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    G.automorphismUnitary θ hθ
      (U.inclusion n (tracialWordTensor G A D n d b a c ha hc)) =
    U.inclusion n (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap
      (tracialWordTensor G A D n d b a c ha hc)) := by
  rw [G.baseMatrixWordAction_tensor, hU, hU, G.automorphismUnitary_vector]
  congr 1
  simp only [map_mul, automorphism_alternatingProduct, hA, hD]

/-- A bounded word intertwining identity extends from the actual algebra
letters to the entire completed word level. -/
theorem intertwining_of_bounded_words (hτ : G.trace 1 = 1) (n : ℕ)
    (W : H →L[ℂ] H)
    (T : MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n →L[ℂ]
      MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n)
    (hword : ∀ (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
      (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
      W (U.inclusion n (tracialWordTensor G A D n d b a c ha hc)) =
        U.inclusion n (T (tracialWordTensor G A D n d b a c ha hc))) :
    W.comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp T := by
  apply DFunLike.coe_injective
  refine G.function_ext_tracialWordTensors (K := H) A D hτ n
    (fun z => W (U.inclusion n z)) (fun z => U.inclusion n (T z))
    (by fun_prop) (by fun_prop)
    (by intros; simp only [map_add]) (by intros; simp only [map_add])
    (by intros; simp only [map_smul]) (by intros; simp only [map_smul]) hword

include hA hD in
/-- Equality on the bounded algebra words extends the automorphism action to
its genuine completed-word intertwining identity. -/
theorem automorphism_level (hU : TracialWordFormula G A D U)
    (hτ : G.trace 1 = 1) (n : ℕ) :
    (G.automorphismUnitary θ hθ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap) := by
  refine intertwining_of_bounded_words hτ n
    (G.automorphismUnitary θ hθ).toContinuousLinearEquiv.toContinuousLinearMap
    (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap) ?_
  intro d b a c ha hc
  exact automorphism_word ι u θ hθ hA hD hU n d b a c ha hc

/-- The matrix action needed for finite-stage word classification is obtained
from the published factor extension, rather than supplied as tensor covariance. -/
theorem matrix_extension_level
    (hgen : G.FactorsTraciallyGenerate A D) (hfaithful : Function.Injective G.vector)
    (hext : G.MatrixConjugationExtensionInput D ι A)
    (hU : TracialWordFormula G A D U) (hτ : G.trace 1 = 1) (n : ℕ) :
    (G.matrixExtensionUnitaryRepresentation A D ι hgen hfaithful hext u : H →L[ℂ] H).comp
        (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp
        (hilbertTensorLift (G.baseMatrixWordAction D ι u n).toContinuousLinearMap) := by
  exact automorphism_level ι u
    (G.matrixExtensionAutomorphism A D ι hgen hfaithful hext u)
    (fun x => G.matrixExtensionAutomorphism_trace A D ι hgen hfaithful hext u x)
    (fun a => G.matrixExtensionAutomorphism_base A D ι hgen hfaithful hext u a)
    (fun d => G.matrixExtensionAutomorphism_other A D ι hgen hfaithful hext u d)
    hU hτ n

end TracialWordFormula
end KadisonSimilarity

end

end OAI
