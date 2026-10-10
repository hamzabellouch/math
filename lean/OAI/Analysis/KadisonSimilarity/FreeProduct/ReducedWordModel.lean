import OAI.Analysis.KadisonSimilarity.FreeProduct.BaseSymmetry
import OAI.Analysis.KadisonSimilarity.FreeProduct.WordBaseCoordinates
import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeExpectation

namespace OAI

/-! The reduced-word part of the published free-product construction.

Ricard–Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2–3 of
arXiv:math/0505302, constructs the reduced free-product Hilbert space as the
orthogonal sum of alternating centered tensor words. Regrouping the first
and last factors gives the coordinates below. The input is only this word
construction, without any operator invariance or commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite alternating product, in its prescribed left-to-right order. -/
def alternatingProduct {n : ℕ} (a b : Fin n → P) : P :=
  (List.ofFn (fun i => a i * b i)).prod

@[simp] theorem alternatingProduct_zero (a b : Fin 0 → P) :
    alternatingProduct a b = 1 := by simp [alternatingProduct]

theorem alternatingProduct_constant (a b : P) (n : ℕ) :
    alternatingProduct (fun _ : Fin n => a) (fun _ => b) = (a * b) ^ n := by
  simp [alternatingProduct, List.ofFn_const]

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

/-- The actual alternating vectors whose span is dense in a reduced product. -/
def reducedWordVectors : Set H := {x | ∃ (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D),
    (∀ i, G.trace (a i : P) = 0) ∧ (∀ i, G.trace (c i : P) = 0) ∧
      x = G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P))}

/-- Being generated in the tracial Hilbert space is a density hypothesis,
not an operator conclusion. -/
def ReducedWordGenerated : Prop :=
  (Submodule.span ℂ (reducedWordVectors G A D)).topologicalClosure = ⊤

/-- The base-algebra part of an elementary word. -/
def tracialMultiplicityWord (n : ℕ) (b : A) (a : Fin n → A)
    (ha : ∀ i, G.trace (a i : P) = 0) : WordMultiplicity (G.baseVector A 1) n :=
  hilbertTensorInsert (completedTensorWord (fun i => G.baseSymmetryLetter A (a i) (ha i)))
    (G.baseVector A b)

/-- The other-factor endpoint and centered internal letters. -/
def tracialEndpointWord (n : ℕ) (d : D) (c : Fin n → D)
    (hc : ∀ i, G.trace (c i : P) = 0) :
    EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n :=
  endpointWord (G.baseVector D d) (fun i => G.baseSymmetryLetter D (c i) (hc i))

/-- The tensor product of the base-word and endpoint factors. -/
def tracialWordTensor (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n :=
  hilbertTensorInsert (tracialMultiplicityWord G A n b a ha) (tracialEndpointWord G D n d c hc)

/-- Regrouped ordinary free-product words. The multiplicity space and the
endpoint space are fixed concrete tensor products of the two base spaces. -/
def TracialWordFormula (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H) : Prop :=
  ∀ (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0),
    U.inclusion n (tracialWordTensor G A D n d b a c ha hc) =
      G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P))

/-- Published input: the alternating centered tensor model for a normalized
faithful tracial reduced product. Its only output is the word coordinates. -/
def RicardXuWordDecompositionInput : Prop :=
  G.trace 1 = 1 → Function.Injective G.vector → ScalarFree G.trace D A →
    ReducedWordGenerated G A D → ∃ U : OrthogonalWordLevels
      (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
        (centeredSubspace (G.baseVector D 1))) H, TracialWordFormula G A D U

namespace TracialWordFormula

variable {G A D}
  {U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H}
  (hU : TracialWordFormula G A D U)

include hU

/-- Constant centered letters recover the exact repeated-word formula. -/
theorem repeated_word_formula (n : ℕ) (d₀ d : D) (a b : A)
    (ha : G.trace (a : P) = 0) (hd : G.trace (d : P) = 0) :
    U.inclusion n (tracialWordTensor G A D n d₀ b
      (fun _ => a) (fun _ => d) (fun _ => ha) (fun _ => hd)) =
      G.vector ((d₀ : P) * ((a : P) * (d : P)) ^ n * (b : P)) := by
  simpa only [alternatingProduct_constant] using
    hU n d₀ b (fun _ => a) (fun _ => d) (fun _ => ha) (fun _ => hd)

/-- Degree zero is the actual product of a head vector and a base vector. -/
theorem zero_word_formula (d : D) (b : A) :
    U.inclusion 0 (tracialWordTensor G A D 0 d b Fin.elim0 Fin.elim0
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)) =
      G.vector ((d : P) * (b : P)) := by
  simpa only [alternatingProduct_zero, mul_one] using
    hU 0 d b Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

end TracialWordFormula
end KadisonSimilarity

end

end OAI
