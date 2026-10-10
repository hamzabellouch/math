import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialDihedralColumns
import OAI.Analysis.KadisonSimilarity.FreeProduct.ReducedWordModel

namespace OAI

/-! The actual normalized dihedral columns agree with the repeated tensor
words on the dense bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

local instance dihedralMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance dihedralMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

variable
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)

/-- The repeated base insertion is the bounded-algebra multiplicity word. -/
theorem baseSymmetryRepeatedInclusion_baseVector (k : ℕ) (b : A) :
    G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k (G.baseVector A b) =
      tracialMultiplicityWord G A k b (fun _ => s) (fun _ => hs0) := rfl

/-- A constant-letter word has exactly the tensor coordinates of the
repeated base insertion and the unnormalized endpoint. -/
theorem repeated_dihedral_word_formula (hU : TracialWordFormula G A D U)
    (k : ℕ) (b : A) :
    U.inclusion k
      (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k (G.baseVector A b))
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))) =
      G.vector ((e : P) * ((s : P) * (d : P)) ^ k * (b : P)) := by
  exact hU.repeated_word_formula k e d s b hs0 hd0

attribute [local irreducible] tracialDihedralInclusion

/-- The two column realizations agree on all bounded algebra vectors. -/
theorem actual_dihedral_column_baseVector (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (k : ℕ) (b : A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte k (G.baseVector A b) =
      dihedralNormalization t • U.inclusion k (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k (G.baseVector A b))
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))) := by
  exact (G.tracialDihedralInclusion_apply D A hf hτ d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte k b).trans
      (congrArg (fun x : H => dihedralNormalization t • x)
        (G.repeated_dihedral_word_formula D A hτ d s e hd0 hsstar hssq hs0 U hU k b)).symm

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
