import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialWordDensity

namespace OAI

/-! The represented left head action follows from the ordinary product
formula in the reduced-word model. It is not extra covariance data. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

local instance actionMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance actionMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

omit [IsClosed (D : Set P)] in
theorem baseRepresentation_baseVector (a b : D) :
    G.baseRepresentation D a (G.baseVector D b) = G.baseVector D (a * b) := by
  apply Subtype.ext
  exact G.left_vector (a : P) (b : P)

/-- Left multiplication acts only on the first other-factor endpoint. -/
def tracialWordHeadAction (n : ℕ) (a : D) :
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n →L[ℂ]
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n :=
  hilbertTensorLift (endpointHeadAction (G.baseRepresentation D a))

theorem tracialWordHeadAction_tensor (n : ℕ) (x d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    G.tracialWordHeadAction A D n x (tracialWordTensor G A D n d b a c ha hc) =
      tracialWordTensor G A D n (x * d) b a c ha hc := by
  simp only [tracialWordHeadAction, tracialWordTensor, tracialEndpointWord,
    hilbertTensorLift_insert, endpointWord, endpointHeadAction_insert,
    G.baseRepresentation_baseVector D]

end TracialCornerGeometry

namespace TracialWordFormula

attribute [local instance] TracialCornerGeometry.actionMultiplicityNormedFamily
  TracialCornerGeometry.actionMultiplicityInnerFamily

variable {G : TracialCornerGeometry P H} {A D : StarSubalgebra ℂ P}
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H}

/-- The actual represented left action intertwines with the completed head
action, by equality on the dense bounded word vectors. -/
theorem left_head (hU : TracialWordFormula G A D U) (hτ : G.trace 1 = 1)
    (n : ℕ) (x : D) :
    (G.left (x : P)).comp (U.inclusion n).toContinuousLinearMap =
      (U.inclusion n).toContinuousLinearMap.comp (G.tracialWordHeadAction A D n x) := by
  apply DFunLike.coe_injective
  refine G.function_ext_tracialWordTensors (K := H) A D hτ n
    (fun z => G.left (x : P) (U.inclusion n z))
    (fun z => U.inclusion n (G.tracialWordHeadAction A D n x z))
    (by fun_prop) (by fun_prop)
    (by intros; simp only [map_add]) (by intros; simp only [map_add])
    (by intros; simp only [map_smul]) (by intros; simp only [map_smul]) ?_
  intro d b a c ha hc
  rw [G.tracialWordHeadAction_tensor, hU, hU, G.left_vector]
  congr 1
  simp only [MulMemClass.coe_mul, mul_assoc]

end TracialWordFormula
end KadisonSimilarity

end

end OAI
