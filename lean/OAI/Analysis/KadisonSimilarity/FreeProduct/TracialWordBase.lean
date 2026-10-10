import OAI.Analysis.KadisonSimilarity.FreeProduct.ReducedWordModel

namespace OAI

/-! The vacuum endpoint in degree zero is the actual base Hilbert space.
Consequently the repeated-word action implies base-space invariance; this
is not an additional assumption on the symmetrized operator. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

theorem norm_baseVector_one (hτ : G.trace 1 = 1) : ‖G.baseVector D 1‖ = 1 :=
  norm_tracialTraceVector (G.baseGeometry D).trace (G.baseVector D)
    (G.baseVector_inner D) hτ

local instance baseMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance baseMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

variable (hτ : G.trace 1 = 1)
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)
  (hU : TracialWordFormula G A D U)

include hτ hU

/-- The empty-word formula identifies the abstract vacuum inclusion. -/
theorem tracial_baseWordInclusion_vector (b : A) :
    baseWordInclusion (G.baseVector A 1) U (G.baseVector D 1)
      (G.norm_baseVector_one D hτ) (G.baseVector A b) = G.vector (b : P) := by
  have ha : (fun i : Fin 0 => G.baseSymmetryLetter A (Fin.elim0 i) (Fin.elim0 i)) =
      (Fin.elim0 : Fin 0 → centeredSubspace (G.baseVector A 1)) := Subsingleton.elim _ _
  have hc : (fun i : Fin 0 => G.baseSymmetryLetter D (Fin.elim0 i) (Fin.elim0 i)) =
      (Fin.elim0 : Fin 0 → centeredSubspace (G.baseVector D 1)) := Subsingleton.elim _ _
  simpa only [baseWordInclusion_apply, zeroMultiplicityEquiv_apply,
    zeroMultiplicityWord, emptyEndpoint, tracialWordTensor, tracialMultiplicityWord,
    tracialEndpointWord, ha, hc, OneMemClass.coe_one, one_mul] using
      hU.zero_word_formula (1 : D) b

/-- Equality extends to the completed base space by density. -/
theorem tracial_baseWordInclusion_eq :
    baseWordInclusion (G.baseVector A 1) U (G.baseVector D 1)
      (G.norm_baseVector_one D hτ) = G.baseInclusion A :=
  baseWordInclusion_eq_baseInclusion (G.baseVector D 1) (G.norm_baseVector_one D hτ)
    G A U (G.tracial_baseWordInclusion_vector A D hτ U hU)

/-- A degree-zero repeated action gives invariance of the actual base space. -/
theorem baseSpace_invariant_of_word_action (Y : H →L[ℂ] H)
    (T : WordMultiplicity (G.baseVector A 1) 0 →L[ℂ]
      WordMultiplicity (G.baseVector A 1) 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) =
      U.inclusion 0 (hilbertTensorInsert (T v)
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) :
    ∀ x ∈ G.baseSpace A, Y x ∈ G.baseSpace A := by
  have hi := baseWordInclusion_intertwines (G.baseVector A 1) U (G.baseVector D 1)
    (G.norm_baseVector_one D hτ) Y T hY
  rw [G.tracial_baseWordInclusion_eq A D hτ U hU] at hi
  intro x hx
  have he := congrArg (fun f : G.baseSpace A →L[ℂ] H => f ⟨x, hx⟩) hi
  exact he.symm ▸ (zeroMultiplicityOperator (G.baseVector A 1) T ⟨x, hx⟩).property

/-- The same word action identifies its multiplicity-zero coefficient with
the actual compression used in the commutator estimate. -/
theorem baseOperator_of_word_action (Y : H →L[ℂ] H)
    (T : WordMultiplicity (G.baseVector A 1) 0 →L[ℂ]
      WordMultiplicity (G.baseVector A 1) 0)
    (hY : ∀ v, Y (U.inclusion 0 (hilbertTensorInsert v
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) =
      U.inclusion 0 (hilbertTensorInsert (T v)
        (emptyEndpoint (F := centeredSubspace (G.baseVector D 1)) (G.baseVector D 1)))) :
    G.baseOperator A Y = zeroMultiplicityOperator (G.baseVector A 1) T :=
  baseOperator_eq_zeroMultiplicityOperator (G.baseVector D 1) (G.norm_baseVector_one D hτ)
    G A U Y T (G.tracial_baseWordInclusion_vector A D hτ U hU) hY

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
