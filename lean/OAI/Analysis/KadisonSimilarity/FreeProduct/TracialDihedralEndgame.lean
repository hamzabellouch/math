import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralColumnIdentification

namespace OAI

/-! The Fourier matrix computed on the actual dihedral columns is the same
matrix tested by the repeated-word propagation estimate. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

attribute [local instance] dihedralMultiplicityNormedFamily dihedralMultiplicityInnerFamily

/-- The exact Fourier compression of the actual normalized columns, together
with the derived multiplicity propagation bounds, controls the base symmetry. -/
theorem commutator_bound_of_actual_dihedral_compression
    (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
    (d : D) (s : A) (e : D)
    (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
    (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
    (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (U : OrthogonalWordLevels
      (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
        (centeredSubspace (G.baseVector D 1))) H)
    (hU : TracialWordFormula G A D U)
    (Y T : H →L[ℂ] H)
    (B : ∀ n, WordMultiplicity (G.baseVector A 1) n →L[ℂ]
      WordMultiplicity (G.baseVector A 1) n)
    (hY : ∀ n v d' r, Y (U.inclusion n
        (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert (B n v) (endpointWord d' (fun _ : Fin n => r))))
    (hYstar : ∀ n v d' r, Y.adjoint (U.inclusion n
        (hilbertTensorInsert v (endpointWord d' (fun _ : Fin n => r)))) =
      U.inclusion n (hilbertTensorInsert ((B n).adjoint v)
        (endpointWord d' (fun _ : Fin n => r))))
    (hlevel : ∀ n x, Y (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    (hlevelstar : ∀ n x, Y.adjoint (U.inclusion n x) ∈ (U.inclusion n).toLinearMap.range)
    {N : ℕ} (hN : 0 < N) (toeplitz : Matrix (Fin N) (Fin N) ℝ)
    {u ε c₀ : ℝ} (hu : 0 < u) (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hT : ‖T‖ ≤ 3 * u) (hcomm : ‖commutator Y T‖ ≤ ε * ‖T‖)
    (hprop : ∀ n v,
      ‖B n (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
        G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
          (G.baseOperator A Y v)‖ ≤ 2 * c₀ * ε * ‖v‖)
    (hpropstar : ∀ n v,
      ‖(B n).adjoint (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n v) -
        G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ n
          ((G.baseOperator A Y).adjoint v)‖ ≤ 2 * c₀ * ε * ‖v‖)
    (hfourier :
      let V := G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte N
      (sumColumns V).adjoint.comp (T.comp (sumColumns V)) =
        (u : ℂ) • matrixOperator (fun i j =>
          (toeplitz i j : ℂ) • ContinuousLinearMap.id ℂ (G.baseSpace A) +
            (arcHankelMatrix N i j : ℂ) • G.baseRepresentation A s)) :
    ‖commutator (G.baseOperator A Y) (G.baseRepresentation A s)‖ ≤
      6 * Real.pi ^ 2 * (1 + 4 * c₀) * ε := by
  apply free_corner_from_multiplicity_propagation U hN
    (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ)
    (G.projectionEndpoint D e t) (G.baseSymmetryLetter D d hd0)
    (G.norm_projectionEndpoint D e he ht hte)
    (G.norm_baseSymmetryLetter D d hd0 hdstar hdsq hτ)
    Y T (G.baseOperator A Y) (G.baseRepresentation A s) B
    (fun n v => hY n v _ _) (fun n v => hYstar n v _ _)
    hlevel hlevelstar toeplitz hu hε hc₀ hT hcomm hprop hpropstar
  have hV : G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N = fun i =>
        (G.repeatedDihedralInclusion D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
          he ht hte U i.val).toContinuousLinearMap := by
    funext i
    ext v
    exact G.actual_dihedral_column_eq_repeated D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte U hf hU i.val v
  dsimp only at hfourier
  rw [hV] at hfourier
  exact hfourier

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
