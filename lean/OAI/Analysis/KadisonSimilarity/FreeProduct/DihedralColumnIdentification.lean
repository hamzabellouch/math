import OAI.Analysis.KadisonSimilarity.FreeProduct.DihedralWordColumn

namespace OAI

/-! Identify the normalized actual dihedral columns with completed word maps. -/

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

attribute [local instance] dihedralMultiplicityNormedFamily dihedralMultiplicityInnerFamily

variable
  (U : OrthogonalWordLevels
    (MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1))) H)

attribute [local irreducible] tracialDihedralInclusion

/-- On every completed base vector, the actual normalized dihedral column
is the normalized repeated word supplied by the reduced-word model. -/
theorem actual_dihedral_column_apply (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (k : ℕ) (v : G.baseSpace A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte k v =
      dihedralNormalization t • U.inclusion k (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k v)
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))) := by
  have hword : Continuous (fun x : G.baseSpace A =>
      dihedralNormalization t • U.inclusion k (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k x)
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0)))) := by
    change Continuous (fun x : G.baseSpace A =>
      dihedralNormalization t • U.inclusion k
        (hilbertTensorRightInsert
          (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))
          (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k x)))
    exact continuous_const.smul ((U.inclusion k).continuous.comp
      ((hilbertTensorRightInsert
        (tracialEndpointWord G D k e (fun _ => d) (fun _ => hd0))).continuous.comp
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k).continuous))
  refine (G.baseVector_dense A).induction_on v
    (isClosed_eq
      (G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
        he ht hte k).continuous hword) ?_
  intro b
  exact G.actual_dihedral_column_baseVector D A hτ d s e hdstar hdsq hd0
    hsstar hssq hs0 he ht hte U hf hU k b

/-- The finite family used in Fourier compression has the same repeated-word
coordinates, with no independently assumed word isometries. -/
theorem actual_dihedral_columns_apply (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (N : ℕ) (i : Fin N) (v : G.baseSpace A) :
    G.tracialDihedralColumns D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte N i v =
      dihedralNormalization t • U.inclusion i.val (hilbertTensorInsert
        (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ i.val v)
        (tracialEndpointWord G D i.val e (fun _ => d) (fun _ => hd0))) := by
  exact G.actual_dihedral_column_apply D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
    he ht hte U hf hU i.val v

/-- The Fourier columns are exactly the normalized repeated-letter columns
used by propagation, with normalization derived from the projection trace. -/
theorem actual_dihedral_column_eq_repeated (hf : ScalarFree G.trace D A)
    (hU : TracialWordFormula G A D U) (k : ℕ) (v : G.baseSpace A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte k v =
    G.repeatedDihedralInclusion D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
      he ht hte U k v := by
  rw [G.actual_dihedral_column_apply D A hτ d s e hdstar hdsq hd0 hsstar hssq hs0
    he ht hte U hf hU k v]
  symm
  simp only [repeatedDihedralInclusion, repeatedWordInclusion_apply, projectionEndpoint]
  exact include_scaled_endpoint (U.inclusion k).toContinuousLinearMap
    (G.baseSymmetryRepeatedInclusion A s hs0 hsstar hssq hτ k v)
    (G.baseVector D e) (fun _ : Fin k => G.baseSymmetryLetter D d hd0)
    (dihedralNormalization t)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
