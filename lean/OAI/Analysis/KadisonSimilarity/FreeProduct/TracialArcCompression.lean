import OAI.Analysis.KadisonSimilarity.FreeProduct.ArcCompression
import OAI.Analysis.KadisonSimilarity.FreeProduct.SymmetryExpectation
import OAI.Analysis.KadisonSimilarity.Tracial.TracialCornerExpectations

namespace OAI

/-! The finite Fourier matrix with the actual base compression and actual
trace-pairing expectations. Only scalar moments of the arc remain as data. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- Scalar Fourier moments and the expectation range on the tested word
algebra determine the finite operator matrix on the actual tracial base. -/
theorem arc_compression_of_scalar_moments
    (E : TracialExpectation G.trace A) {C S : StarSubalgebra ℂ P}
    (EC : TracialExpectation G.trace C) (hCS : C ≤ S)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
    (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
    (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
    (hspan : ∀ x, x ∈ S → ∃ α β : ℂ,
      E.map x = α • (1 : P) + β • (↑(w⁻¹ * d) : P))
    (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
    (e f h : P) (hestar : star e = e) (heh : e * h = h) (hhe : h * e = h)
    (hfC : f ∈ C) (hhS : h ∈ S)
    {N : ℕ} (hN : 0 < N) (t : ℝ) (ht : 0 < t) (c : ℂ)
    (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → G.baseSpace A →L[ℂ] H)
    (hU : ∀ i (a : A), U i (G.baseVector A a) =
      c • G.vector (e * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P)))
    (hEC : EC.map h = (2 * (t : ℂ)) ^ 2 • (f * dihedralHalfProjection d))
    (hcomm : ∀ j : ℤ, (↑(w ^ j) : P) * f = f * (↑(w ^ j) : P))
    (hcoef : ∀ l : ℤ, G.trace (f * (↑(w ^ l) : P)) =
      arcFourierIntegral (arcWidth N) l)
    (hcoset : ∀ l : ℤ,
      G.trace ((↑(w⁻¹ * d) : P) * (f * (↑(w ^ l) : P))) = 0) :
    (sumColumns U).adjoint.comp ((G.left h).comp (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P)) := by
  have hfaithful := G.trace_faithful hf
  have hrotref (l : ℤ) := E.rotation_reflection_of_scalar_moments hτ G.tracial
    (↑(w⁻¹ * d) : P) hsA hs0 hs2 (f * (↑(w ^ l) : P))
    (arcFourierIntegral (arcWidth N) l) (hcoef l) (hcoset l)
    (hspan _ (hCS (C.mul_mem hfC (hpower l))))
    (hspan _ (hCS (C.mul_mem (C.mul_mem hfC (hpower l)) hsC)))
  apply narrow_arc_tracial_compression hN A G.trace G.vector G.left.toLinearMap
    G.inner_vector G.left_vector (G.baseVector A) (G.baseVector_dense A)
    (G.baseCompression A) (G.baseCompression_inner A) (G.baseCompression_one A)
    E.map EC.map E.trace_map (fun a b x => E.bimodule hfaithful G.tracial
      (a : P) (b : P) x a.property b.property)
    w d hw hd e f h hestar heh hhe t ht c hc U hU hEC
  · intro j k
    exact EC.bimodule hfaithful G.tracial _ _ h (hpower j) (hpower (-k))
  · intro j k
    exact E.restricted_tower_of_symmetry_span EC hCS hτ _ hsA hsC hs0 hs2 hspan _
      (S.mul_mem (S.mul_mem (hCS (hpower j)) hhS) (hCS (hpower (-k))))
  · exact hcomm
  · exact fun l => (hrotref l).1
  · exact fun l => (hrotref l).2

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
