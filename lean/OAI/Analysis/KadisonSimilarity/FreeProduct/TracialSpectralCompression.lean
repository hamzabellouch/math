import OAI.Analysis.KadisonSimilarity.FreeProduct.SpectralArc
import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialArcCompression
import OAI.Analysis.KadisonSimilarity.FreeProduct.SymmetryWordAlgebra

namespace OAI

/-! The actual spectral-arc compression matrix. The normalized corner
expectation and the shifted reflection moment are derived here, leaving no
operator-valued Fourier identity among the hypotheses. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem spectral_arc_compression
    (A C D S : StarSubalgebra ℂ P)
    (E : TracialExpectation G.trace A) (EC : TracialExpectation G.trace C)
    (hCS : C ≤ S) (hDS : D ≤ S)
    (hf : Function.Injective G.vector) (hτ : G.trace 1 = 1)
    (hfreeDA : ScalarFree G.trace D A)
    (w d : Pˣ) (hw : star w = w⁻¹) (hd : d * w = w⁻¹ * d)
    (hdC : (d : P) ∈ C)
    (hsA : (↑(w⁻¹ * d) : P) ∈ A) (hsC : (↑(w⁻¹ * d) : P) ∈ C)
    (hs0 : G.trace (↑(w⁻¹ * d) : P) = 0)
    (hs2 : (↑(w⁻¹ * d) : P) * (↑(w⁻¹ * d) : P) = 1)
    (hsstar : star (↑(w⁻¹ * d) : P) = (↑(w⁻¹ * d) : P))
    (hdense : ∀ x, x ∈ S → G.vector x ∈ (Submodule.span ℂ
      (G.vector '' (StarAlgebra.adjoin ℂ ((D : Set P) ∪ {(↑(w⁻¹ * d) : P)}):
        Set P))).topologicalClosure)
    (hpower : ∀ j : ℤ, (↑(w ^ j) : P) ∈ C)
    (hp : IsStarProjection (dihedralHalfProjection d))
    (hpD : dihedralHalfProjection d ∈ D)
    (htp : G.trace (dihedralHalfProjection d) = (1 / 2 : ℂ))
    (hfree : ScalarFree (CStarCorner.normalizedTrace (dihedralHalfProjection d) hp G.trace)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp D hpD)
      (CStarCorner.subalgebra (dihedralHalfProjection d) hp C
        (C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2))))
    (e : CStarCorner (dihedralHalfProjection d) hp)
    (he : IsStarProjection (e : P)) (heD : (e : P) ∈ D)
    {N : ℕ} (hN : 0 < N)
    (F : DihedralSpectralArc G.trace C w d (arcWidth N))
    (t : ℝ) (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))
    (c : ℂ) (hc : star c * c = (t : ℂ)⁻¹)
    (U : Fin N → G.baseSpace A →L[ℂ] H)
    (hU : ∀ i (a : A), U i (G.baseVector A a) =
      c • G.vector ((e : P) * (↑(w ^ (-(i.val : ℤ))) : P) * (a : P))) :
    (sumColumns U).adjoint.comp
      ((G.left ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))).comp
        (sumColumns U)) =
      ((2 * t : ℝ) : ℂ) • matrixOperator (fun i j =>
        (realArcFourierCoefficient (arcWidth N) ((i.val : ℤ) - (j.val : ℤ)) : ℂ) •
          ContinuousLinearMap.id ℂ (G.baseSpace A) +
        (arcHankelMatrix N i j : ℂ) • G.baseCompression A (↑(w⁻¹ * d) : P)) := by
  have hpC : dihedralHalfProjection d ∈ C :=
    C.smul_mem (C.add_mem C.one_mem hdC) (1 / 2)
  have hspan := G.expectation_span_of_generated_symmetry_algebra A D S E hf hτ hfreeDA
    (↑(w⁻¹ * d) : P) hsA hs0 hs2 hsstar hdense
  have hwidth : arcWidth N ≤ Real.pi := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsmall : arcWidth N ≤ 1 := by
      unfold arcWidth
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]
  have heh : (e : P) * ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) =
      (e : P) * (F.element * dihedralHalfProjection d) * (e : P) := by
    simp only [← mul_assoc, he.isIdempotentElem.eq]
  have hhe : ((e : P) * (F.element * dihedralHalfProjection d) * (e : P)) * (e : P) =
      (e : P) * (F.element * dihedralHalfProjection d) * (e : P) := by
    rw [mul_assoc, he.isIdempotentElem.eq]
  exact G.arc_compression_of_scalar_moments A E EC hCS hf hτ w d hw hd hsA hsC hs0 hs2
    hspan hpower (e : P) F.element
    ((e : P) * (F.element * dihedralHalfProjection d) * (e : P))
    he.isSelfAdjoint.star_eq heh hhe F.mem
    (S.mul_mem (S.mul_mem (hDS heD) (hCS (C.mul_mem F.mem hpC))) (hDS heD))
    hN t ht c hc U hU
    (F.compressed_expectation EC (G.trace_faithful hf) G.tracial hp hpC D hpD htp
      hfree e heD hdC hte (arcWidth_pos hN).le hwidth)
    F.rotation_commutes F.rotation_moment (F.shifted_reflection_moment G.tracial)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
