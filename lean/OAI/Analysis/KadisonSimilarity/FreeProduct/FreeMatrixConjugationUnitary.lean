import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeMatrixConjugation

namespace OAI

/-! Inverse matrix conjugations on the actual free word Hilbert space. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

attribute [local irreducible] baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : ReducedWordGenerated G A D)

theorem freeMatrixConjugationIsometry_inverse (x : H) :
    G.freeMatrixConjugationIsometry A D ι u⁻¹ hτ hf hgen
      (G.freeMatrixConjugationIsometry A D ι u hτ hf hgen x) = x := by
  let W := G.freeMatrixConjugationIsometry A D ι u hτ hf hgen
  let V := G.freeMatrixConjugationIsometry A D ι u⁻¹ hτ hf hgen
  let F : H →L[ℂ] H := V.toContinuousLinearMap.comp W.toContinuousLinearMap -
    ContinuousLinearMap.id ℂ H
  have hF : F = 0 := continuousLinearMap_eq_zero_of_total (G.freeWordFamily A D)
    (G.freeWordFamily_total A D hgen) F (by
      rintro ⟨n, p⟩
      let a : Fin n → A := fun i => (p.1.1 i).1
      let c : Fin n → D := fun i => (p.2.2 i).1
      have ha : ∀ i, G.trace (a i : P) = 0 := fun i => (p.1.1 i).2
      have hc : ∀ i, G.trace (c i : P) = 0 := fun i => (p.2.2 i).2
      have hW := G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen
        n p.2.1 p.1.2 a c ha hc
      have hV := G.freeMatrixConjugationIsometry_word A D ι u⁻¹ hτ hf hgen
        n (matrixConjugateLetter D ι u p.2.1) p.1.2 a
        (fun i => matrixConjugateLetter D ι u (c i)) ha
        (fun i => (G.trace_matrixConjugateLetter D ι u (c i)).trans (hc i))
      have hVW := (congrArg V hW).trans hV
      simp only [matrixConjugateLetter_inv] at hVW
      change V (W (G.freeWordFamily A D ⟨n, p⟩)) - G.freeWordFamily A D ⟨n, p⟩ = 0
      exact sub_eq_zero.mpr hVW)
  have hx := congrArg (fun T : H →L[ℂ] H => T x) hF
  change V (W x) - x = 0 at hx
  exact sub_eq_zero.mp hx

def freeMatrixConjugationUnitary : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (G.freeMatrixConjugationIsometry A D ι u hτ hf hgen)
    (fun x => ⟨G.freeMatrixConjugationIsometry A D ι u⁻¹ hτ hf hgen x, by
      simpa only [inv_inv] using
        G.freeMatrixConjugationIsometry_inverse A D ι u⁻¹ hτ hf hgen x⟩)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
