import OAI.Analysis.FreeEntropy.MatrixHeatLawMoments

namespace OAI

universe u1

noncomputable section
open MeasureTheory Finset Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem complex_integrable_re {Ω : Type u1} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => (f x).re) μ := hf.re
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀i,IsSelfAdjoint (X i))
variable {D : ℕ → ℕ} (ν : (k:ℕ) → Measure (MatrixCoordinates n (D k)))
  (hi : ∀k w,Integrable (fun a => matrixMoment a w) (ν k))
  (hip : ∀k v w,Integrable (fun a => matrixMoment a v*matrixMoment a w) (ν k))
  (ht : ∀w,Tendsto (fun k => ∫a,matrixMoment a w ∂ν k) atTop (𝓝 (wordMoment τ X w)))
  (htp : ∀v w,Tendsto (fun k => ∫a,matrixMoment a v*matrixMoment a w ∂ν k) atTop (𝓝 (wordMoment τ X v*wordMoment τ X w)))
 include hi in
 theorem matrixPolynomialNorm_integrable (k : ℕ) (p : WordPolynomial n) :
    Integrable (matrixPolynomialNorm p) (ν k) :=
  (integrable_finsetSum p.support (fun u _ => integrable_finsetSum p.support (fun v _ => (hi k (u.reverse++v)).const_mul (star (p u)*p v)))).re
 include hip in
 theorem matrixPolynomialDerivative_integrable (k : ℕ) (p : WordPolynomial n) (i : Fin n) :
    Integrable (matrixPolynomialDerivative p i) (ν k) := by
  apply integrable_finsetSum p.support
  intro w _
  apply Integrable.const_mul
  apply integrable_finsetSum univ
  intro r _
  by_cases h : w[r.val]=i
  · simpa only [h,ite_true] using hip k (w.take r.val) (w.drop (r.val+1))
  · simp only [h,ite_false]
    exact integrable_zero _ _ _
 include hi ht hX in
 theorem matrixPolynomialNorm_integral_tendsto (p : WordPolynomial n) :
    Tendsto (fun k => ∫a,matrixPolynomialNorm p a ∂ν k) atTop (𝓝 (‖polynomialVector τ X p‖^2)) := by
  have he k : (∫a,matrixPolynomialNorm p a ∂ν k) =
      (∑u∈p.support,∑v∈p.support,star (p u)*p v*(∫a,matrixMoment a (u.reverse++v) ∂ν k)).re := by
    simp only [matrixPolynomialNorm]
    rw [← complex_integral_re (integrable_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hi k _).const_mul _)))]
    rw [integral_finsetSum _ (fun u _ => integrable_finsetSum _ (fun v _ => (hi k _).const_mul _))]
    simp_rw [integral_finsetSum _ (fun v _ => (hi k _).const_mul _),integral_const_mul]
  simp_rw [he]
  rw [polynomialVector_norm_formula τ X hX]
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_finsetSum p.support (fun u _ => tendsto_finsetSum p.support (fun v _ => (ht _).const_mul _)))
 include hip htp in
 theorem matrixPolynomialDerivative_integral_tendsto (p : WordPolynomial n) (i : Fin n) :
    Tendsto (fun k => ∫a,matrixPolynomialDerivative p i a ∂ν k) atTop (𝓝 (polynomialDerivative τ X i p)) := by
  have hir (k : ℕ) (w : List (Fin n)) (r : Fin w.length) : Integrable (fun a : MatrixCoordinates n (D k) => if w[r.val]=i then matrixMoment a (w.take r.val)*matrixMoment a (w.drop (r.val+1)) else 0) (ν k) := by
    by_cases h : w[r.val]=i
    · simpa only [h,ite_true] using hip k (w.take r.val) (w.drop (r.val+1))
    · simp only [h,ite_false]; exact integrable_zero _ _ _
  have he k : (∫a,matrixPolynomialDerivative p i a ∂ν k) =
      ∑w∈p.support,p w*∑r : Fin w.length,if w[r.val]=i then (∫a,matrixMoment a (w.take r.val)*matrixMoment a (w.drop (r.val+1)) ∂ν k) else 0 := by
    simp only [matrixPolynomialDerivative]
    rw [integral_finsetSum _ (fun w _ => (integrable_finsetSum _ (fun r _ => hir k w r)).const_mul _)]
    apply sum_congr rfl
    intro w _
    rw [integral_const_mul,integral_finsetSum _ (fun r _ => hir k w r)]
    congr 1
    apply sum_congr rfl
    intro r _
    split_ifs <;> simp
  simp_rw [he]
  simp only [polynomialDerivative,Finsupp.linearCombination_apply,Finsupp.sum,smul_eq_mul,derivativeMoment]
  apply tendsto_finsetSum p.support
  intro w _
  apply Tendsto.const_mul
  apply tendsto_finsetSum univ
  intro r _
  split_ifs
  · exact htp _ _
  · exact tendsto_const_nhds
 include hi hip ht htp hX in
 theorem matrixFisherTest_integral_tendsto (p : WordPolynomial n) (i : Fin n) :
    Tendsto (fun k => ∫a,matrixFisherTest p i a ∂ν k) atTop (𝓝 (fisherTest τ X i p)) := by
  have he k : (∫a,matrixFisherTest p i a ∂ν k) =
      2*(∫a,matrixPolynomialDerivative p i a ∂ν k).re-∫a,matrixPolynomialNorm p a ∂ν k := by
    simp only [matrixFisherTest]
    rw [integral_sub ((complex_integrable_re (matrixPolynomialDerivative_integrable ν hip k p i)).const_mul 2) (matrixPolynomialNorm_integrable ν hi k p),integral_const_mul,← complex_integral_re (matrixPolynomialDerivative_integrable ν hip k p i)]
  simp_rw [he]
  exact ((Complex.continuous_re.continuousAt.tendsto.comp (matrixPolynomialDerivative_integral_tendsto τ X ν hip htp p i)).const_mul 2).sub
    (matrixPolynomialNorm_integral_tendsto τ X hX ν hi ht p)
end FiniteEntropySeparation

end

end OAI
