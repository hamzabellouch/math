import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianProductIntegral
import OAI.Probability.SKGap.Matrix.MatrixWordRegularity

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma goe_word_even_centered_moment {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0<j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ))
    (hFl : 0<F.length) {R : NNReal} (hR : 0<R)
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f)
    (i b : Fin n) (k : ℕ) :
    (∫ g : MatrixCoordinates (Fin n)→ℝ,
      |matrixFactorProduct F (goeMatrix (j/n) g) i b-
        ∫ h : MatrixCoordinates (Fin n)→ℝ,matrixFactorProduct F (goeMatrix (j/n) h) i b
          ∂Measure.pi (fun _=>gaussianReal 0 1)|^(2*k)
        ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤
      (2*((2*k).factorial:ℝ)*exp (π^2/8)) *
        (((F.length:ℝ)*(R:ℝ)^F.length)^2*(2*j))^k/(n:ℝ)^k := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hRr : (0:ℝ)<R := hR
  have hlr : (0:ℝ)<F.length := Nat.cast_pos.mpr hFl
  let L : NNReal := ((F.length:NNReal)*R^F.length)*⟨sqrt (2*(j/n)),sqrt_nonneg _⟩
  have hLp : 0<L := by change 0<((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*(j/n)); positivity
  have hh := gaussianProduct_abs_centered_moment (goe_word_entry_lipschitz F hF hL (j/n) i b) hLp (2*k)
  apply hh.trans_eq
  change (2*((2*k).factorial:ℝ)*exp (π^2/8)) *
    (((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*(j/n)))^(2*k) = _
  rw [pow_mul,mul_pow,sq_sqrt (by positivity : 0 ≤ 2*(j/n))]
  rw [show ((F.length:ℝ)*(R:ℝ)^F.length)^2*(2*(j/n))=
    (((F.length:ℝ)*(R:ℝ)^F.length)^2*(2*j))/(n:ℝ) by ring,div_pow]
  ring

lemma goe_word_trace_lip_scaled {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0≤j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ)) {R : NNReal}
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    LipschitzWith ⟨((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ),by positivity⟩
      (fun z : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
        trace (matrixFactorProduct F (goeMatrix (j/n) z))/(n:ℝ)) := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have he : (n:ℝ)⁻¹*(sqrt (n:ℝ)*((F.length:ℝ)*(R:ℝ)^F.length))*sqrt (2*(j/n))=
      ((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ) := by
    rw [show 2*(j/(n:ℝ))=(2*j)/(n:ℝ) by ring,sqrt_div (mul_nonneg (by norm_num) hj)]
    field_simp [ne_of_gt hnr,ne_of_gt (sqrt_pos.2 hnr)]
  have hh := goe_word_normalized_trace_lipschitz F hF hL (j/n)
  simpa only [Fintype.card_fin,show (⟨(n:ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg n)⟩ *
      (⟨sqrt (n:ℝ),sqrt_nonneg _⟩*((F.length:NNReal)*R^F.length))*⟨sqrt (2*(j/n)),sqrt_nonneg _⟩ : NNReal)=
      ⟨((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ),by positivity⟩ from NNReal.eq he] using hh

theorem goe_word_trace_centered_L1 {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0<j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ))
    (hFl : 0<F.length) {R : NNReal} (hR : 0<R)
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    (∫ g : MatrixCoordinates (Fin n)→ℝ,
      |trace (matrixFactorProduct F (goeMatrix (j/n) g))/(n:ℝ)-
        ∫ h : MatrixCoordinates (Fin n)→ℝ,trace (matrixFactorProduct F (goeMatrix (j/n) h))/(n:ℝ)
          ∂Measure.pi (fun _=>gaussianReal 0 1)|
        ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ) := by
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hRr : (0:ℝ)<R := hR
  have hlr : (0:ℝ)<F.length := Nat.cast_pos.mpr hFl
  have hh := gaussianProduct_centered_L1 (goe_word_trace_lip_scaled hn hj.le F hF hL)
    (by change 0<((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ); positivity)
  apply hh.trans_eq
  change (2*exp (π^2/8))*(((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ))=_
  ring

lemma goe_word_trace_centered_L1_all {n : ℕ} (hn : 0<n) {j : ℝ} (hj : 0<j)
    (F : List (Matrix (Fin n) (Fin n) ℝ→Matrix (Fin n) (Fin n) ℝ))
    {R : NNReal} (hR : 0<R)
    (hF : ∀ f∈F,∀ M,opNorm (f M) ≤ R) (hL : ∀ f∈F,LipschitzWith R f) :
    (∫ g : MatrixCoordinates (Fin n)→ℝ,
      |trace (matrixFactorProduct F (goeMatrix (j/n) g))/(n:ℝ)-
        ∫ h : MatrixCoordinates (Fin n)→ℝ,trace (matrixFactorProduct F (goeMatrix (j/n) h))/(n:ℝ)
          ∂Measure.pi (fun _=>gaussianReal 0 1)|
        ∂Measure.pi (fun _=>gaussianReal 0 1)) ≤
      (2*exp (π^2/8))*((F.length:ℝ)*(R:ℝ)^F.length)*sqrt (2*j)/(n:ℝ) := by
  by_cases he : F=[]
  · subst F
    simp only [matrixFactorProduct_nil,List.length_nil,Nat.cast_zero,zero_mul,mul_zero,zero_div]
    simp
  · exact goe_word_trace_centered_L1 hn hj F (List.length_pos_iff.mpr he) hR hF hL
end SKGap
end
end

end OAI
