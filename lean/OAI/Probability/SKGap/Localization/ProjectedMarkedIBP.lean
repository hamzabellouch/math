import Mathlib
import OAI.Probability.SKGap.Localization.MarkedProductIBP

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def markedError (r R : ℝ) (L K B C : NNReal) (D E p : ℝ) : ℝ :=
  B*R*C*p+B*C*(Fintype.card ι:ℝ)^2*sqrt (2*r)*sqrt p+
    (Fintype.card ι:ℝ)^2*(sqrt (2*r)*((L*C+B*K:NNReal)*
      (⟨sqrt (2*r),sqrt_nonneg _⟩*(Fintype.card (MatrixCoordinates ι):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)+
      r*(D*C+B*E))*p

theorem projected_marked_product_IBP {r R : ℝ} (hr : 0≤r) (hR : 0≤R)
    (U Q : Matrix ι ι ℝ→Matrix ι ι ℝ)
    (DU DQ : ι→ι→Matrix ι ι ℝ→Matrix ι ι ℝ)
    {L K B C : NNReal} {D E : ℝ}
    (hU : LipschitzWith L U) (hQ : LipschitzWith K Q)
    (hB : ∀ M,opNorm (U M)≤B) (hC : ∀ M,opNorm (Q M)≤C)
    (hDU : ∀ a b,Continuous (DU a b)) (hDQ : ∀ a b,Continuous (DQ a b))
    (hD : ∀ a b M,opNorm (DU a b M)≤D) (hE : ∀ a b M,opNorm (DQ a b M)≤E)
    {s : Set (MatrixCoordinates ι→ℝ)} (hs : MeasurableSet s)
    (hgood : ∀ g∈s,opNorm (goeMatrix r g)≤R)
    (hUd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>U (goeMatrix r g+t • symmetricElementary a b)) (DU a b (goeMatrix r g)) 0)
    (hQd : ∀ a b g,g∈s→HasDerivAt (fun t : ℝ=>Q (goeMatrix r g+t • symmetricElementary a b)) (DQ a b (goeMatrix r g)) 0)
    (i : ι) :
    let μ := Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1)
    |(∫ g,(U (goeMatrix r g)*realProject R hR (goeMatrix r g)*Q (goeMatrix r g)) i i ∂μ)-
      r*(∫ g,∑ a,∑ b,(DU a b (goeMatrix r g) i a*Q (goeMatrix r g) b i+
        U (goeMatrix r g) i a*DQ a b (goeMatrix r g) b i) ∂μ)|≤
      markedError (ι:=ι) r R L K B C D E (μ.real sᶜ) := by
  intro μ
  have h1 := projected_marked_expectation_error hr hR B.coe_nonneg C.coe_nonneg U Q
    hU.continuous hQ.continuous hB hC hs hgood i
  have h2 := goe_marked_product_IBP hr U Q DU DQ hU hQ hB hC hDU hDQ hD hE hs hUd hQd i
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)
end SKGap
end
end

end OAI
