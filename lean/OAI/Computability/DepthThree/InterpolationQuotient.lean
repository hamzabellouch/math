import OAI.Computability.DepthThree.AlgebraQuotient
import OAI.Computability.DepthThree.InterpolationSigns

namespace OAI

universe uDepth1 uDepth2

noncomputable section

namespace DepthThreeLowerBound
namespace Interpolation

open BinaryAlgebra

def coefficientEncoding {r : ℕ} (p : Fin r → F2) (t : ℕ) :
    (Fin t → Fin r → Bool) ≃ (Fin t → InputQuotient p) :=
  Equiv.piCongrRight (fun _ =>
    (bitsEquivF2 (Fin r)).trans (coordinates p).toEquiv.symm)

@[simp] theorem coefficientEncoding_apply {r t : ℕ} (p : Fin r → F2)
    (β : Fin t → Fin r → Bool) (j : Fin t) :
    coefficientEncoding p t β j = encode p (fun i => bitValue (β j i)) := rfl

theorem finiteAvg_coefficientEncoding {r t : ℕ} (p : Fin r → F2)
    (Φ : (Fin t → InputQuotient p) → ℝ) :
    finiteAvg (fun β : Fin t → Fin r → Bool =>
      Φ (fun j => encode p (fun i => bitValue (β j i)))) = finiteAvg Φ :=
  finiteAvg_equiv (coefficientEncoding p t) Φ

theorem finiteAvg_degreeZero {r : ℕ} (p : Fin r → F2) (hr : 0 < r)
    (Φ : F2 → ℝ) :
    finiteAvg (fun z : InputQuotient p => Φ (degreeZero (inputPolynomial_monic p) z)) =
      finiteAvg Φ := by
  classical
  exact AlgebraFiniteFibers.finiteAvg_comp
    (degreeZero (inputPolynomial_monic p)).toAddMonoidHom
    (degreeZero_surjective (inputPolynomial_monic p)
      (by simpa only [inputPolynomial_natDegree] using hr)) Φ

section Irreducible

variable {r t : ℕ} (p : Fin r → F2)
variable [Fact (Irreducible (inputPolynomial p))]
variable (hr : 0 < r)
variable {ι : Type uDepth1} [Fintype ι] [DecidableEq ι]
variable (a : ι → InputQuotient p) (hsize : Fintype.card ι ≤ t)
variable (ha : Function.Injective a)

include hr hsize ha

theorem finiteAvg_quotient_acceptEval (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → InputQuotient p =>
      Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a β)) = finiteAvg Φ := by
  exact finiteAvg_acceptEval (degreeZero (inputPolynomial_monic p))
    (degreeZero_one (inputPolynomial_monic p)
      (by simpa only [inputPolynomial_natDegree] using hr)) a hsize ha Φ

theorem finiteAvg_encoded_acceptEval (Φ : (ι → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → Fin r → Bool =>
      Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a
        (fun j => encode p (fun i => bitValue (β j i))))) = finiteAvg Φ := by
  calc
    finiteAvg (fun β : Fin t → Fin r → Bool =>
        Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a
          (fun j => encode p (fun i => bitValue (β j i))))) =
        finiteAvg (fun β : Fin t → InputQuotient p =>
          Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a β)) :=
      finiteAvg_coefficientEncoding p
        (fun β : Fin t → InputQuotient p =>
          Φ (acceptEval (degreeZero (inputPolynomial_monic p)) t a β))
    _ = finiteAvg Φ := finiteAvg_quotient_acceptEval p hr a hsize ha Φ

end Irreducible

theorem finiteAvg_encoded_acceptEval_finset {r t : ℕ} (p : Fin r → F2)
    [Fact (Irreducible (inputPolynomial p))] (hr : 0 < r) {Z : Type uDepth2} [DecidableEq Z]
    (a : Z → InputQuotient p) (s : Finset Z) (hsize : s.card ≤ t)
    (ha : Set.InjOn a (↑s : Set Z)) (Φ : (s → Bool) → ℝ) :
    finiteAvg (fun β : Fin t → Fin r → Bool =>
      Φ (fun z : s => acceptEval (degreeZero (inputPolynomial_monic p)) t a
        (fun j => encode p (fun i => bitValue (β j i))) z)) = finiteAvg Φ := by
  classical
  apply finiteAvg_encoded_acceptEval p hr (fun z : s => a z)
    (by simpa only [Fintype.card_coe] using hsize)
  intro x y hxy
  exact Subtype.ext (ha x.property y.property hxy)

end Interpolation
end DepthThreeLowerBound

end

end OAI
