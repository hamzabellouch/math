import OAI.NumberTheory.PiExponent.Geometry.CurveCenters
import OAI.NumberTheory.PiExponent.Geometry.WeightedCurveRigidity

namespace OAI

noncomputable section
namespace PiExponent.CurveFieldRigidity

open scoped BigOperators
open PiExponentApprox PersistentWeightComparison CurveCenters CurveValuationCenter

variable {E : Type*} [Field E] [Algebra ℂ E]

def coordinateKernel {n : ℕ} (x : Fin n → E) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.aeval x).toRingHom

instance coordinateKernel_isPrime {n : ℕ} (x : Fin n → E) : (coordinateKernel x).IsPrime :=
  RingHom.ker_isPrime _

@[simp] theorem mem_coordinateKernel {n : ℕ} (x : Fin n → E)
    (p : MvPolynomial (Fin n) ℂ) : p ∈ coordinateKernel x ↔ MvPolynomial.aeval x p = 0 :=
  Iff.rfl

theorem logarithmic_coordinate_eq_one {m : ℕ}
    (x : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (ha : a 0 = 1)
    (p : NormalizedPlace ℂ E) (hp : Centered x a p)
    (hheight : (coordinateKernel x).height ≤ m)
    (rho : Fin (m+1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m+1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m+1) cost (sigma / ((m : ℝ)+2)) N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (hvanish : ∀ word : List (Fin (m+1)), frameWordCost cost word ≤ sigma*N →
      MvPolynomial.aeval x (polynomialFrameWord m word F) = 0)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    x 0 = 1 := by
  have hx0 : x 0 ≠ 0 := by
    intro hz
    have hc := hp.constant_coordinate 0 0 (by simpa using hz)
    rw [ha] at hc
    exact zero_ne_one hc
  have hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel x := by
    simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hx0
  have hepsilon : 0 < sigma / ((m : ℝ)+2) := by positivity
  have hbound : ((m : ℝ)+2) * ((sigma / ((m : ℝ)+2))*N) = sigma*N := by
    have hm : (m : ℝ)+2 ≠ 0 := by positivity
    field_simp
  obtain ⟨c, hc⟩ := CurveComponentRigidity.coordinate_constant_of_persistent_comparison
    (fun i => (rho i : ℝ)) cost (comparisonConstant m sigma)
    ((sigma / ((m : ℝ)+2))*N) (fun i => (hcost i).le) (by positivity)
    F hF0 (coordinateKernel x) inferInstance hheight hY
    (fun word hword => hvanish word (by simpa only [hbound] using hword))
    (logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma hN hrect
      F hF (coordinateKernel x) hY) hseparated
  have hxc : x 0 = algebraMap ℂ E c := by
    simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hc
  have hc1 := hp.constant_coordinate 0 c hxc
  rw [ha] at hc1
  simpa only [hc1, map_one] using hxc

theorem ordinary_coordinate_constant {m n : ℕ} (hn : n ≤ m+2)
    (x : Fin n → E) (d : ℕ) (hd : d ≤ m)
    (hheight : (coordinateKernel x).height ≤ d)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles n cost (sigma / ((m : ℝ)+2)) N)
    (F : OrdinaryDerivatives.Polynomial n) (hF0 : F ≠ 0)
    (hF : WeightedSliceDegree.SupportBound (fun i => (rho i : ℝ)) N F)
    (hvanish : ∀ word : List (Fin n), DerivativeIdeals.wordCost cost word ≤ sigma*N →
      MvPolynomial.aeval x (OrdinaryDerivatives.word n word F) = 0)
    (hseparated : ∀ A B : Finset (Fin n), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, cost j) < ∏ j ∈ A, (rho j : ℝ)) :
    ∃ i : Fin n, ∃ c : ℂ, x i = algebraMap ℂ E c := by
  obtain ⟨i,c,hc⟩ := WeightedCurveRigidity.ordinary_coordinate_constant hn
    rho hrho cost hcost sigma N hsigma hN hrect F hF0 hF d hd
    (coordinateKernel x) inferInstance hheight hvanish hseparated
  refine ⟨i,c,?_⟩
  simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, sub_eq_zero] using hc

theorem fibre_generates {m : ℕ} (x : Fin m → E)
    (hx : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases (1 : E) x : Fin (m+1) → E)) = ⊤) :
    IntermediateField.adjoin ℂ (Set.range x) = ⊤ := by
  apply top_unique
  rw [← hx]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  cases i using Fin.cases with
  | zero => exact one_mem _
  | succ i => exact IntermediateField.subset_adjoin ℂ _ ⟨i,rfl⟩

end PiExponent.CurveFieldRigidity
end

end OAI
