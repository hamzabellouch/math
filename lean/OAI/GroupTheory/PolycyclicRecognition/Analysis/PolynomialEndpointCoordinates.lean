import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialFamilies
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialEndpointSchemes

namespace OAI

/-! # The actual generator endpoint schemes have uniformly bounded degree -/

noncomputable section

namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_sum {P I : Type*} {m n : ℕ}
    (s : Finset I) (f : I → P → (Fin m → ℝ) → (Fin n → ℝ))
    (hf : ∀ i ∈ s, HasPolynomialCoordinates (f i)) :
    HasPolynomialCoordinates (fun a x => ∑ i ∈ s, f i a x) := by
  intro l
  simpa only [Finset.sum_apply] using hasPolynomialFormula_sum s
    (fun i a x => f i a x l) (fun i hi => hf i hi l)

theorem hasPolynomialCoordinates_evalBilinearWord
    {P I : Type*} {m n : ℕ}
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → I → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun a x => X a x i)) (w : FreeMagma I) :
    HasPolynomialCoordinates (fun a x => evalBilinearWord (B a) (X a x) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul u v hu hv => exact hu.bilinear B hv

theorem hasPolynomialCoordinates_bilinearDynkin
    {P : Type*} {m n c l : ℕ} (a : DynkinCoefficients c l)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x => bilinearDynkinPolynomial a (B b) (X b x)) := by
  apply hasPolynomialCoordinates_sum
  intro d _
  apply hasPolynomialCoordinates_sum
  intro w _
  exact (hasPolynomialCoordinates_evalBilinearWord B X hX _).smul
    (hasPolynomialFormula_const (fun _ => a d w))

theorem hasPolynomialCoordinates_dynkinProduct
    {P : Type*} {m n c : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {f g : P → (Fin m → ℝ) → (Fin n → ℝ)}
    (hf : HasPolynomialCoordinates f) (hg : HasPolynomialCoordinates g) :
    HasPolynomialCoordinates (fun b x => dynkinProduct a (B b) (f b x) (g b x)) := by
  apply hasPolynomialCoordinates_bilinearDynkin a B (fun b x => ![f b x, g b x])
  intro i
  fin_cases i
  · exact hf
  · exact hg

theorem hasPolynomialCoordinates_polynomialWord
    {P I : Type*} {m n c : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → I → (Fin n → ℝ)) (w : List (I × ℝ)) :
    HasPolynomialCoordinates (fun b (_ : Fin m → ℝ) => polynomialWord (dynkinProduct a (B b)) (X b) w) :=
  hasPolynomialCoordinates_const _

theorem hasPolynomialCoordinates_listProduct
    {P : Type*} {m n c l : ℕ} (a : DynkinCoefficients c 2)
    (B : P → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (X : P → (Fin m → ℝ) → Fin l → (Fin n → ℝ))
    (hX : ∀ i, HasPolynomialCoordinates (fun b x => X b x i)) :
    HasPolynomialCoordinates (fun b x =>
      polynomialListProduct (dynkinProduct a (B b)) (List.ofFn (X b x))) := by
  induction l with
  | zero => simpa [polynomialListProduct] using
      hasPolynomialCoordinates_const (m := m) (fun _ : P => (0 : Fin n → ℝ))
  | succ l ih =>
    simp only [List.ofFn_succ, polynomialListProduct]
    exact hasPolynomialCoordinates_dynkinProduct a B (hX 0)
      (ih (fun b x i => X b x i.succ) (fun i => hX i.succ))

theorem hasPolynomialCoordinates_endpointScheme
    {I : Type*} {n m c : ℕ} (a : DynkinCoefficients c 2)
    (w : Fin m → List (I × ℝ)) (i : Fin m → I) :
    HasPolynomialCoordinates (fun p :
      ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ) =>
      fun t : Fin m → ℝ => polynomialEndpointScheme a w i p t) := by
  apply hasPolynomialCoordinates_listProduct a Prod.fst
  intro j
  apply hasPolynomialCoordinates_dynkinProduct a Prod.fst
  · apply hasPolynomialCoordinates_dynkinProduct a Prod.fst
    · exact hasPolynomialCoordinates_polynomialWord a Prod.fst Prod.snd (w j)
    · apply HasPolynomialCoordinates.smul
      · exact hasPolynomialCoordinates_const (fun p :
          ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × (I → Fin n → ℝ) =>
          p.2 (i j))
      · exact hasPolynomialFormula_coordinate j
  · exact hasPolynomialCoordinates_polynomialWord a Prod.fst Prod.snd (inverseGeneratorWord (w j))

end PolycyclicRecognition

end

end OAI
