import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingProductSubmersion

namespace OAI

/-! # Polynomial and smooth coordinates for the alternating product

These coordinates keep the two embedding maps among the coefficient
parameters. The input chart can be any fixed continuous linear equivalence.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

theorem hasPolynomialCoordinates_linear {P : Type*} {m n : ℕ}
    (L : P → (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) :
    HasPolynomialCoordinates (fun p x => L p x) := by
  have he (p : P) (x : Fin m → ℝ) :
      L p x = ∑ i, x i • L p (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  intro j
  have hj : (fun p x => L p x j) =
      (fun p x => ∑ i, x i * L p (Pi.single i 1) j) := by
    funext p x
    rw [he p x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hj]
  apply hasPolynomialFormula_sum
  intro i _
  exact (hasPolynomialFormula_coordinate i).mul
    (hasPolynomialFormula_const (fun p => L p (Pi.single i 1) j))

abbrev AlternatingLawData (n : ℕ) :=
  ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) ×
    (((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) × ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))

def flatAlternatingProduct {m n h c : ℕ} (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (p : AlternatingLawData n) (x : Fin m → ℝ) : Fin n → ℝ :=
  alternatingCoordinateProduct a p.1 p.2.1 p.2.2 (e x)

theorem hasPolynomialCoordinates_flatAlternatingProduct {m n h c : ℕ}
    (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ))) :
    HasPolynomialCoordinates (flatAlternatingProduct a e) := by
  unfold flatAlternatingProduct alternatingCoordinateProduct
  apply hasPolynomialCoordinates_listProduct a (fun p : AlternatingLawData n => p.1)
  intro j
  apply hasPolynomialCoordinates_dynkinProduct a (fun p : AlternatingLawData n => p.1)
  · exact hasPolynomialCoordinates_linear (fun p : AlternatingLawData n =>
      p.2.1.comp ((ContinuousLinearMap.fst ℝ _ _).comp
        ((ContinuousLinearMap.proj j).comp e.toContinuousLinearMap)))
  · exact hasPolynomialCoordinates_linear (fun p : AlternatingLawData n =>
      p.2.2.comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.proj j).comp e.toContinuousLinearMap)))

theorem contDiff_flatAlternatingProduct {m n h c : ℕ} {q : ℕ∞}
    (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ))) :
    ContDiff ℝ q (fun z : AlternatingLawData n × (Fin m → ℝ) =>
      flatAlternatingProduct a e z.1 z.2) := by
  unfold flatAlternatingProduct alternatingCoordinateProduct
  apply contDiff_polynomialListProduct_ofFn a
    (fun z : AlternatingLawData n × (Fin m → ℝ) => z.1.1) _ contDiff_fst.fst
  intro j
  apply contDiff_dynkinProduct a
    (fun z : AlternatingLawData n × (Fin m → ℝ) => z.1.1) _ _ contDiff_fst.fst
  · exact contDiff_fst.snd.fst.clm_apply
      (((contDiff_apply ℝ ((Fin n → ℝ) × (Fin n → ℝ)) j).comp
        (e.contDiff.comp contDiff_snd)).fst)
  · exact contDiff_fst.snd.snd.clm_apply
      (((contDiff_apply ℝ ((Fin n → ℝ) × (Fin n → ℝ)) j).comp
        (e.contDiff.comp contDiff_snd)).snd)

theorem flatAlternatingProduct_submersive {m n h c : ℕ}
    (a : DynkinCoefficients c 2)
    (e : (Fin m → ℝ) ≃L[ℝ] (Fin h → (Fin n → ℝ) × (Fin n → ℝ)))
    (p : AlternatingLawData n) (z : Fin h → (Fin n → ℝ) × (Fin n → ℝ))
    (hs : Function.Surjective
      (fderiv ℝ (alternatingCoordinateProduct a p.1 p.2.1 p.2.2) z)) :
    Function.Surjective (fderiv ℝ (flatAlternatingProduct a e p) (e.symm z)) := by
  have hf : DifferentiableAt ℝ (alternatingCoordinateProduct a p.1 p.2.1 p.2.2)
      (e (e.symm z)) :=
    ((contDiff_alternatingCoordinateProduct (q := 1) a p.1 p.2.1 p.2.2).differentiable
      one_ne_zero) _
  have hd := hf.hasFDerivAt.comp (e.symm z) e.hasFDerivAt
  rw [e.apply_symm_apply] at hd
  change HasFDerivAt (flatAlternatingProduct a e p) _ (e.symm z) at hd
  intro y
  obtain ⟨v, hv⟩ := hs y
  refine ⟨e.symm v, ?_⟩
  rw [hd.fderiv]
  simpa using hv

end PolycyclicRecognition

end

end OAI
