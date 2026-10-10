import OAI.Combinatorics.Progressions.Lattices.JointAffineL1Parameter

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineMonomialCoefficientDensity_eq_jet {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype N] [DecidableEq N]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : I → Finset α) (x : X → ℝ) (vertices : Finset α → K → ℤ) (T : K → ℝ)
    (hT : ∀ k, 0 < T k)
    (hcoords : ∀ t k, (vertices t k : ℝ) / T k = normalizedCubeTuple input z x t k)
    (hfull : ((Matrix.fromCols A
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows)).submatrix id
        (s.trans Function.Embedding.inl)).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (c w : J ⊕ N → ℝ) {δ : ℝ≥0} (hδ : 0 < δ) (hw : ∀ j, (δ : ℝ) ≤ w j)
    (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    selectedCoefficientDensity (Matrix.fromCols A
      (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows))
      (s.trans Function.Embedding.inl) hfull
      (Sum.elim S (fun n => H / monomialScale T (e n))) (fun _ => H)
      (Sum.rec hS (fun n => div_pos hH (monomialScale_pos T hT (e n)))) (fun _ => hH)
      (affineProductProfile c w) =
      normalizedJetDensity
        (normalizedPivotEquiv (A.submatrix id s) hA (fun i => S (s i)) (fun _ => H)
          (fun i => hS (s i)) (fun _ => hH))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s) (fun j => S j.val) (fun _ => H)))
        e input z rows
        (selectedCoefficientProfile s (affineProductProfile (fun j => c (.inl j)) (fun j => w (.inl j))))
        (affineProductProfile (fun n => c (.inr n)) (fun n => w (.inr n))) x := by
  have he := affineCoefficientDensity_split A
    (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows)
    s hA hfull S (fun n => H / monomialScale T (e n)) (fun _ => H) hS
    (fun n => div_pos hH (monomialScale_pos T hT (e n))) (fun _ => hH) c w hδ hw R hsupport
  rw [normalizedIntegerJetColumns_eq e input z rows x vertices T hcoords hH.ne'] at he
  exact he

end Erdos3

end

end OAI
