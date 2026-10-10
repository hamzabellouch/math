import Mathlib
import OAI.Computability.MinUncut.Estimates.OuterRemainder
import OAI.Computability.MinUncut.Estimates.RowListBridge

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient

structure ProofFamily (Name I : Type*) [Fintype I] where
  first : (U : I → Equation Name) → FoldedProof (FirstAlphabet U)
  second : (V : I → SecondQuestion Name) → FoldedProof (SecondAlphabet V)

variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

def ProofFamily.rows (f : ProofFamily Name I) (σ η : ℝ) (c : Point m n → ℝ)
    (x : Point m n) (r : Row m n) : LocalRows Name I {t : Row m n // t≠r} where
  first U := comparisonRow (f.first U) σ η c x r
  second V := comparisonRow (f.second V) σ η c x r

lemma ProofFamily.rows_first_bound (f : ProofFamily Name I) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (c : Point m n → ℝ) (x : Point m n) (r : Row m n)
    (U : I → Equation Name) (D : Rest (W := Forms (FirstAlphabet U)) r)
    (z : Forms (FirstAlphabet U)) :
    |(f.rows σ η c x r).first U D z| ≤ Real.sqrt (n^m:ℕ)/σ :=
  gradient_abs_le _ _ hσ η c x

lemma ProofFamily.rows_second_bound (f : ProofFamily Name I) {σ : ℝ} (hσ : 0<σ) (η : ℝ)
    (c : Point m n → ℝ) (x : Point m n) (r : Row m n)
    (V : I → SecondQuestion Name) (D : Rest (W := Forms (SecondAlphabet V)) r)
    (z : Forms (SecondAlphabet V)) :
    |(f.rows σ η c x r).second V D z| ≤ Real.sqrt (n^m:ℕ)/σ :=
  gradient_abs_le _ _ hσ η c x

lemma ProofFamily.rows_atom_integrable (f : ProofFamily Name I) {σ θ : ℝ}
    (hσ : σ≠0) (hθ : 0<θ) (η : ℝ) (x : Point m n) (i : Fin m)
    (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B : Rest (W := Forms (SecondAlphabet (secondQuestion U h pos))) (⟨i,face x i⟩ : Row m n)) :
    Integrable (fun c => (f.rows σ η c x ⟨i,face x i⟩).atom θ U h pos B) (gauss (Point m n)) := by
  change Integrable (fun c => if (labelList (comparisonRow (f.second _) σ η c x ⟨i,face x i⟩ B) θ).Nonempty then (1:ℝ) else 0) _
  simp_rw [← rowAtomIndicator_eq_list _ σ η hθ]
  exact rowAtomIndicator_integrable _ hσ η θ x i B

lemma ProofFamily.rows_distance_integrable (f : ProofFamily Name I) {σ : ℝ}
    (hσ : σ≠0) (η : ℝ) (x : Point m n) (r : Row m n)
    (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B : Rest (W := Forms (SecondAlphabet (secondQuestion U h pos))) r) :
    Integrable (fun c => (f.rows σ η c x r).distance U h pos B) (gauss (Point m n)) := by
  apply integrable_expect
  intro z
  exact ((gradient_memLp (f.second _) _ hσ η x).sub
    (gradient_memLp (f.first U) _ hσ η x)).integrable_sq

lemma rest_card (r : Row m n) : Fintype.card {t : Row m n // t≠r}=Fintype.card (Row m n)-1 := by
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique (α := {t : Row m n // t=r})]

end MinUncut.Outer

end
end

end OAI
