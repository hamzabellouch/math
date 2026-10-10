import Mathlib
import OAI.Analysis.Crouzeix.HomologicalCauchy
import OAI.Analysis.Crouzeix.PolynomialApproximation
import OAI.Analysis.Crouzeix.Sharpness

namespace OAI

/-! Hilbert Extension. -/

noncomputable section

open Set Filter Metric

open scoped Topology

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem differentiableOn_resolvent [CompleteSpace H] (A : Operator H) :
    DifferentiableOn ℂ (fun z : ℂ => Ring.inverse (algebraMap ℂ (Operator H) z - A))
      (numericalClosure A)ᶜ := by
  intro z hz
  have hr : z ∈ resolventSet ℂ A := by
    by_contra h
    exact hz (spectrum_subset_numericalClosure A h)
  exact (spectrum.hasDerivAt_resolvent_const_left hr).differentiableAt.differentiableWithinAt

theorem contourEval_eq_integral (A : Operator H) (Γ : SmoothContour) (f : ℂ → ℂ) :
    contourEval A Γ f =
      Γ.integral (fun z => f z • Ring.inverse (algebraMap ℂ (Operator H) z - A)) := by
  simp only [contourEval, SmoothContour.integral, smul_smul]

theorem contourEval_independent [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ Δ : CalculusContour (numericalClosure A) U) :
    contourEval A Γ.toSmoothContour f = contourEval A Δ.toSmoothContour f := by
  let V := U \ numericalClosure A
  have hV : IsOpen V := hU.sdiff isClosed_closure
  let paths : Bool → SmoothContour := fun b => if b then Γ.toSmoothContour else Δ.toSmoothContour
  let c : Bool → ℂ := fun b => if b then 1 else -1
  have hp : ∀ b, (paths b).trace ⊆ V := by
    intro b z hz
    cases b <;> rcases hz with ⟨t, ht, rfl⟩
    · exact Δ.avoids t ht
    · exact Γ.avoids t ht
  have hi : ∀ z ∉ V, ∑ b, c b * (paths b).index z = 0 := by
    intro z hz
    simp only [Fintype.sum_bool, paths, c, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, ← sub_eq_add_neg]
    by_cases hK : z ∈ numericalClosure A
    · rw [Γ.index_inside z hK, Δ.index_inside z hK, sub_self]
    · have hzU : z ∉ U := fun hzU => hz ⟨hzU, hK⟩
      rw [Γ.index_outside z hzU, Δ.index_outside z hzU, sub_self]
  have hd : DifferentiableOn ℂ (fun z => f z •
      Ring.inverse (algebraMap ℂ (Operator H) z - A)) V :=
    (hf.mono (fun _ hz => hz.1)).fun_smul
      ((differentiableOn_resolvent A).mono (fun _ hz => hz.2))
  have h := sum_integral_eq_zero_of_null_homology paths c hV hp hi hd
  simp only [Fintype.sum_bool, paths, c, Bool.false_eq_true, ite_false, ite_true,
    one_smul, neg_smul, ← sub_eq_add_neg] at h
  rw [contourEval_eq_integral, contourEval_eq_integral]
  exact sub_eq_zero.mp h

theorem holomorphicEval_eq_contourEval [CompleteSpace H] (A : Operator H)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (Γ : CalculusContour (numericalClosure A) U) :
    holomorphicEval A U f = contourEval A Γ.toSmoothContour f :=
  holomorphicEval_eq_contourEval_of_independent A Γ f (fun Δ => contourEval_independent A hU hf Δ Γ)

theorem nonzeroConclusion_of_finite_matrix_bound [CompleteSpace H] [Nontrivial H]
    (hfin : FiniteMatrixPolynomialBound) (A : Operator H) : NonzeroConclusion A :=
  nonzeroConclusion_of_finite_bound_and_contour_independence A hfin
    (fun _U hU _hK _f hf Γ Δ => contourEval_independent A hU hf Γ Δ)

theorem hilbert_of_finite_matrix_bound (hfin : FiniteMatrixPolynomialBound)
    (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator H) :
    (Nontrivial H → NonzeroConclusion A) ∧
    (Subsingleton H → ZeroConclusion A) ∧ SharpConstant := by
  refine ⟨fun h => ?_, fun h => ?_, sharpConstant⟩
  · have := h
    exact nonzeroConclusion_of_finite_matrix_bound hfin A
  · have := h
    exact zeroConclusion A

end CrouzeixHilbert

end

end OAI
