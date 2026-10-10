import OAI.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

theorem fullTaggedSlowProjectionChart_center_change
    (c c' : ∀ j, J j → ℝ) (j : Fin m) (i : J j) :
    fullTaggedSlowProjectionChart J P N poly c' (Sum.inr ⟨j, i⟩) =
      fullTaggedSlowProjectionChart J P N poly c (Sum.inr ⟨j, i⟩) +
        C (c' j i - c j i) := by
  simp only [fullTaggedSlowProjectionChart_inr, fullTaggedCenteredCoordinates,
    map_sub, rename_C]
  ring

theorem fullTaggedSlowProjectionChart_center_injective :
    Function.Injective (fullTaggedSlowProjectionChart J P N poly) := by
  intro c c' h
  funext j i
  have htag := congrFun h (Sum.inr ⟨j, i⟩)
  rw [fullTaggedSlowProjectionChart_center_change J P N poly c c' j i] at htag
  have hz : C (c' j i - c j i) = (0 : MvPolynomial (X ⊕ (Σ j, J j)) ℝ) := by
    apply add_left_cancel (a := fullTaggedSlowProjectionChart J P N poly c (Sum.inr ⟨j, i⟩))
    simpa only [add_zero] using htag.symm
  have hzero : c' j i - c j i = 0 := by
    simpa using congrArg (constantCoeff : MvPolynomial (X ⊕ (Σ j, J j)) ℝ →+* ℝ) hz
  exact (sub_eq_zero.mp hzero).symm

theorem fullTaggedSlowProjectionChart_eq_iff_center_eq
    (c c' : ∀ j, J j → ℝ) :
    fullTaggedSlowProjectionChart J P N poly c =
      fullTaggedSlowProjectionChart J P N poly c' ↔ c = c' :=
  (fullTaggedSlowProjectionChart_center_injective J P N poly).eq_iff

end Erdos3.VectorPolynomial

end

end OAI
