import OAI.Probability.SwitchChain.SliceSynthesis
import OAI.Probability.SwitchChain.SliceGramAction

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem gram_action_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix c)) =
      ofMatrix (intersectionAction a b d c) := by
  ext p
  rcases p with ⟨i,j⟩
  rw [gram_synthesis_apply, ofMatrix_apply]
  simp only [ofMatrix_apply]
  by_cases hij : i=j
  · subst j
    simp [hzdiag, intersectionAction]
  · have h := half_sum_kernel_eq_intersectionAction a b d
      (fun k l => 2 * ⟪z i j,z k l⟫) c hsym hdiag hij (hgram i j hij)
    have hsum : (∑ k, ∑ l, (2 * ⟪z i j,z k l⟫) * c k l) =
        2 * (∑ k, ∑ l, c k l * ⟪z i j,z k l⟫) := by
      simp_rw [show ∀ k l, (2 * ⟪z i j,z k l⟫) * c k l =
        2 * (c k l * ⟪z i j,z k l⟫) by intros; ring]
      simp only [← Finset.mul_sum]
    rw [hsum] at h
    linarith

theorem gram_linear_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (u : V → ℝ) (hu : (∑ i, u i) = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix (linearPair u))) =
      (a + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d) •
        ofMatrix (linearPair u) := by
  rw [gram_action_of_orbit_entries z a b d hzdiag hgram _
    (linearPair_symmetric u) (linearPair_diag u)]
  ext p
  exact intersectionAction_linearPair a b d u hu p.1 p.2

theorem gram_rowZero_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, rowSum c i = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix c)) =
      (a-2*b+d) • ofMatrix c := by
  rw [gram_action_of_orbit_entries z a b d hzdiag hgram c hsym hdiag]
  ext p
  exact intersectionAction_rowZero a b d c hsym hdiag hrow p.1 p.2

end Problem315.SliceSynthesis

end

end OAI
