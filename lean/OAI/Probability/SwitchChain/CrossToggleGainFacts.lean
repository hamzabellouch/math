import OAI.Probability.SwitchChain.CrossToggleGain
import OAI.Probability.SwitchChain.PairAffineInteraction

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.CrossToggle

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

@[simp] theorem gain_fluctuation_left (a b : Finset (Fin n))
    (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.fluctuation n d a f) = gain a b f := by
  rw [PairResampling.fluctuation_eq_sub, map_sub, gain_expectation_left, sub_zero]

@[simp] theorem gain_fluctuation_right (a b : Finset (Fin n))
    (f : PairResampling.StateSpace n d) :
    gain a b (PairResampling.fluctuation n d b f) = gain a b f := by
  rw [PairResampling.fluctuation_eq_sub, map_sub, gain_expectation_right, sub_zero]

theorem gain_interaction_of_affine_conditional_images
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : PairFiber.Outside i j k) (hl : PairFiber.Outside i j l)
    (hi : PairFiber.Outside k l i) (hj : PairFiber.Outside k l j)
    (hBA : ∀ f : PairResampling.StateSpace n d,
      PairEquality.AffineFlagImage i j k l
        (PairResampling.expectation n d {k,l} (PairResampling.expectation n d {i,j} f)))
    (hAB : ∀ f : PairResampling.StateSpace n d,
      PairEquality.AffineFlagImage k l i j
        (PairResampling.expectation n d {i,j} (PairResampling.expectation n d {k,l} f)))
    (f : PairResampling.StateSpace n d) :
    2 * ‖gain {i,j} {k,l} f‖ ^ 2 -
        ‖PairEquality.projection i j k l f‖ ^ 2 -
        ‖PairEquality.projection k l i j f‖ ^ 2 ≤
      2 * ⟪PairResampling.fluctuation n d {i,j} f,
        PairResampling.fluctuation n d {k,l} f⟫ := by
  exact PairEquality.interaction_of_affine_conditional_images i j k l hij hkl
    hk hl hi hj (gain {i,j} {k,l}) (gain_isSymmetric _ _) (gain_idempotent _ _)
    (gain_expectation_left _ _) (gain_expectation_right _ _) hBA hAB f

end Problem315.CrossToggle

end

end OAI
