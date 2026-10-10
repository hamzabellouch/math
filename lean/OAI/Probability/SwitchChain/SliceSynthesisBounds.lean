import OAI.Probability.SwitchChain.SliceSynthesisAction
import OAI.Probability.SwitchChain.SliceGramConstant

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem intersectionAction_constant_zero_of_total (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l) :
    ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0 := by
  have h := gram_action_of_orbit_entries z 1 b d hzdiag hgram
    (constantPair 1) (constantPair_symmetric 1) (constantPair_diag 1)
  rw [synthesis_constant z hzdiag hztotal, map_zero] at h
  intro i j
  have he := congrArg (fun c : Coeff V => c (i,j)) h
  simpa only [ofMatrix_apply, PiLp.zero_apply] using he.symm

theorem constant_relation_of_orbit_entries [Nontrivial V]
    (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l) :
    1 + 2 * ((Fintype.card V : ℝ) - 2) * b +
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d = 0 := by
  exact constant_relation_of_intersectionAction_eq_zero b d
    (intersectionAction_constant_zero_of_total z b d hzdiag hztotal hgram)

theorem degree_two_bound_of_orbit_entries
    (hcard : 4 ≤ Fintype.card V) (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l)
    (hpositive : 0 ≤ 1 + ((Fintype.card V : ℝ) - 4) * b -
      ((Fintype.card V : ℝ) - 3) * d) :
    1 - 2 * b + d ≤ (Fintype.card V : ℝ) - 1 := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact degree_two_bound_of_intersectionAction_eq_zero hcard b d
    (intersectionAction_constant_zero_of_total z b d hzdiag hztotal hgram) hpositive

end Problem315.SliceSynthesis

end

end OAI
