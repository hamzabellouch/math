import OAI.Probability.SwitchChain.DisjointGraphAffine
import OAI.Probability.SwitchChain.DisjointProjectionCell
import OAI.Probability.SwitchChain.PairAffineInteraction
import OAI.Probability.SwitchChain.CrossTogglePairs

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling DisjointEncoding DisjointMarginal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem right_left_expectation_affine (e : Fin 4 ↪ Fin n)
    (f : StateSpace n d) :
    AffineFlagImage (e 0) (e 1) (e 2) (e 3)
      (expectation n d {e 2,e 3} (expectation n d {e 0,e 1} f)) := by
  apply affineFlagImage_of_cellwise _ _ _ _ (cellIndex e)
    (fun G H h => (cellIndex_eq_iff e G H).mpr
      (sameCell_of_sameFiber_left e G.val H.val h))
  intro c
  induction c using Quotient.inductionOn with
  | h G =>
    obtain ⟨A,B,hB,hAB⟩ := right_left_expectation_cell_affine e G f
    refine ⟨A,B,?_,?_⟩
    · intro H hH
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      exact hAB ⟨H,hcell⟩
    · intro H hH ht
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      apply hB
      rwa [← equality_crossTotal_on_cell e G ⟨H,hcell⟩]

theorem left_right_expectation_affine (e : Fin 4 ↪ Fin n)
    (f : StateSpace n d) :
    AffineFlagImage (e 2) (e 3) (e 0) (e 1)
      (expectation n d {e 0,e 1} (expectation n d {e 2,e 3} f)) := by
  apply affineFlagImage_of_cellwise _ _ _ _ (cellIndex e)
    (fun G H h => (cellIndex_eq_iff e G H).mpr
      (sameCell_of_sameFiber_right e G.val H.val h))
  intro c
  induction c using Quotient.inductionOn with
  | h G =>
    obtain ⟨A,B,hB,hAB⟩ := left_right_expectation_cell_affine e G f
    refine ⟨A,B,?_,?_⟩
    · intro H hH
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      exact hAB ⟨H,hcell⟩
    · intro H hH ht
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      apply hB
      rwa [← equality_crossTotal_reverse_on_cell e G ⟨H,hcell⟩]

theorem actual_switch_interaction (e : Fin 4 ↪ Fin n)
    (p : SwitchProposal n)
    (hpa : SwitchPairFiber.Crosses p {e 0,e 1})
    (hpb : SwitchPairFiber.Crosses p {e 2,e 3})
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection p f‖ ^ 2 -
        ‖projection (e 0) (e 1) (e 2) (e 3) f‖ ^ 2 -
        ‖projection (e 2) (e 3) (e 0) (e 1) f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {e 0,e 1} f,
        fluctuation n d {e 2,e 3} f⟫ := by
  have he (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j :=
    fun h => hij (e.injective h)
  exact switch_interaction_of_affine_conditional_images
    (e 0) (e 1) (e 2) (e 3) (he 0 1 (by decide)) (he 2 3 (by decide))
    ⟨he 2 0 (by decide),he 2 1 (by decide)⟩
    ⟨he 3 0 (by decide),he 3 1 (by decide)⟩
    ⟨he 0 2 (by decide),he 0 3 (by decide)⟩
    ⟨he 1 2 (by decide),he 1 3 (by decide)⟩
    p hpa hpb (right_left_expectation_affine e)
    (left_right_expectation_affine e) f

theorem actual_named_interaction (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  let e : Fin 4 ↪ Fin n :=
    ⟨![i,j,k,l], by
      rcases h with ⟨hij,hik,hil,hjk,hjl,hkl⟩
      intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [Ne.symm hij, Ne.symm hik, Ne.symm hil,
          Ne.symm hjk, Ne.symm hjl, Ne.symm hkl]⟩
  exact actual_switch_interaction e (CrossToggle.crossProposal i j k l h)
    (CrossToggle.crossProposal_left i j k l h)
    (CrossToggle.crossProposal_right i j k l h) f

end Problem315.PairEquality

end

end OAI
