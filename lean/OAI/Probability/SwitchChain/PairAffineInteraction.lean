import OAI.Probability.SwitchChain.PairRangeInteraction
import OAI.Probability.SwitchChain.PairEqualityProjection
import OAI.Probability.SwitchChain.SwitchFlip

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def AffineFlagImage (i j k l : Fin n) (f : StateSpace n d) : Prop :=
  ∃ base weight : StateSpace n d,
    base ∈ fiberSpace n d {i,j} ∧ weight ∈ fiberSpace n d {i,j} ∧
    (∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → weight G = 0) ∧
    f = base + multiply weight (observable i k l)

theorem affineFlagImage_of_cellwise {β : Type*}
    (i j k l : Fin n) (key : GraphState n d → β)
    (hkey : ∀ G H : GraphState n d, SameFiber {i,j} G.val H.val → key G = key H)
    (f : StateSpace n d)
    (hcell : ∀ c : β, ∃ A B : ℝ,
      (∀ G : GraphState n d, key G = c → f G = A + B * observable i k l G) ∧
      (∀ G : GraphState n d, key G = c → crossTotal i j k l G ≠ 2 → B = 0)) :
    AffineFlagImage i j k l f := by
  choose A B hformula hsupport using hcell
  let base : StateSpace n d := WithLp.toLp 2 (fun G => A (key G))
  let weight : StateSpace n d := WithLp.toLp 2 (fun G => B (key G))
  refine ⟨base,weight,?_,?_,?_,?_⟩
  · intro G H h
    change A (key G) = A (key H)
    rw [hkey G H h]
  · intro G H h
    change B (key G) = B (key H)
    rw [hkey G H h]
  · intro G hG
    exact hsupport (key G) G rfl hG
  · ext G
    exact hformula (key G) G rfl

theorem fluctuation_mem_of_affineFlagImage
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (f : StateSpace n d) (hf : AffineFlagImage i j k l f) :
    fluctuation n d {i,j} f ∈ equalitySpace i j k l := by
  obtain ⟨base,weight,hbase,hweight,hsupport,rfl⟩ := hf
  rw [map_add, (fluctuation_eq_zero_iff _ _).mpr hbase, zero_add]
  exact fluctuation_weighted_observable_mem i j k l hij hk hl weight hweight hsupport

theorem projection_fixes_fluctuation_of_affineFlagImage
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (f : StateSpace n d) (hf : AffineFlagImage i j k l f) :
    projection i j k l (fluctuation n d {i,j} f) = fluctuation n d {i,j} f :=
  (projection_eq_self_iff _ _ _ _ _).mpr
    (fluctuation_mem_of_affineFlagImage i j k l hij hk hl f hf)

theorem interaction_of_affine_conditional_images
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : Outside i j k) (hl : Outside i j l)
    (hi : Outside k l i) (hj : Outside k l j)
    (G : StateSpace n d →L[ℝ] StateSpace n d)
    (hGs : G.toLinearMap.IsSymmetric) (hGi : ∀ f, G (G f) = G f)
    (hGa : ∀ f, G (expectation n d {i,j} f) = 0)
    (hGb : ∀ f, G (expectation n d {k,l} f) = 0)
    (hBA : ∀ f, AffineFlagImage i j k l
      (expectation n d {k,l} (expectation n d {i,j} f)))
    (hAB : ∀ f, AffineFlagImage k l i j
      (expectation n d {i,j} (expectation n d {k,l} f)))
    (f : StateSpace n d) :
    2 * ‖G f‖ ^ 2 - ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  exact pair_interaction_of_correlated_ranges {i,j} {k,l} G
    (projection i j k l) (projection k l i j) hGs
    (equalitySpace i j k l).starProjection_isSymmetric
    (equalitySpace k l i j).starProjection_isSymmetric
    hGi hGa hGb
    (fun z => projection_fixes_fluctuation_of_affineFlagImage i j k l hij hk hl _ (hBA z))
    (fun z => projection_fixes_fluctuation_of_affineFlagImage k l i j hkl hi hj _ (hAB z)) f

theorem switch_interaction_of_affine_conditional_images
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : Outside i j k) (hl : Outside i j l)
    (hi : Outside k l i) (hj : Outside k l j)
    (p : SwitchProposal n)
    (hpa : SwitchPairFiber.Crosses p {i,j}) (hpb : SwitchPairFiber.Crosses p {k,l})
    (hBA : ∀ f : StateSpace n d, AffineFlagImage i j k l
      (expectation n d {k,l} (expectation n d {i,j} f)))
    (hAB : ∀ f : StateSpace n d, AffineFlagImage k l i j
      (expectation n d {i,j} (expectation n d {k,l} f)))
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection p f‖ ^ 2 -
        ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  exact interaction_of_affine_conditional_images i j k l hij hkl hk hl hi hj
    (SwitchFlip.projection p) (SwitchFlip.projection_symmetric p)
    (SwitchFlip.projection_idempotent p)
    (SwitchFlip.projection_expectation p {i,j} hpa)
    (SwitchFlip.projection_expectation p {k,l} hpb) hBA hAB f

end Problem315.PairEquality

end

end OAI
