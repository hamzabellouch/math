import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFAtomicRepresentation

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_quantile_spatial {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) :
    scalarCDFValue β (quantileCDF k Q) 0 1=
      fun x => scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) scalarSpinTerminal x+
          (β*Real.sqrt (1-Q (Fin.last k)))^2/2 := by
  change Monotone Q ∧ (∀ j, Q j∈Icc (0:ℝ) 1) at hQ
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_prefix_chain Q hQ.1 (hQ.2 0).1
  let t : ℝ≥0 := ⟨1-Q (Fin.last k),sub_nonneg.mpr (hQ.2 (Fin.last k)).2⟩
  have hdur : chainDuration (l++[(1,t)])=1 := by
    apply NNReal.coe_injective
    rw [chainDuration_append,NNReal.coe_add,hd]
    simp only [chainDuration_cons,chainDuration_nil,add_zero,NNReal.coe_one]
    change Q (Fin.last k)+(1-Q (Fin.last k))=1
    ring
  have hm' : ∀ p∈l++[(1,t)], p.1∈Icc (0:ℝ) 1 := by
    intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact hm p hp
    · have hp' := List.mem_singleton.mp hp
      subst p
      exact ⟨zero_le_one,le_rfl⟩
  have hmodel' : TimeChainModels (quantileCDF k Q) 0 (l++[(1,t)]) := by
    apply hmodel.append
    constructor
    · intro z hz
      apply quantileCDF_of_last_le Q hQ.1
      simpa only [zero_add,hd] using hz.1
    · trivial
  funext x
  rw [show scalarCDFValue β (quantileCDF k Q) 0 1 x=
    scalarTimeChain β (l++[(1,t)]) scalarSpinTerminal x from
    scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) _ hm' 0 1 le_rfl hdur hmodel' x]
  rw [scalarTimeChain_append]
  simp only [scalarTimeChain,scalarTimeStep,scalarStep_one_spin,t]
  rw [he,scalarHierarchy_add_const _ _ _ _ scalarSpinTerminal_regular]
  rfl

theorem scalarCDFGradient_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) :
    scalarCDFGradient β (quantileCDF k Q) 0 1=
      rootGradient 0 (scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) scalarSpinTerminal) := by
  funext x
  have H := scalarCDFValue_hasDerivAt β (quantileCDF_bounds k Q)
    (quantileCDF_monotone k Q) 0 1 le_rfl x
  rw [scalarCDFValue_quantile_spatial β Q hQ] at H
  exact H.unique ((scalarHierarchy_spin_hasDerivAt _ _ _ x).add_const _)

theorem scalarCDFHessian_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) :
    scalarCDFHessian β (quantileCDF k Q) 0 1=
      rootHessian 0 (scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) scalarSpinTerminal) := by
  funext x
  have H := scalarCDFGradient_hasDerivAt β (quantileCDF_bounds k Q)
    (quantileCDF_monotone k Q) 0 1 le_rfl x
  rw [scalarCDFGradient_quantile β Q hQ] at H
  exact H.unique (scalarHierarchy_spin_gradient_hasDerivAt _ _ _ x)

end SK.Analytic

end
end

end OAI
