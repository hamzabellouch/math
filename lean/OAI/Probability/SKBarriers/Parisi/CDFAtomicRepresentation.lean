import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileMinimizer
import OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit
import OAI.Probability.SKBarriers.Hierarchy.TimeChainRepresentation
import OAI.Probability.SKBarriers.Parisi.QuantileChain

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileCDF_of_last_le {k : ℕ} (Q : Fin (k+1) → ℝ) (hQ : Monotone Q)
    {z : ℝ} (hz : Q (Fin.last k) ≤ z) : quantileCDF k Q z=1 := by
  rw [quantileCDF_formula]
  simp only [ite_eq_left ((hQ (Fin.le_last _)).trans hz),uniformAtom_sum]

theorem quantile_full_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) (h1 : Q (Fin.last k) ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=1 ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β, scalarTimeChain β l scalarSpinTerminal 0=atomicScalarValue k β Q := by
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_prefix_chain Q hQ h0
  let t := NNReal.mk (1-Q (Fin.last k)) (sub_nonneg.mpr h1)
  refine ⟨l++[(1,t)],?_,?_,?_,?_⟩
  · apply NNReal.coe_injective
    simp only [chainDuration_append,chainDuration_cons,chainDuration_nil,add_zero,
      NNReal.coe_add,hd,t,NNReal.coe_mk,NNReal.coe_one]
    ring
  · intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact hm p hp
    · have hp' := List.mem_singleton.mp hp
      subst p
      exact ⟨zero_le_one,le_rfl⟩
  · apply hmodel.append
    constructor
    · intro z hz
      apply quantileCDF_of_last_le Q hQ
      simpa only [zero_add,hd] using hz.1
    · trivial
  · intro β
    rw [scalarTimeChain_append]
    simp only [scalarTimeChain]
    rw [he]
    rfl

theorem scalarCDFValue_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) (h1 : Q (Fin.last k) ≤ 1) :
    scalarCDFValue β (quantileCDF k Q) 0 1 0=atomicScalarValue k β Q := by
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_full_chain Q hQ h0 h1
  exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
    β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l hm 0 1 le_rfl hd hmodel 0).trans (he β)

def scalarCDFParisi (β : ℝ) (α : ℝ → ℝ) : ℝ :=
  scalarCDFValue β α 0 1 0-(β^2/2)*∫ s in Icc (0:ℝ) 1, s*α s

theorem scalarCDFParisi_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q ∈ admissibleQuantiles k) :
    scalarCDFParisi β (quantileCDF k Q)=extendedQuantileParisi k β Q := by
  rw [scalarCDFParisi,scalarCDFValue_quantile β Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2]
  exact atomicParisi_eq_extended k β Q hQ.2

end SK.Analytic

end
end

end OAI
