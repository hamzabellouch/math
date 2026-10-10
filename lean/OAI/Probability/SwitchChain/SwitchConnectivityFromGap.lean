import OAI.Probability.SwitchChain.Definitions
import OAI.Probability.SwitchChain.FiniteConnectivity

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315

theorem switchKernel_nonzero_support (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) (hK : switchKernel n d G H ≠ 0) :
    G = H ∨ SwitchStep n d G H := by
  classical
  by_cases hGH : G = H
  · exact Or.inl hGH
  right
  have hfilter : ((allProposals n).filter
      (fun p => proposalResult G.val p = H.val)).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [switchKernel, hGH, he] at hK
  obtain ⟨p, hp⟩ := hfilter
  have hpresult := (Finset.mem_filter.mp hp).2
  have hpvalid : validSwitch G.val p := by
    by_contra hv
    have hvv : G.val = H.val := by simpa [proposalResult, hv] using hpresult
    exact hGH (Subtype.ext hvv)
  exact ⟨p, hpvalid, hpresult⟩

theorem switch_connectivity_of_positive_gap (n : Nat) (d : Fin n → Nat)
    (γ : ℝ) (hγ : 0 < γ)
    (hrow : ∀ G : GraphState n d,
      ∑ H ∈ allGraphStates n d, switchKernel n d G H = 1)
    (hgap : hasSpectralGapAtLeast n d γ)
    (G H : GraphState n d) : Relation.ReflTransGen (SwitchStep n d) G H := by
  classical
  apply FiniteConnectivity.of_poincare (SwitchStep n d) (switchKernel n d) γ hγ
  · intro K
    simpa [allGraphStates] using hrow K
  · exact switchKernel_nonzero_support n d
  · intro f
    simpa [uniformVariance, uniformAverage, dirichletEnergy, uniformInner,
      markovApply, stateCount, allGraphStates] using hgap f

end Problem315

end

end OAI
