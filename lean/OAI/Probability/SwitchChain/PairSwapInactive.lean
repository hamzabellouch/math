import OAI.Probability.SwitchChain.PairSwapFlip
import OAI.Probability.SwitchChain.ProposalLaplacian

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFiber

theorem singleton_labels_of_valid_reverse_fourVertex
    {n : ℕ} (G : SimpleGraph (Fin n)) (i k l j : Fin n)
    (h : FourDistinct i k l j)
    (hv : validSwitch G (reverseProposal (fourVertexProposal i k l j h))) :
    k ∈ singletonSet G i j ∧ l ∈ singletonSet G i j := by
  have hil : G.Adj i l := hv.1 (by simp)
  have hkj : G.Adj k j := hv.1 (by simp)
  have hik : ¬ G.Adj i k := hv.2 (by simp)
  have hlj : ¬ G.Adj l j := hv.2 (by simp)
  constructor
  · exact (mem_singletonSet G i j k).mpr
      ⟨⟨h.1.symm, h.2.2.2.2.1⟩, Or.inr ⟨hkj.symm, hik⟩⟩
  · exact (mem_singletonSet G i j l).mpr
      ⟨⟨h.2.1.symm, h.2.2.2.2.2⟩, Or.inl ⟨hil, fun hjl => hlj hjl.symm⟩⟩

theorem not_valid_of_nonsingleton
    {n : ℕ} (G : SimpleGraph (Fin n)) (i k l j : Fin n)
    (h : FourDistinct i k l j)
    (hinactive : k ∉ singletonSet G i j ∨ l ∉ singletonSet G i j) :
    ¬ validSwitch G (fourVertexProposal i k l j h) ∧
      ¬ validSwitch G (reverseProposal (fourVertexProposal i k l j h)) := by
  have hnot : ¬ (k ∈ singletonSet G i j ∧ l ∈ singletonSet G i j) := by
    rcases hinactive with hk | hl
    · exact fun hs => hk hs.1
    · exact fun hs => hl hs.2
  exact ⟨fun hv => hnot (singleton_labels_of_valid_fourVertex G i k l j h hv),
    fun hv => hnot (singleton_labels_of_valid_reverse_fourVertex G i k l j h hv)⟩

theorem bidirectional_proposal_fix_of_nonsingleton
    {n : ℕ} {d : Fin n → ℕ} (G : GraphState n d) (i k l j : Fin n)
    (h : FourDistinct i k l j)
    (hinactive : k ∉ singletonSet G.val i j ∨ l ∉ singletonSet G.val i j) :
    (if validSwitch G.val (fourVertexProposal i k l j h) then
      proposalState G (fourVertexProposal i k l j h)
    else if validSwitch G.val (reverseProposal (fourVertexProposal i k l j h)) then
      proposalState G (reverseProposal (fourVertexProposal i k l j h))
    else G) = G := by
  obtain ⟨hf, hr⟩ := not_valid_of_nonsingleton G.val i k l j h hinactive
  simp only [ite_eq_right hf, ite_eq_right hr]

theorem nonsingleton_of_sameFiber
    {n : ℕ} {G H : SimpleGraph (Fin n)} (i j k l : Fin n) (hij : i ≠ j)
    (hGH : PairResampling.SameFiber {i, j} G H)
    (hinactive : k ∉ singletonSet G i j ∨ l ∉ singletonSet G i j) :
    k ∉ singletonSet H i j ∨ l ∉ singletonSet H i j := by
  have hs := singletonSet_eq_of_key_eq ((sameFiber_iff_key_eq i j hij G H).mp hGH)
  rwa [← hs]

theorem bidirectional_proposal_fix_on_inactive_fiber
    {n : ℕ} {d : Fin n → ℕ} (G H : GraphState n d) (i k l j : Fin n)
    (h : FourDistinct i k l j)
    (hH : H ∈ PairResampling.fiberStates {i, j} G)
    (hinactive : k ∉ singletonSet G.val i j ∨ l ∉ singletonSet G.val i j) :
    (if validSwitch H.val (fourVertexProposal i k l j h) then
      proposalState H (fourVertexProposal i k l j h)
    else if validSwitch H.val (reverseProposal (fourVertexProposal i k l j h)) then
      proposalState H (reverseProposal (fourVertexProposal i k l j h))
    else H) = H := by
  apply bidirectional_proposal_fix_of_nonsingleton H i k l j h
  exact nonsingleton_of_sameFiber i j k l h.2.2.1
    ((PairResampling.mem_fiberStates {i, j} G H).mp hH) hinactive

end Problem315.PairFiber

end

end OAI
