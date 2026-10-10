import OAI.Probability.SwitchChain.ProposalLaplacian

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.PairSquaredEnergy
attribute [local instance] Classical.propDecidable

def reverseMove {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) : GraphState n d × SwitchProposal n :=
  if validSwitch x.1.val x.2 then (proposalState x.1 x.2, reverseProposal x.2) else x

lemma reverseMove_involutive {n : ℕ} {d : Fin n → ℕ} :
    Function.Involutive (@reverseMove n d) := by
  intro x
  rcases x with ⟨G,p⟩
  by_cases h : validSwitch G.val p
  · have hr : validSwitch (proposalState G p).val (reverseProposal p) := by
      change validSwitch (proposalResult G.val p) (reverseProposal p)
      rw [proposalResult_of_valid h]
      exact validSwitch_reverse_replace h
    have hb : proposalState (proposalState G p) (reverseProposal p) = G := by
      apply Subtype.ext
      exact proposalResult_reverse h
    simp [reverseMove, h, hr, hb]
  · simp [reverseMove, h]

def reverseMoveEquiv {n : ℕ} {d : Fin n → ℕ} :
    Equiv.Perm (GraphState n d × SwitchProposal n) :=
  ⟨reverseMove, reverseMove, reverseMove_involutive, reverseMove_involutive⟩

lemma reverseMove_fst {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) :
    (reverseMove x).1 = proposalState x.1 x.2 := by
  by_cases h : validSwitch x.1.val x.2
  · simp [reverseMove, h]
  · simp only [reverseMove, ite_eq_right h]
    apply Subtype.ext
    simp [proposalState, proposalResult, h]

lemma crossingPairs_reverse {n : ℕ} (p : SwitchProposal n) :
    SwitchPairFiber.crossingPairs (reverseProposal p) = SwitchPairFiber.crossingPairs p := by
  ext a
  simp only [SwitchPairFiber.crossingPairs, Finset.mem_filter]
  change (a ∈ p.1.val.powersetCard 2 ∧ SwitchPairFiber.Crosses (reverseProposal p) a) ↔ _
  unfold SwitchPairFiber.Crosses
  simp only [removedMatching_reverse, addedMatching_reverse, or_comm]

lemma reverseMove_crossing {n : ℕ} {d : Fin n → ℕ}
    (x : GraphState n d × SwitchProposal n) (a : Finset (Fin n)) :
    a ∈ SwitchPairFiber.crossingPairs (reverseMove x).2 ↔
      a ∈ SwitchPairFiber.crossingPairs x.2 := by
  by_cases h : validSwitch x.1.val x.2
  · simp [reverseMove, h, crossingPairs_reverse]
  · simp [reverseMove, h]

theorem involution_energy {X : Type*} [Fintype X] (e : Equiv.Perm X)
    (he : Function.Involutive e) (w f : X → ℝ) (hw : ∀ x, w (e x) = w x) :
    (∑ x, w x * f x * (f x - f (e x))) =
      (1 / 2 : ℝ) * ∑ x, w x * (f x - f (e x)) ^ 2 := by
  have hr : (∑ x, w x * f (e x) * (f (e x) - f x)) =
      ∑ x, w x * f x * (f x - f (e x)) := by
    have h := Equiv.sum_comp e (fun x => w x * f x * (f x - f (e x)))
    have he' (x : X) : e (e x) = x := he x
    simpa only [hw, he'] using h
  have hsum : (∑ x, w x * (f x - f (e x)) ^ 2) =
      (∑ x, w x * f x * (f x - f (e x))) +
      (∑ x, w x * f (e x) * (f (e x) - f x)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum, hr]
  ring

theorem pairSwitchLaplacian_energy {n : ℕ} {d : Fin n → ℕ}
    (a : Finset (Fin n)) (f : GraphState n d → ℝ) :
    (∑ G, f G * pairSwitchLaplacian n d a f G) =
      (1 / 2 : ℝ) * ∑ G, ∑ p ∈ allProposals n,
        if a ∈ SwitchPairFiber.crossingPairs p then
          (f G - f (proposalState G p)) ^ 2 else 0 := by
  let w : GraphState n d × SwitchProposal n → ℝ :=
    fun x => if a ∈ SwitchPairFiber.crossingPairs x.2 then 1 else 0
  have hw (x : GraphState n d × SwitchProposal n) :
      w (reverseMoveEquiv x) = w x := by
    change (if a ∈ SwitchPairFiber.crossingPairs (reverseMove x).2 then (1:ℝ) else 0) = _
    simp only [reverseMove_crossing, w]
  have h := involution_energy (@reverseMoveEquiv n d) reverseMove_involutive
    w (fun x => f x.1) hw
  change (∑ x, w x * f x.1 * (f x.1 - f (reverseMove x).1)) =
    (1 / 2 : ℝ) * ∑ x, w x * (f x.1 - f (reverseMove x).1) ^ 2 at h
  simp only [reverseMove_fst, Fintype.sum_prod_type] at h
  simpa only [w, pairSwitchLaplacian, allProposals, Finset.mul_sum,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero] using h

end Problem315.PairSquaredEnergy

end

end OAI
