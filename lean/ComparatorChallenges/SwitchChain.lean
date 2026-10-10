import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem315

def graphDegree {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) : Nat := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

def Realizes (n : Nat) (d : Fin n → Nat) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v, graphDegree G v = d v

abbrev GraphState (n : Nat) (d : Fin n → Nat) :=
  {G : SimpleGraph (Fin n) // Realizes n d G}

def Graphical (n : Nat) (d : Fin n → Nat) : Prop :=
  Nonempty (GraphState n d)

abbrev FourSet (n : Nat) := {S : Finset (Fin n) // S.card = 4}

def IsPerfectMatchingOn {n : Nat} (S : Finset (Fin n))
    (M : SimpleGraph (Fin n)) : Prop :=
  ∀ v, (v ∈ S → ∃! w, M.Adj v w) ∧
    (v ∉ S → ∀ w, ¬ M.Adj v w)

abbrev PerfectMatching {n : Nat} (S : FourSet n) :=
  {M : SimpleGraph (Fin n) // IsPerfectMatchingOn S.1 M}

abbrev SwitchProposal (n : Nat) :=
  Σ S : FourSet n,
    {p : PerfectMatching S × PerfectMatching S // p.1 ≠ p.2}

def removedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.1.val

def addedMatching {n : Nat} (p : SwitchProposal n) : SimpleGraph (Fin n) :=
  p.2.val.2.val

def validSwitch {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : Prop :=
  (∀ ⦃u v⦄, (removedMatching p).Adj u v → G.Adj u v) ∧
  (∀ ⦃u v⦄, (addedMatching p).Adj u v → ¬ G.Adj u v)

def replaceEdges {n : Nat} (G M N : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := (G.Adj u v ∧ ¬ M.Adj u v) ∨ N.Adj u v
  symm := by
    constructor
    intro u v h
    rcases h with h | h
    · left
      exact ⟨G.symm.symm u v h.1, fun hm => h.2 (M.symm.symm v u hm)⟩
    · right
      exact N.symm.symm u v h
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact G.loopless.irrefl v h.1
    · exact N.loopless.irrefl v h

def proposalResult {n : Nat} (G : SimpleGraph (Fin n))
    (p : SwitchProposal n) : SimpleGraph (Fin n) := by
  classical
  exact
    if validSwitch G p then
      replaceEdges G (removedMatching p) (addedMatching p)
    else G

def allGraphStates (n : Nat) (d : Fin n → Nat) :
    Finset (GraphState n d) := by
  classical
  exact Finset.univ

def allProposals (n : Nat) : Finset (SwitchProposal n) := by
  classical
  exact Finset.univ

def stateCount (n : Nat) (d : Fin n → Nat) : Nat :=
  (allGraphStates n d).card

def switchKernel (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : ℝ := by
  classical
  exact
    (if G = H then (1 : ℝ) / 2 else 0) +
      (((allProposals n).filter
          (fun p => proposalResult G.val p = H.val)).card : ℝ) /
        (12 * (Nat.choose n 4 : ℝ))

def kernelPow (n : Nat) (d : Fin n → Nat) :
    Nat → GraphState n d → GraphState n d → ℝ := by
  classical
  intro t
  induction t with
  | zero =>
      exact fun G H => if G = H then 1 else 0
  | succ t previous =>
      exact fun G H =>
        Finset.sum (allGraphStates n d)
          (fun K => previous G K * switchKernel n d K H)

def uniformAverage (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  Finset.sum (allGraphStates n d) (fun G => f G) /
    (stateCount n d : ℝ)

def uniformInner (n : Nat) (d : Fin n → Nat)
    (f g : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d (fun G => f G * g G)

def uniformVariance (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformAverage n d
    (fun G => (f G - uniformAverage n d f) ^ 2)

def markovApply (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) (G : GraphState n d) : ℝ :=
  Finset.sum (allGraphStates n d)
    (fun H => switchKernel n d G H * f H)

def dirichletEnergy (n : Nat) (d : Fin n → Nat)
    (f : GraphState n d → ℝ) : ℝ :=
  uniformInner n d f (fun G => f G - markovApply n d f G)

def hasSpectralGapAtLeast (n : Nat) (d : Fin n → Nat) (γ : ℝ) : Prop :=
  ∀ f : GraphState n d → ℝ,
    γ * uniformVariance n d f ≤ dirichletEnergy n d f

def tvDistanceFrom (n : Nat) (d : Fin n → Nat)
    (t : Nat) (G : GraphState n d) : ℝ :=
  (1 / 2 : ℝ) *
    Finset.sum (allGraphStates n d)
      (fun H =>
        |kernelPow n d t G H - (1 : ℝ) / (stateCount n d : ℝ)|)

def MixedAt (n : Nat) (d : Fin n → Nat) (t : Nat) : Prop :=
  ∀ G : GraphState n d, tvDistanceFrom n d t G ≤ (1 : ℝ) / 4

def mixingTime (n : Nat) (d : Fin n → Nat)
    (h : ∃ t : Nat, MixedAt n d t) : Nat := by
  classical
  exact Nat.find h

def SwitchStep (n : Nat) (d : Fin n → Nat)
    (G H : GraphState n d) : Prop :=
  ∃ p : SwitchProposal n,
    validSwitch G.val p ∧ proposalResult G.val p = H.val

theorem switch_chain_main :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ((∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧ (stateCount n d = 1 → (MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0)) ∧ (1 < stateCount n d → hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))) := by
  sorry

theorem switch_chain_tv_bound :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d), tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  sorry

theorem switch_connectivity :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ∀ G H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H := by
  sorry

end Problem315

end

end OAI
