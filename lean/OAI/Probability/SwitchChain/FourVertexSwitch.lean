import OAI.Probability.SwitchChain.SwitchFoundations

namespace OAI

noncomputable section

namespace Problem315

def FourDistinct {α : Type*} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

private def twoEdgeGraph {n : Nat} (a b c d : Fin n)
    (hab : a ≠ b) (hcd : c ≠ d) : SimpleGraph (Fin n) where
  Adj u v := (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
    (u = c ∧ v = d) ∨ (u = d ∧ v = c)
  symm := by
    constructor
    intro u v huv
    tauto
  loopless := by
    constructor
    intro v hv
    rcases hv with h | h | h | h
    · exact hab (h.1.symm.trans h.2)
    · exact hab (h.2.symm.trans h.1)
    · exact hcd (h.1.symm.trans h.2)
    · exact hcd (h.2.symm.trans h.1)

private theorem twoEdgeGraph_matching {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) :
    IsPerfectMatchingOn {a, b, c, d}
      (twoEdgeGraph a b c d h.1 h.2.2.2.2.2) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  intro v
  constructor
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · refine ⟨b, ?_, ?_⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · intro y hy
        simp_all [twoEdgeGraph]
    · refine ⟨a, ?_, ?_⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
    · refine ⟨d, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
    · refine ⟨c, ?_, ?_⟩
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · intro y hy
        simp_all [twoEdgeGraph]
        aesop
  · intro hv w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    change (v = a ∧ w = b) ∨ (v = b ∧ w = a) ∨
      (v = c ∧ w = d) ∨ (v = d ∧ w = c) at hw
    tauto

def fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) : SwitchProposal n := by
  classical
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  let S : FourSet n := ⟨{a, b, c, d}, by
    simp [hab, hac, had, hbc, hbd, hcd]⟩
  have hfirst : IsPerfectMatchingOn S.val (twoEdgeGraph a b c d hab hcd) :=
    twoEdgeGraph_matching a b c d ⟨hab, hac, had, hbc, hbd, hcd⟩
  have hsecond : IsPerfectMatchingOn S.val (twoEdgeGraph a c b d hac hbd) := by
    have hm := twoEdgeGraph_matching a c b d ⟨hac, hab, had, hbc.symm, hcd, hbd⟩
    convert hm using 1
    ext x
    simp [S, or_left_comm]
  refine ⟨S, ⟨(⟨twoEdgeGraph a b c d hab hcd, hfirst⟩,
    ⟨twoEdgeGraph a c b d hac hbd, hsecond⟩), ?_⟩⟩
  intro heq
  have he := congrArg (fun M : PerfectMatching S => M.val.Adj a b) heq
  simp [twoEdgeGraph, hab, hac, had, hbc, hbd, Ne.symm hab] at he

@[simp] theorem removedMatching_fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) (u v : Fin n) :
    (removedMatching (fourVertexProposal a b c d h)).Adj u v ↔
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
      (u = c ∧ v = d) ∨ (u = d ∧ v = c) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  rfl

@[simp] theorem addedMatching_fourVertexProposal {n : Nat} (a b c d : Fin n)
    (h : FourDistinct a b c d) (u v : Fin n) :
    (addedMatching (fourVertexProposal a b c d h)).Adj u v ↔
      (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
      (u = b ∧ v = d) ∨ (u = d ∧ v = b) := by
  rcases h with ⟨hab, hac, had, hbc, hbd, hcd⟩
  rfl

theorem validSwitch_fourVertexProposal_iff {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d) :
    validSwitch G (fourVertexProposal a b c d h) ↔
      G.Adj a b ∧ G.Adj c d ∧ ¬ G.Adj a c ∧ ¬ G.Adj b d := by
  constructor
  · intro hv
    refine ⟨hv.1 ?_, hv.1 ?_, hv.2 ?_, hv.2 ?_⟩ <;> simp
  · rintro ⟨hab, hcd, hac, hbd⟩
    constructor
    · intro u v huv
      rw [removedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact G.symm.symm _ _ hab
      · exact hcd
      · exact G.symm.symm _ _ hcd
    · intro u v huv
      rw [addedMatching_fourVertexProposal] at huv
      rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hac
      · exact fun he => hac (G.symm.symm _ _ he)
      · exact hbd
      · exact fun he => hbd (G.symm.symm _ _ he)

theorem proposalResult_fourVertex_adj {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (u v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj u v ↔
      (G.Adj u v ∧ ¬ ((u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        (u = c ∧ v = d) ∨ (u = d ∧ v = c))) ∨
      (u = a ∧ v = c) ∨ (u = c ∧ v = a) ∨
      (u = b ∧ v = d) ∨ (u = d ∧ v = b) := by
  classical
  have hv : validSwitch G (fourVertexProposal a b c d h) :=
    (validSwitch_fourVertexProposal_iff G a b c d h).2 ⟨hab, hcd, hac, hbd⟩
  simp only [proposalResult, ite_eq_left hv, replaceEdges,
    removedMatching_fourVertexProposal, addedMatching_fourVertexProposal]

theorem switchStep_of_fourVertex_result {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e)
    (heq : proposalResult G.val (fourVertexProposal a b c e h) = H.val) :
    SwitchStep n d G H := by
  exact ⟨fourVertexProposal a b c e h,
    (validSwitch_fourVertexProposal_iff G.val a b c e h).2 ⟨hab, hce, hac, hbe⟩, heq⟩

theorem proposalResult_fourVertex_adj_first {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (v : Fin n) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj a v ↔
      (G.Adj a v ∧ v ≠ b) ∨ v = c := by
  simpa [h.1, h.2.1, h.2.2.1] using
    proposalResult_fourVertex_adj G a b c d h hab hcd hac hbd a v

theorem proposalResult_fourVertex_adj_outside {n : Nat} (G : SimpleGraph (Fin n))
    (a b c d : Fin n) (h : FourDistinct a b c d)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d)
    (u v : Fin n) (hua : u ≠ a) (hub : u ≠ b) (huc : u ≠ c) (hud : u ≠ d) :
    (proposalResult G (fourVertexProposal a b c d h)).Adj u v ↔ G.Adj u v := by
  simpa [hua, hub, huc, hud] using
    proposalResult_fourVertex_adj G a b c d h hab hcd hac hbd u v

def fourVertexState {n : Nat} {d : Fin n → Nat} (G : GraphState n d)
    (a b c e : Fin n) (h : FourDistinct a b c e) : GraphState n d :=
  ⟨proposalResult G.val (fourVertexProposal a b c e h),
    proposalResult_realizes G.property (fourVertexProposal a b c e h)⟩

theorem switchStep_fourVertexState {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    SwitchStep n d G (fourVertexState G a b c e h) := by
  exact switchStep_of_fourVertex_result G _ a b c e h hab hce hac hbe rfl

theorem fourVertexState_agrees_outside {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (he : e ∈ R)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e)
    (u v : Fin n) (hu : u ∉ R) :
    (fourVertexState G a b c e h).val.Adj u v ↔ G.val.Adj u v := by
  apply proposalResult_fourVertex_adj_outside G.val a b c e h hab hce hac hbe u v
  · exact fun heq => hu (heq ▸ ha)
  · exact fun heq => hu (heq ▸ hb)
  · exact fun heq => hu (heq ▸ hc)
  · exact fun heq => hu (heq ▸ he)

end Problem315

end

end OAI
