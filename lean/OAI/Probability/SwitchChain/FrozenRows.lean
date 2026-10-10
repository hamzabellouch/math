import OAI.Probability.SwitchChain.FourVertexSwitch

namespace OAI

noncomputable section

namespace Problem315

def FrozenRowsAgree {n : Nat} (G H : SimpleGraph (Fin n))
    (R : Finset (Fin n)) : Prop :=
  ∀ u, u ∉ R → ∀ v, G.Adj u v ↔ H.Adj u v

theorem FrozenRowsAgree.refl {n : Nat} (G : SimpleGraph (Fin n))
    (R : Finset (Fin n)) : FrozenRowsAgree G G R := by
  intro u hu v
  rfl

theorem FrozenRowsAgree.symm {n : Nat} {G H : SimpleGraph (Fin n)}
    {R : Finset (Fin n)} (h : FrozenRowsAgree G H R) : FrozenRowsAgree H G R := by
  intro u hu v
  exact (h u hu v).symm

theorem FrozenRowsAgree.trans {n : Nat} {G H K : SimpleGraph (Fin n)}
    {R : Finset (Fin n)} (hGH : FrozenRowsAgree G H R)
    (hHK : FrozenRowsAgree H K R) : FrozenRowsAgree G K R := by
  intro u hu v
  exact (hGH u hu v).trans (hHK u hu v)

theorem graphDegree_split_residual {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (R : Finset (Fin n)) (v : Fin n) :
    (R.filter (G.Adj v)).card + ((Finset.univ \ R).filter (G.Adj v)).card =
      graphDegree G v := by
  classical
  have hin : (Finset.univ.filter (G.Adj v)).filter (fun w => w ∈ R) =
      R.filter (G.Adj v) := by
    ext w
    simp [and_comm]
  have hout : (Finset.univ.filter (G.Adj v)).filter (fun w => w ∉ R) =
      (Finset.univ \ R).filter (G.Adj v) := by
    ext w
    simp [and_comm]
  have hs := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (G.Adj v)) (fun w => w ∈ R)
  rw [hin, hout] at hs
  calc
    _ = (Finset.univ.filter (G.Adj v)).card := hs
    _ = graphDegree G v := by
      unfold graphDegree
      congr 1
      ext w
      simp

theorem residualDegree_eq_of_frozenRows {n : Nat} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (R : Finset (Fin n))
    (hdeg : ∀ v, graphDegree G v = graphDegree H v)
    (hfreeze : FrozenRowsAgree G H R) (v : Fin n) :
    (R.filter (G.Adj v)).card = (R.filter (H.Adj v)).card := by
  classical
  have hout : (Finset.univ \ R).filter (G.Adj v) =
      (Finset.univ \ R).filter (H.Adj v) := by
    apply Finset.filter_congr
    intro w hw
    have hwR : w ∉ R := (Finset.mem_sdiff.mp hw).2
    constructor
    · intro hvw
      exact ((hfreeze w hwR v).1 hvw.symm).symm
    · intro hvw
      exact ((hfreeze w hwR v).2 hvw.symm).symm
  have hg := graphDegree_split_residual G R v
  have hh := graphDegree_split_residual H R v
  rw [hout, hdeg v] at hg
  omega

theorem graphState_residualDegree_eq {n : Nat} {d : Fin n → Nat}
    (G H : GraphState n d) [DecidableRel G.val.Adj] [DecidableRel H.val.Adj]
    (R : Finset (Fin n)) (hfreeze : FrozenRowsAgree G.val H.val R) (v : Fin n) :
    (R.filter (G.val.Adj v)).card = (R.filter (H.val.Adj v)).card := by
  apply residualDegree_eq_of_frozenRows G.val H.val R _ hfreeze v
  intro u
  exact (G.property u).trans (H.property u).symm

theorem fourVertexState_residual_neighbors {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    [DecidableRel G.val.Adj] [DecidableRel (fourVertexState G a b c e h).val.Adj]
    (hc : c ∈ R) (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    R.filter ((fourVertexState G a b c e h).val.Adj a) =
      insert c ((R.filter (G.val.Adj a)).erase b) := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  change (w ∈ R ∧ (proposalResult G.val (fourVertexProposal a b c e h)).Adj a w) ↔ _
  rw [proposalResult_fourVertex_adj_first G.val a b c e h hab hce hac hbe]
  constructor
  · rintro ⟨hwR, ⟨hadj, hwb⟩ | rfl⟩
    · exact Or.inr ⟨hwb, hwR, hadj⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨hwb, hwR, hadj⟩)
    · exact ⟨hc, Or.inr rfl⟩
    · exact ⟨hwR, Or.inl ⟨hadj, hwb⟩⟩

theorem fourVertexState_frozenRows {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (R : Finset (Fin n))
    (a b c e : Fin n) (h : FourDistinct a b c e)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (he : e ∈ R)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    FrozenRowsAgree (fourVertexState G a b c e h).val G.val R := by
  intro u hu v
  exact fourVertexState_agrees_outside G R a b c e h ha hb hc he hab hce hac hbe u v hu

end Problem315

end

end OAI
