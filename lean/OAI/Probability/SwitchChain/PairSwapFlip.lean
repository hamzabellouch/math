import OAI.Probability.SwitchChain.PairAssignmentMoves
import OAI.Probability.SwitchChain.ProposalUniqueness
import OAI.Probability.SwitchChain.ProposalLaplacian

namespace OAI

noncomputable section
namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

theorem reverse_fourVertexProposal {n : ℕ} (i u v j : Fin n)
    (h : FourDistinct i u v j) (hr : FourDistinct i v u j) :
    reverseProposal (fourVertexProposal i u v j h) = fourVertexProposal i v u j hr := by
  apply SwitchProposal.ext_matchings
  · ext x y
    simp only [removedMatching_reverse, addedMatching_fourVertexProposal,
      removedMatching_fourVertexProposal]
  · ext x y
    simp only [addedMatching_reverse, removedMatching_fourVertexProposal,
      addedMatching_fourVertexProposal]

theorem valid_fourVertex_iff_left_membership {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j) :
    validSwitch G.val (fourVertexProposal i u v j h) ↔
      u ∈ leftSet G.val i j ∧ v ∉ leftSet G.val i j := by
  rw [validSwitch_fourVertexProposal_iff]
  obtain ⟨huo, huadj⟩ := (mem_singletonSet G.val i j u).mp hu
  obtain ⟨hvo, hvadj⟩ := (mem_singletonSet G.val i j v).mp hv
  simp only [mem_leftSet, huo, hvo, true_and]
  constructor
  · rintro ⟨hiu, hvj, hiv, huj⟩
    exact ⟨⟨hiu, fun hju => huj hju.symm⟩, fun hh => hiv hh.1⟩
  · rintro ⟨⟨hiu, hju⟩, hvl⟩
    have hr : G.val.Adj j v ∧ ¬ G.val.Adj i v := hvadj.resolve_left hvl
    exact ⟨hiu, hr.1.symm, hr.2, fun huj => hju huj.symm⟩

theorem state_eq_bidirectional_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j = (leftSet G.val i j).map (Equiv.swap u v).toEmbedding) :
    H = if validSwitch G.val (fourVertexProposal i u v j h) then
      proposalState G (fourVertexProposal i u v j h)
    else if validSwitch G.val (reverseProposal (fourVertexProposal i u v j h)) then
      proposalState G (reverseProposal (fourVertexProposal i u v j h)) else G := by
  classical
  let hr : FourDistinct i v u j :=
    ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1.symm, h.2.2.2.2.2, h.2.2.2.2.1⟩
  rw [reverse_fourVertexProposal i u v j h hr]
  have hp := valid_fourVertex_iff_left_membership G i u v j h hu hv
  have hq := valid_fourVertex_iff_left_membership G i v u j hr hv hu
  have hforward (hvl : u ∈ leftSet G.val i j) (hvr : v ∉ leftSet G.val i j) :
      H = proposalState G (fourVertexProposal i u v j h) := by
    have hh := (validSwitch_fourVertexProposal_iff G.val i u v j h).mp
      (hp.mpr ⟨hvl, hvr⟩)
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans (fourVertexState_key G i u v j h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm
    · change leftSet H.val i j = leftSet (fourVertexState G i u v j h).val i j
      rw [hleft, map_swap_eq_exchange _ u v hvl hvr,
        fourVertexState_leftSet G i u v j h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2]
  have hreverse (hvl : v ∈ leftSet G.val i j) (hvr : u ∉ leftSet G.val i j) :
      H = proposalState G (fourVertexProposal i v u j hr) := by
    have hh := (validSwitch_fourVertexProposal_iff G.val i v u j hr).mp
      (hq.mpr ⟨hvl, hvr⟩)
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq
    · exact hkey.trans (fourVertexState_key G i v u j hr hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm
    · change leftSet H.val i j = leftSet (fourVertexState G i v u j hr).val i j
      rw [hleft, Equiv.swap_comm u v, map_swap_eq_exchange _ v u hvl hvr,
        fourVertexState_leftSet G i v u j hr hh.1 hh.2.1 hh.2.2.1 hh.2.2.2]
  have hfixed (hh : u ∈ leftSet G.val i j ↔ v ∈ leftSet G.val i j) : H = G := by
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq hkey
    rw [hleft, map_swap_eq_self_of_mem_iff _ u v hh]
  by_cases hul : u ∈ leftSet G.val i j <;> by_cases hvl : v ∈ leftSet G.val i j
  · rw [ite_eq_right (by simp only [hp, hul, hvl, not_true_eq_false, and_false, not_false_eq_true]),
      ite_eq_right (by simp only [hq, hul, hvl, not_true_eq_false, and_false, not_false_eq_true])]
    exact hfixed (by simp [hul, hvl])
  · rw [ite_eq_left (hp.mpr ⟨hul, hvl⟩)]
    exact hforward hul hvl
  · rw [ite_eq_right (by simp only [hp, hul, false_and, not_false_eq_true]),
      ite_eq_left (hq.mpr ⟨hvl, hul⟩)]
    exact hreverse hvl hul
  · rw [ite_eq_right (by simp only [hp, hul, false_and, not_false_eq_true]),
      ite_eq_right (by simp only [hq, hvl, false_and, not_false_eq_true])]
    exact hfixed (by simp [hul, hvl])

theorem assignmentRelabel_swap_eq_bidirectional {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (h : FourDistinct i x.val y.val j)
    (T : Assignment G.val i j) :
    ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j (Equiv.swap x y) T)).val =
    let H := ((stateFiberEquiv G i j hij).symm T).val
    let p := fourVertexProposal i x.val y.val j h
    if validSwitch H.val p then proposalState H p
    else if validSwitch H.val (reverseProposal p) then
      proposalState H (reverseProposal p) else H := by
  classical
  let H : GraphState n d := ((stateFiberEquiv G i j hij).symm T).val
  let K : GraphState n d := ((stateFiberEquiv G i j hij).symm
    (assignmentRelabel G.val i j (Equiv.swap x y) T)).val
  have hkH : key i j H.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm T).property
  have hkK : key i j K.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm _).property
  have hlH : leftSet H.val i j = T.val :=
    leftSet_trade G.val i j hij T.val T.property.1
  have hlK : leftSet K.val i j = T.val.map (Equiv.swap x.val y.val).toEmbedding := by
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
        (assignmentRelabel_swap_val G.val i j x y T)
  apply state_eq_bidirectional_of_key_leftSet_swap H K i x.val y.val j h
  · rw [singletonSet_eq_of_key_eq hkH]
    exact x.property
  · rw [singletonSet_eq_of_key_eq hkH]
    exact y.property
  · exact hkK.trans hkH.symm
  · rw [hlK, hlH]

theorem fourDistinct_of_singleton_labels {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : i ≠ j) (x y : singletonSet G i j) (hxy : x ≠ y) :
    FourDistinct i x.val y.val j := by
  have hx := ((mem_singletonSet G i j x.val).mp x.property).1
  have hy := ((mem_singletonSet G i j y.val).mp y.property).1
  exact ⟨hx.1.symm, hy.1.symm, hij,
    fun hval => hxy (Subtype.ext hval), hx.2, hy.2⟩

theorem singleton_labels_of_valid_fourVertex {n : ℕ} (G : SimpleGraph (Fin n))
    (i u v j : Fin n) (h : FourDistinct i u v j)
    (hp : validSwitch G (fourVertexProposal i u v j h)) :
    u ∈ singletonSet G i j ∧ v ∈ singletonSet G i j := by
  have hh := (validSwitch_fourVertexProposal_iff G i u v j h).mp hp
  constructor
  · apply (mem_singletonSet G i j u).mpr
    exact ⟨⟨h.1.symm, h.2.2.2.2.1⟩,
      Or.inl ⟨hh.1, fun huj => hh.2.2.2 huj.symm⟩⟩
  · apply (mem_singletonSet G i j v).mpr
    exact ⟨⟨h.2.1.symm, h.2.2.2.2.2⟩, Or.inr ⟨hh.2.1.symm, hh.2.2.1⟩⟩

theorem bidirectional_eq_self_of_not_singleton {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i u v j : Fin n) (h : FourDistinct i u v j)
    (hout : ¬ (u ∈ singletonSet G.val i j ∧ v ∈ singletonSet G.val i j)) :
    (if validSwitch G.val (fourVertexProposal i u v j h) then
      proposalState G (fourVertexProposal i u v j h)
    else if validSwitch G.val (reverseProposal (fourVertexProposal i u v j h)) then
      proposalState G (reverseProposal (fourVertexProposal i u v j h)) else G) = G := by
  have hp : ¬ validSwitch G.val (fourVertexProposal i u v j h) :=
    fun hv => hout (singleton_labels_of_valid_fourVertex G.val i u v j h hv)
  let hr : FourDistinct i v u j :=
    ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1.symm, h.2.2.2.2.2, h.2.2.2.2.1⟩
  have hq : ¬ validSwitch G.val (reverseProposal (fourVertexProposal i u v j h)) := by
    rw [reverse_fourVertexProposal i u v j h hr]
    intro hv
    exact hout (singleton_labels_of_valid_fourVertex G.val i v u j hr hv).symm
  simp only [ite_eq_right hp, ite_eq_right hq]

theorem fourVertexProposal_exchange_pairs {n : ℕ} (i u v j : Fin n)
    (h : FourDistinct i u v j) (hs : FourDistinct u i j v) :
    fourVertexProposal i u v j h = fourVertexProposal u i j v hs := by
  apply SwitchProposal.ext_matchings
  · ext x y
    simp only [removedMatching_fourVertexProposal]
    tauto
  · ext x y
    simp only [addedMatching_fourVertexProposal]
    tauto

end Problem315.PairFiber

end

end OAI
