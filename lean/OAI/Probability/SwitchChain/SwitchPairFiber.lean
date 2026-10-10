import OAI.Probability.SwitchChain.SwitchFoundations

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

lemma matching_endpoints_mem {n : ℕ} {S : FourSet n}
    (M : PerfectMatching S) {u v : Fin n} (h : M.val.Adj u v) :
    u ∈ S.val ∧ v ∈ S.val := by
  constructor
  · by_contra hu
    exact (M.property u).2 hu v h
  · by_contra hv
    exact (M.property v).2 hv u h.symm

theorem exists_cross_cut {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    ∃ A : Finset (Fin n), A.card = 2 ∧ A ⊆ p.1.val ∧
      ∀ a b, ((removedMatching p).Adj a b ∨ (addedMatching p).Adj a b) →
        (a ∈ A ↔ b ∉ A) := by
  classical
  let S := p.1
  let M := p.2.val.1
  let N := p.2.val.2
  have hS : S.val.card = 4 := S.property
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < S.val.card by omega)
  obtain ⟨v, huv, hvuniq⟩ := (M.property u).1 hu
  obtain ⟨w, huw, hwuniq⟩ := (N.property u).1 hu
  have hv := (matching_endpoints_mem M huv).2
  have hw := (matching_endpoints_mem N huw).2
  have huvne : u ≠ v := M.val.ne_of_adj huv
  have huwne : u ≠ w := N.val.ne_of_adj huw
  have hvwne : v ≠ w := by
    intro heq
    subst w
    exact validSwitch_matchings_disjoint hp huv huw
  let T : Finset (Fin n) := {u, v, w}
  have hT : T.card = 3 := by simp [T, huvne, huwne, hvwne]
  have hnot : ¬ S.val ⊆ T := by
    intro h
    have := Finset.card_le_card h
    omega
  obtain ⟨x, hx⟩ := Finset.sdiff_nonempty.mpr hnot
  have hxS : x ∈ S.val := (Finset.mem_sdiff.mp hx).1
  have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
  have hxune : x ≠ u := by intro h; apply hxT; simp [T, h]
  have hxvne : x ≠ v := by intro h; apply hxT; simp [T, h]
  have hxwne : x ≠ w := by intro h; apply hxT; simp [T, h]
  have hfull : S.val = {u, v, w, x} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    · simp [hS, huvne, huwne, hvwne, hxune.symm, hxvne.symm, hxwne.symm]
  have hMxw : M.val.Adj x w := by
    obtain ⟨y, hxy, hyuniq⟩ := (M.property x).1 hxS
    have hy := (matching_endpoints_mem M hxy).2
    rw [hfull] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · exact False.elim (hxvne (hvuniq x hxy.symm))
    · obtain ⟨z, hz, hzuniq⟩ := (M.property v).1 hv
      have hxu : x = u := (hzuniq x hxy.symm).trans (hzuniq u huv.symm).symm
      exact False.elim (hxune hxu)
    · exact hxy
    · exact False.elim (M.val.loopless.irrefl x hxy)
  have hNxv : N.val.Adj x v := by
    obtain ⟨y, hxy, hyuniq⟩ := (N.property x).1 hxS
    have hy := (matching_endpoints_mem N hxy).2
    rw [hfull] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy | hy <;> subst y
    · exact False.elim (hxwne (hwuniq x hxy.symm))
    · exact hxy
    · obtain ⟨z, hz, hzuniq⟩ := (N.property w).1 hw
      have hxu : x = u := (hzuniq x hxy.symm).trans (hzuniq u huw.symm).symm
      exact False.elim (hxune hxu)
    · exact False.elim (N.val.loopless.irrefl x hxy)
  refine ⟨{u, x}, by simp [hxune.symm], ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  · intro a b hab
    have hmem : a ∈ S.val := by
      rcases hab with hab | hab
      · exact (matching_endpoints_mem M hab).1
      · exact (matching_endpoints_mem N hab).1
    rw [hfull] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with ha | ha | ha | ha <;> subst a
    all_goals rcases hab with hab | hab
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton]
    · have hb := hvuniq b hab
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb := hwuniq b hab
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = u := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property v).1 hv
        exact (hzuniq b hab).trans (hzuniq u huv.symm).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb : b = x := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property v).1 hv
        exact (hzuniq b hab).trans (hzuniq x hNxv.symm).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]
    · have hb : b = x := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property w).1 hw
        exact (hzuniq b hab).trans (hzuniq x hMxw.symm).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = u := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property w).1 hw
        exact (hzuniq b hab).trans (hzuniq u huw.symm).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = w := by
        obtain ⟨z, hz, hzuniq⟩ := (M.property x).1 hxS
        exact (hzuniq b hab).trans (hzuniq w hMxw).symm
      subst b
      simp [huwne, hxwne, hxune, Ne.symm]
    · have hb : b = v := by
        obtain ⟨z, hz, hzuniq⟩ := (N.property x).1 hxS
        exact (hzuniq b hab).trans (hzuniq v hNxv).symm
      subst b
      simp [huvne, hxvne, hxune, Ne.symm]

theorem exists_frozen_cut {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    ∃ A : Finset (Fin n), A.card = 2 ∧ A ⊆ p.1.val ∧
      ∀ a b, (a ∈ A ↔ b ∈ A) →
        ((proposalResult G p).Adj a b ↔ G.Adj a b) := by
  classical
  obtain ⟨A, hA, hAS, hcross⟩ := exists_cross_cut p hp
  refine ⟨A, hA, hAS, ?_⟩
  intro a b hside
  have hm : ¬ (removedMatching p).Adj a b := by
    intro h
    have := hcross a b (Or.inl h)
    tauto
  have hn : ¬ (addedMatching p).Adj a b := by
    intro h
    have := hcross a b (Or.inr h)
    tauto
  rw [proposalResult_of_valid hp]
  change ((G.Adj a b ∧ ¬ (removedMatching p).Adj a b) ∨
    (addedMatching p).Adj a b) ↔ G.Adj a b
  simp [hm, hn]

theorem degree_into_eq {n : ℕ} (G H : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (w : Fin n)
    (hdegree : graphDegree G w = graphDegree H w)
    (hout : ∀ v, v ∉ A → (G.Adj w v ↔ H.Adj w v)) :
    (A.filter (G.Adj w)).card = (A.filter (H.Adj w)).card := by
  classical
  let D (X : SimpleGraph (Fin n)) := Finset.univ.filter (X.Adj w)
  have hinter (X : SimpleGraph (Fin n)) :
      D X ∩ A = A.filter (X.Adj w) := by
    ext v
    simp [D, and_comm]
  have hdiff : D G \ A = D H \ A := by
    ext v
    simp only [Finset.mem_sdiff, D, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨(hout v h.2).mp h.1, h.2⟩
    · intro h
      exact ⟨(hout v h.2).mpr h.1, h.2⟩
  have hG := Finset.card_sdiff_add_card_inter (D G) A
  have hH := Finset.card_sdiff_add_card_inter (D H) A
  rw [hinter] at hG hH
  have hcard : (D G).card = (D H).card := hdegree
  rw [hdiff, hcard] at hG
  exact Nat.add_left_cancel (hG.trans hH.symm)

end Problem315.SwitchPairFiber

end

end OAI
