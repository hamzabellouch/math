import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GateAncestor

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Rerooting
open Classical Finset SimpleGraph
noncomputable section
variable {V α : Type*} [DecidableEq V] [Fintype α] [DecidableEq α]
variable {G₁ G₂ : SimpleGraph V} {root₁ root₂ : V} {A₁ A₂ : α→Finset V}

theorem two_block_rerooting (hG₁ : G₁.IsAcyclic) (hG₂ : G₂.IsAcyclic)
    (g₁ : ∀ p,Gate G₁ root₁ (A₁ p)) (g₂ : ∀ p,Gate G₂ root₂ (A₂ p))
    (hA₂ : ∀ p,ConnectedSet G₂ (A₂ p))
    (J n : ℕ) (hn : n^8 ≤ Fintype.card α)
    (hcap : ∀ x y,G₂.Adj x y → (univ.filter (fun p => x ∈ A₂ p ∧ y ∈ A₂ p)).card ≤ J) :
    ∃ (t : Finset α) (root : V) (g : ∀ p : t,Gate G₂ root (A₂ p.val)) (key : t→ℕ),
      n ≤ (2*J+1)*t.card ∧ (root=root₂ ∨ ∃ p,root=(g₂ p).vertex) ∧
      ∀ p q : t,gateAncestor (fun p : t => g₁ p.val) p q ∨ gateAncestor g p q → key p<key q := by
  by_cases hn0 : n=0
  · refine ⟨∅,root₂,(fun p => g₂ p.val),(fun p => (g₁ p.val).path.length),by simp [hn0],Or.inl rfl,?_⟩
    intro p _ _
    exact (notMem_empty p.val p.property).elim
  have hr₁ := ancestor_trans hG₁ root₁ (fun p => (g₁ p).vertex) (fun p => (g₁ p).path) (fun p => (g₁ p).simple)
  have hr₂ := ancestor_trans hG₂ root₂ (fun p => (g₂ p).vertex) (fun p => (g₂ p).path) (fun p => (g₂ p).simple)
  obtain ⟨c,hcu,hc,hcases⟩ := two_order_extraction (gateAncestor g₁) (gateAncestor g₂)
    hr₁ (ancestor_irrefl root₁ (fun p => (g₁ p).vertex) (fun p => (g₁ p).path))
      hr₂ (ancestor_irrefl root₂ (fun p => (g₂ p).vertex) (fun p => (g₂ p).path)) univ n (by simpa using hn)
  have hcne : c.Nonempty := card_pos.mp (by omega)
  have hcs : n ≤ (2*J+1)*c.card := hc.trans (by nlinarith)
  rcases hcases with ha₁|ha₂|hag|hre
  · refine ⟨c,root₂,(fun p => g₂ p.val),(fun p => (g₂ p.val).path.length),hcs,Or.inl rfl,?_⟩
    intro p q h
    rcases h with h|h
    · exact ((ha₁ p.property q.property (fun he => h.2 (congrArg (fun p => (g₁ p).vertex) he))).1 h).elim
    · exact ancestor_length_lt hG₂ root₂ _ _ (fun p : c => (g₂ p.val).simple) h
  · refine ⟨c,root₂,(fun p => g₂ p.val),(fun p => (g₁ p.val).path.length),hcs,Or.inl rfl,?_⟩
    intro p q h
    rcases h with h|h
    · exact ancestor_length_lt hG₁ root₁ _ _ (fun p : c => (g₁ p.val).simple) h
    · exact ((ha₂ p.property q.property (fun he => h.2 (congrArg (fun p => (g₂ p).vertex) he))).1 h).elim
  · refine ⟨c,root₂,(fun p => g₂ p.val),(fun p => (g₁ p.val).path.length),hcs,Or.inl rfl,?_⟩
    intro p q h
    rcases h with h|h
    · exact ancestor_length_lt hG₁ root₁ _ _ (fun p : c => (g₁ p.val).simple) h
    · have hpq : p.val≠q.val := fun he => h.2 (congrArg (fun p => (g₂ p).vertex) he)
      rcases hag p.property q.property hpq with ha|ha
      · exact ancestor_length_lt hG₁ root₁ _ _ (fun p => (g₁ p).simple) ha.1
      · have hlt := ancestor_length_lt hG₂ root₂ _ _ (fun p : c => (g₂ p.val).simple) h
        have hgt := ancestor_length_lt hG₂ root₂ _ _ (fun p => (g₂ p).simple) ha.2
        omega
  · let : Nonempty c := ⟨⟨hcne.choose,hcne.choose_spec⟩⟩
    have hre' : Chain (Reverse (gateAncestor (fun p : c => g₁ p.val))
        (gateAncestor (fun p : c => g₂ p.val))) univ := by
      intro p _ q _ hpq
      exact hre p.property q.property (fun he => hpq (Subtype.ext he))
    have hcap' (x y : V) (hxy : G₂.Adj x y) :
        (univ.filter (fun p : c => x ∈ A₂ p.val ∧ y ∈ A₂ p.val)).card ≤ J := by
      let u := univ.filter (fun p : c => x ∈ A₂ p.val ∧ y ∈ A₂ p.val)
      calc
        u.card=(u.image Subtype.val).card := (card_image_of_injective _ Subtype.val_injective).symm
        _  ≤  (univ.filter (fun p => x ∈ A₂ p ∧ y ∈ A₂ p)).card := by
          apply card_le_card
          intro p hp
          obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
          exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hq).2⟩
        _  ≤  J := hcap x y hxy
    obtain ⟨root,g,u,hcard,hroot,horder⟩ := reroot_reverse hG₁ hG₂
      (fun p : c => g₁ p.val) (fun p : c => g₂ p.val) (fun p => hA₂ p.val) hre' J hcap'
    let t := u.image Subtype.val
    have htc : t ⊆ c := image_subset_iff.mpr (fun p _ => p.property)
    let e : t→c := fun p => ⟨p.val,htc p.property⟩
    have heu (p : t) : e p ∈ u := by
      obtain ⟨q,hq,he⟩ := mem_image.mp p.property
      have heq : e p=q := Subtype.ext he.symm
      simpa only [heq] using hq
    have htcard : t.card=u.card := card_image_of_injective _ Subtype.val_injective
    refine ⟨t,root,(fun p => g (e p)),(fun p => (g₁ p.val).path.length),?_,?_,?_⟩
    · rw [htcard]
      exact hc.trans (by simpa using hcard)
    · right
      obtain ⟨p,hp⟩ := hroot
      exact ⟨p.val,hp⟩
    · intro p q h
      rcases h with h|h
      · exact ancestor_length_lt hG₁ root₁ _ _ (fun p : t => (g₁ p.val).simple) h
      · exact horder (e p) (heu p) (e q) (heu q) h

end
end OrdinaryCorrelations.Rerooting

end

end OAI
