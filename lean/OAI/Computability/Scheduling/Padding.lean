import OAI.Computability.Scheduling.HierarchySoundness

namespace OAI

section

namespace ThreeMachine

def Instance.order {n : ℕ} (G : Instance n) : Fin n → Fin n → Prop := Relation.TransGen G.edge

theorem Feasible.order {n T : ℕ} {G : Instance n} {time : Fin n → ℕ}
    (h : Feasible G T time) {x y : Fin n} (hxy : G.order x y) : time x < time y := by
  induction hxy with
  | single hxy => exact h.2.2 _ _ hxy
  | tail _ hxy ih => exact ih.trans (h.2.2 _ _ hxy)

def paddedOrder {n : ℕ} (r : Fin n → Fin n → Prop) (m : ℕ) (u v : Fin m) : Prop :=
  ∃ x y : Fin n, u.val = x.val ∧ v.val = y.val ∧ r x y

theorem paddedOrder_trans {n m : ℕ} {r : Fin n → Fin n → Prop}
    (htrans : ∀ ⦃x y z⦄, r x y → r y z → r x z) :
    ∀ ⦃x y z⦄, paddedOrder r m x y → paddedOrder r m y z → paddedOrder r m x z := by
  rintro _ _ _ ⟨a, b, ha, hb, hab⟩ ⟨c, d, hc, hd, hcd⟩
  have he : b = c := Fin.ext (hb.symm.trans hc)
  subst c
  exact ⟨a, d, ha, hd, htrans hab hcd⟩

theorem paddedOrder_irrefl {n m : ℕ} {r : Fin n → Fin n → Prop}
    (hirr : ∀ x, ¬r x x) : ∀ x, ¬paddedOrder r m x x := by
  rintro _ ⟨a, b, ha, hb, hab⟩
  have he : a = b := Fin.ext (ha.symm.trans hb)
  exact hirr a (he ▸ hab)

theorem paddedOrder_castLE {n m : ℕ} {r : Fin n → Fin n → Prop} (hnm : n ≤ m)
    (x y : Fin n) : paddedOrder r m (Fin.castLE hnm x) (Fin.castLE hnm y) ↔ r x y := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have ea : x = a := Fin.ext ha
    have eb : y = b := Fin.ext hb
    simpa only [ea, eb] using hab
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩

namespace Structure

theorem Layout.capacity {J : Type} [Fintype J] (p : Layout J)
    (hfull : 3 ∣ Fintype.card J) (t : ℕ) : (p.slot t).card ≤ 3 := by
  by_cases ht : 1 ≤ t ∧ t ≤ Fintype.card J / 3
  · exact (p.card_slot hfull t ht.1 ht.2).le
  · have he : p.slot t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx' := (p.mem_slot t x).mp hx
      have := p.time_bounds hfull x
      omega
    simp [he]

end Structure

theorem feasible_iff_padded_layout {n T : ℕ} (G : Instance n) (hn : n ≤ 3*T) :
    (∃ time, Feasible G T time) ↔
      ∃ p : Structure.Layout (Fin (3*T)), p.Full (paddedOrder G.order (3*T)) := by
  classical
  constructor
  · rintro ⟨time, htime⟩
    have hcap (t : ℕ) : {x | time x = t}.ncard ≤ 3 := by
      have he : {x | time x = t} = (Finset.univ.filter (fun x => time x = t) : Set (Fin n)) := by
        ext x
        simp
      rw [he, Set.ncard_coe_finset]
      exact htime.2.1 t
    obtain ⟨f, hf, ht⟩ := Structure.exists_slot_embedding time htime.1 hcap
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hn) f
      (Fin.castLE_injective hn) hf
    let p : Structure.Layout (Fin (3*T)) := σ.trans (finCongr (Fintype.card_fin _).symm)
    have hp (x : Fin n) : p.time (Fin.castLE hn x) = time x := by
      change (σ (Fin.castLE hn x)).val / 3 + 1 = time x
      rw [hσ]
      exact ht x
    refine ⟨p, by simp, ?_⟩
    rintro x y ⟨a, b, ha, hb, hab⟩
    have ea : x = Fin.castLE hn a := Fin.ext ha
    have eb : y = Fin.castLE hn b := Fin.ext hb
    rw [ea, eb, hp, hp]
    exact htime.order hab
  · rintro ⟨p, hp⟩
    let time : Fin n → ℕ := fun x => p.time (Fin.castLE hn x)
    refine ⟨time, ?_, ?_, ?_⟩
    · intro x
      have h := p.time_bounds hp.1 (Fin.castLE hn x)
      simpa only [Fintype.card_fin, Nat.mul_div_right _ (by omega : 0 < 3)] using h
    · intro t
      have hcard : (Finset.univ.filter (fun x : Fin n => time x = t)).card ≤ (p.slot t).card := by
        apply Finset.card_le_card_of_injOn (Fin.castLE hn)
        · intro x hx
          exact (p.mem_slot _ _).mpr (Finset.mem_filter.mp hx).2
        · exact (Fin.castLE_injective hn).injOn
      exact hcard.trans (p.capacity hp.1 t)
    · intro x y hxy
      exact hp.2 _ _ ((paddedOrder_castLE hn x y).mpr (.single hxy))

theorem Feasible.size_bound {n T : ℕ} {G : Instance n} {time : Fin n → ℕ}
    (h : Feasible G T time) : n ≤ 3*T := by
  classical
  have hcap (t : ℕ) : {x | time x = t}.ncard ≤ 3 := by
    have he : {x | time x = t} = (Finset.univ.filter (fun x => time x = t) : Set (Fin n)) := by
      ext x
      simp
    rw [he, Set.ncard_coe_finset]
    exact h.2.1 t
  obtain ⟨f, hf, _⟩ := Structure.exists_slot_embedding time h.1 hcap
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

end ThreeMachine

end

end OAI
