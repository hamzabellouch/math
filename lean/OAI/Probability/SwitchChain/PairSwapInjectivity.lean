import OAI.Probability.SwitchChain.PairTradeSwitch

namespace OAI

noncomputable section
namespace Problem315.PairFiber

variable {V : Type*} [DecidableEq V]

theorem exchange_endpoints_unique (T : Finset V) {u v u' v' : V}
    (hu : u ∈ T) (hv : v ∉ T) (_hu' : u' ∈ T) (_hv' : v' ∉ T)
    (h : insert v (T.erase u) = insert v' (T.erase u')) :
    u = u' ∧ v = v' := by
  have hvv : v = v' := by
    have hmem : v ∈ insert v' (T.erase u') := h ▸ Finset.mem_insert_self v _
    rcases Finset.mem_insert.mp hmem with heq | hmem
    · exact heq
    · exact False.elim (hv (Finset.mem_of_mem_erase hmem))
  have huu : u = u' := by
    by_contra hne
    have huv : u ≠ v := fun heq => hv (heq ▸ hu)
    have hnot : u ∉ insert v (T.erase u) := by simp [huv]
    apply hnot
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, hu⟩)
  exact ⟨huu, hvv⟩

theorem swap_eq_of_map_eq (T : Finset V) {u v u' v' : V}
    (hu : u ∈ T) (hv : v ∉ T) (hu' : u' ∈ T) (hv' : v' ∉ T)
    (h : T.map (Equiv.swap u v).toEmbedding =
      T.map (Equiv.swap u' v').toEmbedding) :
    Equiv.swap u v = Equiv.swap u' v' := by
  rw [map_swap_eq_exchange T u v hu hv, map_swap_eq_exchange T u' v' hu' hv'] at h
  obtain ⟨rfl, rfl⟩ := exchange_endpoints_unique T hu hv hu' hv' h
  rfl

theorem exists_oriented_swap_of_map_ne (T : Finset V) {σ : Equiv.Perm V}
    (hσ : σ.IsSwap) (hne : T.map σ.toEmbedding ≠ T) :
    ∃ u v, u ∈ T ∧ v ∉ T ∧ σ = Equiv.swap u v := by
  obtain ⟨u, v, _, rfl⟩ := hσ
  by_cases hu : u ∈ T
  · by_cases hv : v ∈ T
    · exact False.elim (hne (map_swap_eq_self_of_mem_iff T u v (by simp [hu, hv])))
    · exact ⟨u, v, hu, hv, rfl⟩
  · by_cases hv : v ∈ T
    · exact ⟨v, u, hv, hu, Equiv.swap_comm u v⟩
    · exact False.elim (hne (map_swap_eq_self_of_mem_iff T u v (by simp [hu, hv])))

theorem map_swap_injective_on_nontrivial (T : Finset V) {σ τ : Equiv.Perm V}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hneσ : T.map σ.toEmbedding ≠ T) (hneτ : T.map τ.toEmbedding ≠ T)
    (h : T.map σ.toEmbedding = T.map τ.toEmbedding) : σ = τ := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_oriented_swap_of_map_ne T hσ hneσ
  obtain ⟨u', v', hu', hv', rfl⟩ := exists_oriented_swap_of_map_ne T hτ hneτ
  exact swap_eq_of_map_eq T hu hv hu' hv' h

theorem map_swap_injOn (T : Finset V) :
    Set.InjOn (fun σ : Equiv.Perm V => T.map σ.toEmbedding)
      {σ | σ.IsSwap ∧ T.map σ.toEmbedding ≠ T} := by
  intro σ hσ τ hτ h
  exact map_swap_injective_on_nontrivial T hσ.1 hτ.1 hσ.2 hτ.2 h

end Problem315.PairFiber

end

end OAI
