import OAI.Combinatorics.SecondNeighborhood.Reindex
import Mathlib.Data.Nat.Find

namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

def induced (r : V → V → Prop) (S : Finset V) : S → S → Prop :=
  fun x y => r x.val y.val

omit [Fintype V] [DecidableEq V] in
theorem isOriented_induced {r : V → V → Prop} (hr : IsOriented r)
    (S : Finset V) : IsOriented (induced r S) where
  loopless x := hr.loopless x.val
  asymmetric hxy hyx := hr.asymmetric hxy hyx

omit [DecidableEq V] in
theorem firstNeighbors_induced_map {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (firstNeighbors (induced r S) v).map
      (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ V) = firstNeighbors r v.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_map.mp hw
    change z.val = w at hzw
    subst w
    have hz' : induced r S v z := mem_firstNeighbors.mp hz
    exact mem_firstNeighbors.mpr hz'
  · intro hw
    have hvw := mem_firstNeighbors.mp hw
    have hwS : w ∈ S := hclosed (mem_image.mpr ⟨v.val, v.property, hvw⟩)
    exact Finset.mem_map.mpr ⟨⟨w, hwS⟩, mem_firstNeighbors.mpr hvw, rfl⟩

theorem secondNeighbors_induced_map {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (secondNeighbors (induced r S) v).map
      (⟨Subtype.val, Subtype.val_injective⟩ : S ↪ V) = secondNeighbors r v.val := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz, hzw⟩ := Finset.mem_map.mp hw
    change z.val = w at hzw
    subst w
    obtain ⟨hne, hnr, u, hvu, huz⟩ := mem_secondNeighbors.mp hz
    apply mem_secondNeighbors.mpr
    refine ⟨?_, hnr, ⟨u.val, hvu, huz⟩⟩
    intro heq
    exact hne (Subtype.ext heq)
  · intro hw
    obtain ⟨hne, hnr, u, hvu, huw⟩ := mem_secondNeighbors.mp hw
    have huS : u ∈ S := hclosed (mem_image.mpr ⟨v.val, v.property, hvu⟩)
    have hwS : w ∈ S := hclosed (mem_image.mpr ⟨u, huS, huw⟩)
    apply Finset.mem_map.mpr
    refine ⟨⟨w, hwS⟩, mem_secondNeighbors.mpr ?_, rfl⟩
    refine ⟨?_, hnr, ⟨⟨u, huS⟩, hvu, huw⟩⟩
    intro heq
    exact hne (congrArg Subtype.val heq)

omit [DecidableEq V] in
theorem card_firstNeighbors_induced {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (firstNeighbors (induced r S) v).card = (firstNeighbors r v.val).card := by
  rw [← firstNeighbors_induced_map hclosed v, Finset.card_map]

theorem card_secondNeighbors_induced {r : V → V → Prop} {S : Finset V}
    (hclosed : image r S ⊆ S) (v : S) :
    (secondNeighbors (induced r S) v).card = (secondNeighbors r v.val).card := by
  rw [← secondNeighbors_induced_map hclosed v, Finset.card_map]

theorem counterexample_induced {r : V → V → Prop} (hbad : Counterexample r)
    {S : Finset V} (hclosed : image r S ⊆ S) : Counterexample (induced r S) := by
  intro v
  rw [card_secondNeighbors_induced hclosed v, card_firstNeighbors_induced hclosed v]
  exact hbad v.val

def OrderMinimal (_r : V → V → Prop) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ s : Fin n → Fin n → Prop,
    IsOriented s → Counterexample s → Fintype.card V ≤ n

theorem OrderMinimal.nonemptyBoundary {r : V → V → Prop}
    (hmin : OrderMinimal r) (hr : IsOriented r) (hbad : Counterexample r) :
    NonemptyBoundary r := by
  classical
  intro S hS hproper
  by_contra hboundary
  have hclosed : image r S ⊆ S := by
    intro w hw
    by_contra hwS
    exact hboundary ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwS⟩⟩
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hpos : 0 < Fintype.card S := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.mpr hS
  have hle := hmin (Fintype.card S) hpos (reindex e (induced r S))
    (isOriented_reindex e (isOriented_induced hr S))
    (counterexample_reindex e (counterexample_induced hbad hclosed))
  have hlt : Fintype.card S < Fintype.card V := by
    rw [Fintype.card_coe]
    exact (Finset.card_lt_iff_ne_univ S).mpr hproper
  exact (not_le_of_gt hlt) hle

theorem NonemptyBoundary.positiveIndegree {r : V → V → Prop}
    (hboundary : NonemptyBoundary r) (hr : IsOriented r)
    (hbad : Counterexample r) : PositiveIndegree r := by
  classical
  intro v
  obtain ⟨w, hvw⟩ := hbad.first_nonempty v
  have hvw' := mem_firstNeighbors.mp hvw
  have hwv : w ≠ v := by
    intro heq
    subst w
    exact hr.loopless v hvw'
  have hnonempty : (Finset.univ.erase v : Finset V).Nonempty :=
    ⟨w, Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩⟩
  have hproper : (Finset.univ.erase v : Finset V) ≠ Finset.univ := by
    intro heq
    have hv : v ∈ (Finset.univ.erase v : Finset V) := heq.symm ▸ Finset.mem_univ v
    exact Finset.notMem_erase v Finset.univ hv
  obtain ⟨x, hx⟩ := hboundary (Finset.univ.erase v) hnonempty hproper
  obtain ⟨hximage, hxnot⟩ := Finset.mem_sdiff.mp hx
  have hxv : x = v := by
    by_contra hne
    exact hxnot (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
  obtain ⟨u, _, hux⟩ := mem_image.mp hximage
  exact ⟨u, hxv ▸ hux⟩

theorem exists_minimal_counterexample [Nonempty V] {r : V → V → Prop}
    (hr : IsOriented r) (hbad : Counterexample r) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : Fin n → Fin n → Prop,
      IsOriented s ∧ Counterexample s ∧ ArcMinimal s ∧
        NonemptyBoundary s ∧ PositiveIndegree s := by
  classical
  let P : ℕ → Prop := fun n => 0 < n ∧ ∃ s : Fin n → Fin n → Prop,
    IsOriented s ∧ Counterexample s
  have hex : ∃ n, P n := by
    refine ⟨Fintype.card V, Fintype.card_pos_iff.mpr inferInstance,
      reindex (Fintype.equivFin V) r, ?_, ?_⟩
    · exact isOriented_reindex (Fintype.equivFin V) hr
    · exact counterexample_reindex (Fintype.equivFin V) hbad
  let n := Nat.find hex
  obtain ⟨hn, t, ht, htb⟩ := Nat.find_spec hex
  have harcs : ∃ a : ℕ, ∃ s : Fin n → Fin n → Prop,
      IsOriented s ∧ Counterexample s ∧ (arcSet s).card = a :=
    ⟨(arcSet t).card, t, ht, htb, rfl⟩
  obtain ⟨s, hs, hsb, hscard⟩ := Nat.find_spec harcs
  have hsmin : ArcMinimal s := by
    intro u hu hub
    rw [hscard]
    exact Nat.find_min' harcs ⟨u, hu, hub, rfl⟩
  have hsorder : OrderMinimal s := by
    intro k hk u hu hub
    simpa only [Fintype.card_fin] using (Nat.find_min' hex ⟨hk, u, hu, hub⟩)
  have hboundary := hsorder.nonemptyBoundary hs hsb
  exact ⟨n, hn, s, hs, hsb, hsmin, hboundary,
    hboundary.positiveIndegree hs hsb⟩

end SeymourSecondNeighborhood

end OAI
