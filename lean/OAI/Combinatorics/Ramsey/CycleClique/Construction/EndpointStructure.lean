import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointDegreeCover
import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointAllowedAttachment

namespace OAI

/-! Assembling the endpoint clique and its single attachment. -/

namespace CycleClique.Construction
theorem endpoint_structure {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {U W : Finset V} {x y z : V} {r s : ℕ}
    (hs : 4 ≤ s) (hno : H.cliqueNum < s)
    (hdegree : ∀ v, s ≤ (H.neighborSet v).ncard)
    (hexpand : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).card)
    (hyU : y ∉ U) (hzU : z ∉ U) (hWU : W ⊆ U)
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    {f : Fin (r + 1) → V} (hf : IsSpanningPath H x W f)
    (hcard : W.card = r + 1) (hshort : W.card + 2 < 2 * s)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r) :
    let E := pathEnds H x W r
    H.IsClique (E : Set V) ∧ s - 2 ≤ E.card ∧ E.card ≤ s - 1 ∧
      ∃ u ∈ U, u ∉ E ∧
        (∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ H.Adj a u ∧ H.Adj b u) ∧
        (∀ e ∈ E, ∀ v, H.Adj e v → v ∈ E ∨ v = u ∨ v = y ∨ v = z) ∧
        ∃ w ∈ E, H.Adj w y ∧ H.Adj w z := by
  classical
  let E := pathEnds H x W r
  have hEW : E ⊆ W := pathEnds_subset H x W r
  have hEU : E ⊆ U := hEW.trans hWU
  have hyE : y ∉ E := fun hy => hyU (hEU hy)
  have hzE : z ∉ E := fun hz => hzU (hEU hz)
  have he : f (Fin.last r) ∈ E := mem_pathEnds.mpr ⟨f, hf, rfl⟩
  have hcoverE : ∀ e ∈ E, ∀ v, H.Adj e v → v ∈ W ∨ v = y ∨ v = z :=
    restricted_endpoint_neighbor_cover hWU hcover hmax
  have hclique : H.IsClique (E : Set V) := by
    apply clique_of_endpoint_neighbor_cover (s := s) hEW
      (Z := {y, z})
    · intro e he v hev
      rcases hcoverE e he v hev with hv | rfl | rfl
      · exact Finset.mem_union_left _ hv
      · simp
      · simp
    · have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
      omega
    · exact hexpand
  have hupper : E.card ≤ s - 1 := by
    have := hclique.card_le_cliqueNum
    omega
  have hlower : s - 2 ≤ E.card := by
    have hbound := endpoint_degree_le_card_add_two he (hcoverE _ he)
    change (H.neighborSet (f (Fin.last r))).ncard ≤ E.card + 2 at hbound
    have hlow := hdegree (f (Fin.last r))
    omega
  have hr : 1 ≤ r := by
    have hbound := Finset.card_le_card hEW
    omega
  obtain ⟨t, hfinal⟩ := pathEnds_final_segment hr hf hclique
  let u := f t.castSucc
  let w₀ := f t.succ
  have huU : u ∈ U := by
    apply hWU
    change f t.castSucc ∈ (W : Set V)
    rw [← hf.2.2.2]
    exact ⟨t.castSucc, rfl⟩
  have huE : u ∉ E := by
    intro hu
    have h := (hfinal t.castSucc).mp hu
    simp only [Fin.val_castSucc] at h
    omega
  have hw₀ : w₀ ∈ E := (hfinal t.succ).mpr (by simp)
  have huw₀ : H.Adj u w₀ := hf.2.1 t
  have hpartial : ∀ e ∈ E, e ≠ w₀ → ∀ v, H.Adj e v →
      v ∈ (E.erase e) ∪ {u, y, z} := by
    intro e he hne v hev
    rcases hcoverE e he v hev with hvW | rfl | rfl
    · rcases partial_endpoint_attachment_in_W hf t hfinal hclique he hne hvW hev with hvE | hveq
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hev.ne.symm, hvE⟩)
      · subst v
        exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · simp
    · simp
  have hzero : ¬ H.Adj w₀ y → ¬ H.Adj w₀ z → (H.neighborSet w₀).ncard ≤ E.card := by
    intro hny hnz
    apply endpoint_degree_le hw₀
    intro v hwv
    rcases hcoverE w₀ hw₀ v hwv with hv | rfl | rfl
    · exact hv
    · exact False.elim (hny hwv)
    · exact False.elim (hnz hwv)
  have hsecond := endpoint_second_attachment hs ⟨hlower, hupper⟩ hclique hno
    hyE hzE hw₀ (fun e _ => hdegree e) hpartial hzero
  have hfull : ∀ e ∈ E, ∀ v, H.Adj e v → v ∈ E ∨ v = u ∨ v = y ∨ v = z := by
    intro e he v hev
    rcases hcoverE e he v hev with hvW | hvy | hvz
    · rcases full_endpoint_attachment_in_W hf t hfinal hclique hsecond he hvW hev with hv | hvu
      · exact Or.inl hv
      · exact Or.inr (Or.inl hvu)
    · exact Or.inr (Or.inr (Or.inl hvy))
    · exact Or.inr (Or.inr (Or.inr hvz))
  have hfull' : ∀ e ∈ E, ∀ v, H.Adj e v → v ∈ (E.erase e) ∪ {u, y, z} := by
    intro e he v hev
    rcases hfull e he v hev with hv | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hev.ne.symm, hv⟩)
    · simp
    · simp
    · simp
  have hcommon := endpoint_common_deleted_neighbor hs ⟨hlower, hupper⟩ hclique hno
    huE (fun e _ => hdegree e) hfull'
  obtain ⟨b, hb, hbne, hub⟩ := hsecond
  exact ⟨hclique, hlower, hupper, u, huU, huE,
    ⟨w₀, hw₀, b, hb, hbne.symm, huw₀.symm, hub.symm⟩, hfull, hcommon⟩

end CycleClique.Construction

end OAI
