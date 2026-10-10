import OAI.Combinatorics.Ramsey.CycleClique.Construction.EndpointStructure
import OAI.Combinatorics.Ramsey.CycleClique.Construction.DeletionOrder
import OAI.Combinatorics.Ramsey.CycleClique.Construction.AttachmentResidual
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ResidualPaths

namespace OAI

/-! The full prescribed-length coloured-path lemma of manuscript Section 3. -/

namespace CycleClique.Construction
private noncomputable def indexedSupport {V : Type*} {r : ℕ}
    (f : Fin (r + 1) → V) : Finset V := by
  classical
  exact Finset.univ.image f

private theorem mem_indexedSupport {V : Type*} {r : ℕ} {f : Fin (r + 1) → V} {v : V} :
    v ∈ indexedSupport f ↔ ∃ i, f i = v := by
  classical
  simp [indexedSupport]

private theorem indexedSupport_range {V : Type*} {r : ℕ} (f : Fin (r + 1) → V) :
    Set.range f = (indexedSupport f : Set V) := by
  ext v
  exact mem_indexedSupport.symm

private theorem indexedSupport_card {V : Type*} {r : ℕ} {f : Fin (r + 1) → V}
    (hf : Function.Injective f) : (indexedSupport f).card = r + 1 := by
  classical
  rw [indexedSupport, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

/-- Prescribed-length paths with differently coloured endpoints. -/
theorem colored_path_prescribed_length {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {s : ℕ} (hs : 4 ≤ s)
    (hconn : H.Connected) (hnonbip : ¬ H.IsBipartite) (hno : H.cliqueNum < s)
    (hdegree : ∀ v, s ≤ (H.neighborSet v).ncard)
    (hpair : ∀ a b, a ≠ b → ¬ H.Adj a b →
      2 * s ≤ (closedNeighborhood H {a, b}).card)
    (χ : V → Fin 2) (hnonconstant : ∃ a b, χ a ≠ χ b)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓmax : ℓ ≤ 2 * s - 2) :
    ∃ g : Fin (ℓ + 1) → V, IsIndexedPath H g ∧ χ (g 0) ≠ χ (g (Fin.last ℓ)) := by
  classical
  by_contra hnone
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ :=
    differently_colored_common_neighbors hconn hnonbip χ hnonconstant
  let D := H.induce {v | v ≠ y ∧ v ≠ z}
  let x' : {v : V | v ≠ y ∧ v ≠ z} := ⟨x, hxy.ne, hxz.ne⟩
  let C := D.connectedComponentMk x'
  let U := componentVertices C
  have hxU : x ∈ U := mem_componentVertices.mpr
    ⟨⟨x', SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩, rfl⟩
  obtain ⟨hyU, hzU⟩ := deleted_not_componentVertices C
  change y ∉ U at hyU
  change z ∉ U at hzU
  have hUavoid : ∀ a ∈ U, a ≠ y ∧ a ≠ z := fun a ha =>
    ⟨ne_of_mem_of_not_mem ha hyU, ne_of_mem_of_not_mem ha hzU⟩
  have hcoverU : ∀ a ∈ U, ∀ b, H.Adj a b → b ∈ U ∨ b = y ∨ b = z := by
    intro a ha b hab
    exact componentVertices_neighbor_cover C ha hab
  have hUconn : (H.induce (U : Set V)).Connected := componentVertices_connected C
  obtain ⟨r, f, hf, hstart, hfU, hmax⟩ := exists_longest_path_in H U hxU
  let W := indexedSupport f
  have hWcard : W.card = r + 1 := indexedSupport_card hf.1
  have hWU : W ⊆ U := by
    intro v hv
    obtain ⟨i, rfl⟩ := mem_indexedSupport.mp hv
    exact hfU i
  have hspanning : IsSpanningPath H x W f := ⟨hf.1, hf.2, hstart, indexedSupport_range f⟩
  have havoid : ∀ i, f i ≠ y ∧ f i ≠ z := fun i => hUavoid _ (hfU i)
  have hrshort := no_colored_path_start_bound hxy hxz χ hyz hℓ hnone hf hstart havoid
  have hshort : W.card + 2 < 2 * s := by omega
  let E := pathEnds H x W r
  have hstructure := endpoint_structure hs hno hdegree hpair hyU hzU hWU hcoverU
    hspanning hWcard hshort hmax
  obtain ⟨hEclique, hElower, hEupper, u, huU, huE, htwo, hfull, w, hw, hwy, hwz⟩ := hstructure
  change H.IsClique (E : Set V) at hEclique
  change s - 2 ≤ E.card at hElower
  change E.card ≤ s - 1 at hEupper
  change u ∈ U at huU
  change u ∉ E at huE
  change w ∈ E at hw
  have hEU : E ⊆ U := (pathEnds_subset H x W r).trans hWU
  have hattach : ∀ e ∈ E, ∀ v ∈ U, H.Adj e v → v ∉ E → v = u := by
    intro e he v hv hev hvE
    rcases hfull e he v hev with hv' | hvu | rfl | rfl
    · exact False.elim (hvE hv')
    · exact hvu
    · exact False.elim (hyU hv)
    · exact False.elim (hzU hv)
  have hUnotclique := not_clique_of_two_deleted_neighborhoods
    ⟨x, hxU⟩ hyU hno (fun v _ => hdegree v) hcoverU
  have hUorder := two_deleted_component_order hUnotclique hcoverU hpair
  let T := U \ E
  have hTset : (T : Set V) = {v | v ∈ U ∧ v ∉ E} := by ext v; simp [T]
  have hTsum : T.card + E.card = U.card := Finset.card_sdiff_add_card_eq_card hEU
  have hTcard : 2 ≤ T.card := by omega
  have huT : u ∈ T := Finset.mem_sdiff.mpr ⟨huU, huE⟩
  have hTconn : (H.induce (T : Set V)).Connected := by
    rw [hTset]
    exact connected_induce_difference_single_attachment hUconn huU huE hattach
  obtain ⟨q, g, hg, hgstart, hgT, hgmax⟩ := exists_longest_path_in H T huT
  have hq : 1 ≤ q := restricted_longest_nontrivial hTconn hTcard huT hgmax
  let R := indexedSupport g
  let v := g (Fin.last q)
  have hRcard : R.card = q + 1 := indexedSupport_card hg.1
  have hRT : R ⊆ T := by
    intro a ha
    obtain ⟨i, rfl⟩ := mem_indexedSupport.mp ha
    exact hgT i
  have hvR : v ∈ R := mem_indexedSupport.mpr ⟨Fin.last q, rfl⟩
  have huR : u ∈ R := mem_indexedSupport.mpr ⟨0, hgstart⟩
  have hvU : v ∈ U := (Finset.mem_sdiff.mp (hRT hvR)).1
  have hvE : v ∉ E := (Finset.mem_sdiff.mp (hRT hvR)).2
  have hvu : v ≠ u := by
    intro heq
    have hidx := hg.1 (heq.trans hgstart.symm)
    have hval := congrArg Fin.val hidx
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  have hspanningR : IsSpanningPath H u R g :=
    ⟨hg.1, hg.2, hgstart, indexedSupport_range g⟩
  have hvEnd : v ∈ pathEnds H u R q := mem_pathEnds.mpr ⟨g, hspanningR, rfl⟩
  have hcoverv : ∀ a, H.Adj v a → a ∈ R ∨ a = y ∨ a = z := by
    intro a hva
    rcases hcoverU v hvU a hva with haU | hay | haz
    · have haE : a ∉ E := by
        intro ha
        exact hvu (hattach a ha v hvU hva.symm hvE)
      have haT : a ∈ T := Finset.mem_sdiff.mpr ⟨haU, haE⟩
      exact Or.inl (restricted_endpoint_neighbors hRT hgmax hvEnd a haT hva)
    · exact Or.inr (Or.inl hay)
    · exact Or.inr (Or.inr haz)
  have hvw : v ≠ w := (ne_of_mem_of_not_mem hw hvE).symm
  have hnonadj : ¬ H.Adj v w := fun h => hvu (hattach w hw v hvU h.symm hvE)
  have hcombined := endpoint_residual_order huR hvR hw hcoverv (hfull w hw)
    (hpair v w hvw hnonadj)
  change 2 * s - 2 ≤ E.card + R.card at hcombined
  have hRlist := indexedPath_ofFn_chain hg
  have hRhead : (List.ofFn g).head? = some u := by rw [List.ofFn_succ]; simp [hgstart]
  have hRmem : ∀ a ∈ List.ofFn g, a ∈ R := by
    intro a ha
    exact mem_indexedSupport.mpr ((List.mem_ofFn' g a).mp ha)
  have hRoutside : ∀ a ∈ List.ofFn g, a ∉ E := by
    intro a ha
    exact (Finset.mem_sdiff.mp (hRT (hRmem a ha))).2
  obtain ⟨L, hL, hLchain, hLhead, hLlen, hLmem⟩ := clique_join_remaining_path
    hEclique hw htwo (List.ofFn g) hRlist.1 hRlist.2 hRhead hRoutside
  have hLavoid : ∀ a ∈ L, a ≠ y ∧ a ≠ z := by
    intro a ha
    have haU : a ∈ U := by
      rcases hLmem a ha with haE | haR
      · exact hEU haE
      · exact (Finset.mem_sdiff.mp (hRT (hRmem a haR))).1
    exact hUavoid a haU
  have hLshort := no_colored_path_list_bound hwy hwz χ hyz hℓ hnone hL hLchain hLhead hLavoid
  simp only [List.length_ofFn] at hLlen
  omega

end CycleClique.Construction

end OAI
