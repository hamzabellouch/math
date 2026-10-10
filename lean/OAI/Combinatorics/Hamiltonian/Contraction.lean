import OAI.Combinatorics.Hamiltonian.Forest

namespace OAI

/-! Contraction and deletion of finite oriented dual networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def inducedEdges (U : Finset F) : Finset E :=
  Finset.univ.filter fun e => D.tail e ∈ U ∧ D.head e ∈ U

omit [Fintype F] in
@[simp] lemma mem_inducedEdges (U : Finset F) (e : E) :
    e ∈ D.inducedEdges U ↔ D.tail e ∈ U ∧ D.head e ∈ U := by
  simp [inducedEdges]

def inducedNetwork (U : Finset F) : Network U (D.inducedEdges U) where
  tail e := ⟨D.tail e.val,((D.mem_inducedEdges U e.val).mp e.property).1⟩
  head e := ⟨D.head e.val,((D.mem_inducedEdges U e.val).mp e.property).2⟩

omit [Fintype F] in
lemma inducedNetwork_map (U : Finset F) :
    (D.inducedNetwork U).mapVertices Subtype.val =
      D.restrict (Subtype.val : D.inducedEdges U → E) := rfl

lemma inducedNetwork_boundary (U : Finset F) (x : D.inducedEdges U → ℝ) :
    push (Subtype.val : U → F) ((D.inducedNetwork U).boundary x) =
      D.boundary (push Subtype.val x) := by
  rw [← boundary_mapVertices,D.inducedNetwork_map,boundary_restrict]

def regions (U : Finset F) : Network V {e // e ∉ D.inducedEdges U} :=
  N.restrict Subtype.val

abbrev Regions (U : Finset F) := (N.regions D U).Components

def regionQuotient (U : Finset F) : Network (N.Regions D U) (D.inducedEdges U) :=
  (N.mapVertices (N.regions D U).componentMap).restrict Subtype.val

omit [Fintype V] [Fintype F] in
lemma regionQuotient_connected (hN : N.graph.Connected) (U : Finset F) :
    (N.regionQuotient D U).graph.Connected := by
  let H := N.regions D U
  let q := H.componentMap
  let L := N.regionQuotient D U
  have : Nonempty V := hN.nonempty
  have : Nonempty H.Components := Nonempty.map q inferInstance
  apply L.connected_of_kernel_constants
  intro f hf a b
  obtain ⟨a',rfl⟩ := H.componentMap_surjective a
  obtain ⟨b',rfl⟩ := H.componentMap_surjective b
  apply N.gradient_zero_reachable (f := pull q f) _ (hN a' b')
  ext e
  by_cases he : e ∈ D.inducedEdges U
  · exact congrFun hf ⟨e,he⟩
  · exact congrFun (H.gradient_componentMap f) ⟨e,he⟩

omit [Fintype V] in

lemma induced_cycles_eq_regions (h : N.Duality D) (U : Finset F) :
    (D.inducedNetwork U).boundary.ker = (N.regionQuotient D U).gradient.range := by
  let H := N.regions D U
  let q := H.componentMap
  ext x
  constructor
  · intro hx
    have hx' : (D.inducedNetwork U).boundary x = 0 := hx
    have hz : D.boundary (push (Subtype.val : D.inducedEdges U → E) x) = 0 := by
      rw [← D.inducedNetwork_boundary,hx',map_zero]
    obtain ⟨g,hg⟩ : ∃ g, N.gradient g = push (Subtype.val : D.inducedEdges U → E) x := by
      have hh : push (Subtype.val : D.inducedEdges U → E) x ∈ D.boundary.ker := hz
      rw [h.dual_cycles_eq_cuts] at hh
      exact hh
    have hgH : H.gradient g = 0 := by
      ext e
      change N.gradient g e.val = 0
      rw [hg]
      exact push_eq_zero_outside x (by simpa using e.property)
    obtain ⟨f,hf⟩ := H.descends_components g hgH
    refine ⟨f,?_⟩
    change pull (Subtype.val : D.inducedEdges U → E) (N.gradient (pull q f)) = x
    rw [hf,hg,pull_push_injective Subtype.val_injective]
  · rintro ⟨f,rfl⟩
    have hext : push (Subtype.val : D.inducedEdges U → E)
        ((N.regionQuotient D U).gradient f) = N.gradient (pull q f) := by
      ext e
      by_cases he : e ∈ D.inducedEdges U
      · exact push_subtype_apply (D.inducedEdges U) _ ⟨e,he⟩
      · rw [push_eq_zero_outside _ (by simpa using he)]
        exact (congrFun (H.gradient_componentMap f) ⟨e,he⟩).symm
    have hz : push (Subtype.val : U → F)
        ((D.inducedNetwork U).boundary ((N.regionQuotient D U).gradient f)) = 0 := by
      rw [D.inducedNetwork_boundary,hext]
      exact h.dual_conserved_gradient N D _
    have hz' := congrArg (pull (Subtype.val : U → F)) hz
    rw [pull_push_injective Subtype.val_injective,map_zero] at hz'
    exact hz'

omit [Fintype F] in
lemma rank_boundary_le [Nonempty V] :
    Module.finrank ℝ N.boundary.range + 1 ≤ Fintype.card V := by
  have hle : (constant (V := V)).range ≤ N.gradient.ker := by
    rintro _ ⟨c,rfl⟩
    exact N.gradient_const c
  have hi : Function.Injective (constant (V := V)) := by
    intro a b hh
    exact congrFun hh (Classical.choice inferInstance)
  have hk : 1 ≤ Module.finrank ℝ N.gradient.ker := by
    have hh := Submodule.finrank_mono hle
    rwa [LinearMap.finrank_range_of_inj hi,Module.finrank_self] at hh
  have hr : Module.finrank ℝ N.boundary.range = Module.finrank ℝ N.gradient.range := by
    rw [N.gradient_matrix,boundary,Matrix.toLin'_apply',Matrix.toLin'_apply',
      ← Matrix.rank,← Matrix.rank,Matrix.rank_transpose]
  have hh := N.gradient.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hh
  omega

lemma induced_euler_bound (h : N.Duality D) (U : Finset F) (hU : U.Nonempty) :
    (D.inducedEdges U).card + 2 ≤ U.card + Fintype.card (N.Regions D U) := by
  have : Nonempty U := by obtain ⟨u,hu⟩ := hU; exact ⟨⟨u,hu⟩⟩
  have hr := (D.inducedNetwork U).rank_boundary_le
  have hk := (D.inducedNetwork U).boundary.finrank_range_add_finrank_ker
  rw [Module.finrank_pi,Fintype.card_coe] at hk
  rw [N.induced_cycles_eq_regions D h U] at hk
  have ho := (N.regionQuotient D U).rank_gradient (N.regionQuotient_connected D h.connected U)
  simp only [Fintype.card_coe] at hr
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma star_count (hN : N.Simple) (v : V) :
    (N.star v).card = ∑ e, ((if N.tail e = v then 1 else 0) +
      (if N.head e = v then 1 else 0)) := by
  rw [star,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne := hN.loopless e
  by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all [Incident]

lemma weighted_stars (hN : N.Simple) (f : V → ℤ) :
    ∑ v, f v * (N.star v).card = ∑ e, (f (N.tail e) + f (N.head e)) := by
  simp only [N.star_count hN,Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,Finset.mul_sum,mul_add,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [Finset.sum_add_distrib,eq_comm]

def colorSign (black : V → Prop) (v : V) : ℤ := if black v then 1 else -1

omit [Fintype V] [Fintype E] in
lemma colorSign_add (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    colorSign black (N.tail e) + colorSign black (N.head e) = 0 := by
  have he := hc e
  by_cases ht : black (N.tail e) <;> by_cases hh : black (N.head e) <;>
    simp_all [colorSign]

lemma colorSign_sum (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    ∑ v, colorSign black v = 0 := by
  have hs := N.weighted_stars hN (colorSign black)
  have hv : ∀ v, (N.star v).card = 3 := fun v => (N.card_star hN v).trans (h3 v)
  simp only [hv,N.colorSign_add black hc,Finset.sum_const_zero,Nat.cast_ofNat,
    ← Finset.sum_mul] at hs
  omega

def regionShore (U : Finset F) (q : N.Regions D U) : Finset V :=
  Finset.univ.filter fun v => (N.regions D U).componentMap v = q

omit [Fintype F] in
@[simp] lemma mem_regionShore (U : Finset F) (q : N.Regions D U) (v : V) :
    v ∈ N.regionShore D U q ↔ (N.regions D U).componentMap v = q := by
  simp [regionShore]

omit [Fintype F] in
lemma regionShore_nonempty (U : Finset F) (q : N.Regions D U) :
    (N.regionShore D U q).Nonempty := by
  obtain ⟨v,hv⟩ := (N.regions D U).componentMap_surjective q
  exact ⟨v,(N.mem_regionShore D U q v).mpr hv⟩

omit [Fintype F] in
lemma regionShore_off_edge (U : Finset F) (q : N.Regions D U) {e : E}
    (he : e ∉ D.inducedEdges U) :
    N.tail e ∈ N.regionShore D U q ↔ N.head e ∈ N.regionShore D U q := by
  simp only [N.mem_regionShore]
  have hh : (N.regions D U).componentMap (N.tail e) =
      (N.regions D U).componentMap (N.head e) :=
    SimpleGraph.ConnectedComponent.sound ((N.regions D U).edge_reachable ⟨e,he⟩)
  rw [hh]

def rim (U : Finset F) (q : N.Regions D U) : ℕ :=
  ∑ e ∈ D.inducedEdges U, ((if N.tail e ∈ N.regionShore D U q then 1 else 0) +
    (if N.head e ∈ N.regionShore D U q then 1 else 0))

def blackRim (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℕ :=
  ∑ e ∈ D.inducedEdges U, ((if N.tail e ∈ N.regionShore D U q ∧ black (N.tail e) then 1 else 0) +
    (if N.head e ∈ N.regionShore D U q ∧ black (N.head e) then 1 else 0))

def regionBalance (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℤ :=
  ∑ v ∈ N.regionShore D U q, colorSign black v

omit [Fintype F] in
lemma blackRim_le (black : V → Prop) (U : Finset F) (q : N.Regions D U) :
    N.blackRim D black U q ≤ N.rim D U q := by
  apply Finset.sum_le_sum
  intro e _
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;>
    by_cases bt : black (N.tail e) <;> by_cases bh : black (N.head e) <;> simp [ht,hh,bt,bh]

omit [Fintype F] in
lemma region_balance_rim (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) (q : N.Regions D U) :
    3 * N.regionBalance D black U q = 2 * (N.blackRim D black U q : ℤ) - N.rim D U q := by
  let A := N.regionShore D U q
  let f : V → ℤ := fun v => if v ∈ A then colorSign black v else 0
  have hs := N.weighted_stars hN f
  have hv : ∀ v, (N.star v).card = 3 := fun v => (N.card_star hN v).trans (h3 v)
  have hleft : (∑ v, f v * (N.star v).card) = 3 * N.regionBalance D black U q := by
    simp only [hv,Nat.cast_ofNat,← Finset.sum_mul,f]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,regionBalance,A,mul_comm]
  rw [hleft] at hs
  have hreduce : (∑ e, (f (N.tail e) + f (N.head e))) =
      ∑ e ∈ D.inducedEdges U, (f (N.tail e) + f (N.head e)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have heq := N.regionShore_off_edge D U q he
    simp only [f,A,heq]
    split_ifs
    · exact N.colorSign_add black hc e
    · rfl
  rw [hreduce] at hs
  rw [hs]
  simp only [blackRim,rim,Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [f,A,colorSign]
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;>
    by_cases bt : black (N.tail e) <;> by_cases bh : black (N.head e) <;> norm_num [ht,hh,bt,bh]

omit [Fintype F] in
lemma sum_rim (U : Finset F) :
    ∑ q : N.Regions D U, N.rim D U q = 2 * (D.inducedEdges U).card := by
  simp only [rim]
  rw [Finset.sum_comm]
  simp [N.mem_regionShore,Finset.sum_add_distrib,Nat.mul_comm]

omit [Fintype F] in
lemma sum_regionBalance (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) : ∑ q : N.Regions D U, N.regionBalance D black U q = 0 := by
  simp only [regionBalance,regionShore,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact N.colorSign_sum hN h3 black hc

lemma rim_defect (b d : ℕ) (β : ℤ) (hb : b ≤ d) (hd : 4 ≤ d)
    (hβ : 3*β = 2*(b:ℤ) - d) : β ≤ (d:ℤ)-4 := by
  by_cases h4 : d = 4
  · subst d; omega
  by_cases h5 : d = 5
  · subst d; omega
  have h6 : (6:ℤ) ≤ d := by omega
  have hbd : (b:ℤ) ≤ d := by exact_mod_cast hb
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def ThreeEdgeConnected : Prop := ∀ A : Finset V, A.Nonempty → Aᶜ.Nonempty → 3 ≤ (N.cut A).card

def TrivialThreeCuts : Prop := ∀ A : Finset V, (N.cut A).card = 3 → A.card = 1 ∨ Aᶜ.card = 1

omit [Fintype F] in
lemma region_cut_subset (U : Finset F) (q : N.Regions D U) :
    N.cut (N.regionShore D U q) ⊆ D.inducedEdges U := by
  intro e he
  by_contra hn
  have hh := N.regionShore_off_edge D U q hn
  have hc := (N.mem_cut _ _).mp he
  exact hc.elim (fun h => h.2 (hh.mp h.1)) (fun h => h.2 (hh.mpr h.1))

omit [Fintype F] in
lemma rim_cut_count (U : Finset F) (q : N.Regions D U) :
    N.rim D U q = (N.cut (N.regionShore D U q)).card +
      2 * ((D.inducedEdges U).filter fun e =>
        N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q).card := by
  have hcut : N.cut (N.regionShore D U q) =
      (D.inducedEdges U).filter fun e => e ∈ N.cut (N.regionShore D U q) := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun he => ⟨N.region_cut_subset D U q he,he⟩,And.right⟩
  rw [hcut]
  simp only [rim,Finset.card_filter,Finset.mul_sum,← Finset.sum_add_distrib,N.mem_cut]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;> simp [ht,hh]

omit [Fintype F] in
lemma cut_le_rim (U : Finset F) (q : N.Regions D U) :
    (N.cut (N.regionShore D U q)).card ≤ N.rim D U q := by
  rw [N.rim_cut_count]
  omega

omit [Fintype F] in
lemma rim_of_shore_univ (U : Finset F) (q : N.Regions D U)
    (hq : N.regionShore D U q = Finset.univ) :
    N.rim D U q = 2 * (D.inducedEdges U).card := by
  simp [rim,hq,Nat.mul_comm]

omit [Fintype F] in
lemma rim_ge_three (hN : N.ThreeEdgeConnected) (U : Finset F)
    (hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) : 3 ≤ N.rim D U q := by
  by_cases hq : N.regionShore D U q = Finset.univ
  · rw [N.rim_of_shore_univ D U q hq]; omega
  · have hA := N.regionShore_nonempty D U q
    have hAc : (N.regionShore D U q)ᶜ.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      exact hq ((Finset.compl_eq_empty_iff _).mp he)
    exact (hN _ hA hAc).trans (N.cut_le_rim D U q)

omit [Fintype F] in
lemma rim_three_cut (hN : N.ThreeEdgeConnected) (U : Finset F)
    (_hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) (hq : N.rim D U q = 3) :
    (N.cut (N.regionShore D U q)).card = 3 := by
  have hproper : N.regionShore D U q ≠ Finset.univ := by
    intro he
    have hh := N.rim_of_shore_univ D U q he
    omega
  have hAc : (N.regionShore D U q)ᶜ.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hproper ((Finset.compl_eq_empty_iff _).mp he)
  have hl := hN _ (N.regionShore_nonempty D U q) hAc
  have hu := N.cut_le_rim D U q
  omega

omit [Fintype F] in
lemma rim_three_no_internal (hN : N.ThreeEdgeConnected) (U : Finset F)
    (_hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) (hq : N.rim D U q = 3)
    {e : E} (he : e ∈ D.inducedEdges U) :
    ¬(N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) := by
  have hc := N.rim_three_cut D hN U _hm q hq
  have hh := N.rim_cut_count D U q
  have hz : ((D.inducedEdges U).filter fun e =>
      N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  intro hi
  have hhmem : e ∈ (D.inducedEdges U).filter (fun e =>
      N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) :=
    Finset.mem_filter.mpr ⟨he,hi⟩
  rw [hz] at hhmem
  exact Finset.notMem_empty _ hhmem

omit [Fintype F] in
lemma singleton_region_star (hN : N.Simple) (U : Finset F) (q : N.Regions D U)
    {v : V} (hq : N.regionShore D U q = {v}) : N.star v ⊆ D.inducedEdges U := by
  intro e he
  by_contra hn
  have hi := (N.mem_star e v).mp he
  have hh := N.regionShore_off_edge D U q hn
  rw [hq] at hh
  simp only [Finset.mem_singleton] at hh
  exact hN.loopless e (hi.elim (fun hv => hv.trans ((hh.mp hv).symm))
    (fun hv => (hh.mpr hv).trans hv.symm))

lemma star_subset_eq (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    {v w : V} (hvw : N.star v ⊆ N.star w) : v = w := by
  by_contra hne
  have hc : 1 < (N.star v).card := by rw [N.card_star hN,h3 v]; decide
  obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hc
  have ends {e : E} (he : e ∈ N.star v) : s(N.tail e,N.head e) = s(v,w) := by
    have hv := (N.mem_star e v).mp he
    have hw := (N.mem_star e w).mp (hvw he)
    apply Sym2.eq_iff.mpr
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact (hne (hv.symm.trans hw)).elim
    · exact Or.inl ⟨hv,hw⟩
    · exact Or.inr ⟨hw,hv⟩
    · exact (hne (hv.symm.trans hw)).elim
  exact hef (hN.pair_injective ((ends he).trans (ends hf).symm))

omit [Fintype F] in
lemma complement_singleton_root (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (U : Finset F) (root : V)
    (hr : N.star root ⊆ D.inducedEdges U) (q : N.Regions D U)
    (hq : N.rim D U q = 3) {v : V} (hv : (N.regionShore D U q)ᶜ = {v}) : v = root := by
  have hm : 3 ≤ (D.inducedEdges U).card := by
    have hh := Finset.card_le_card hr
    rwa [N.card_star hN,h3 root] at hh
  apply (N.star_subset_eq hN h3 (v := root) (w := v) ?_).symm
  intro e he
  have hn := N.rim_three_no_internal D hcut U hm q hq (hr he)
  rw [N.mem_star]
  have ht : N.tail e ∉ N.regionShore D U q ↔ N.tail e = v := by
    rw [← Finset.mem_compl,hv,Finset.mem_singleton]
  have hh : N.head e ∉ N.regionShore D U q ↔ N.head e = v := by
    rw [← Finset.mem_compl,hv,Finset.mem_singleton]
  rcases not_and_or.mp hn with ht' | hh'
  · exact Or.inl (ht.mp ht')
  · exact Or.inr (hh.mp hh')

end
end Barnette.Network

end OAI
