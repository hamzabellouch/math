import Mathlib
import OAI.GroupTheory.FiniteType.OrderChainsOnSet

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderListChains
variable (P : Type*)
noncomputable def vertexSupport (c : Chain P) : Finset P := by
  classical
  exact c.support.biUnion (fun s => (list P s).toFinset)
lemma mem_vertexSupport {c : Chain P} {x : P} : x ∈ vertexSupport P c ↔
    ∃ s ∈ c.support, x ∈ vertices P s := by
  classical
  simp only [vertexSupport,Finset.mem_biUnion,List.mem_toFinset,mem_list]
end OrderListChains

namespace OrderChains
section
open OrderListChains
variable (P : Type*) [PartialOrder P]
theorem raise_rank_step (r : P → ℕ) (hr : StrictMono r) (D : Set P) (m N : ℕ)
    (hup : ∀ a ∈ D, r a = m → ∃ x ∈ D, a < x)
    (hupper : ∀ a ∈ D, r a = m → ∀ k ≤ N, ExactSet P {x | x ∈ D ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P)
    (hc : c ∈ onSet P {x | x ∈ D ∧ m ≤ r x}) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P {x | x ∈ D ∧ m+1 ≤ r x} ∧ Homogeneous P n c' ∧
      boundary P c' = 0 ∧ augmentation P c' = 0 ∧ d ∈ onSet P D ∧
      Homogeneous P (n+1) d ∧ boundary P d = c-c' := by
  classical
  let T := (vertexSupport P c).filter (fun x => r x = m)
  let U : Set P := {x | x ∈ D ∧ m+1 ≤ r x} ∪ (T : Set P)
  have hT (a : P) (ha : a ∈ T) : a ∈ D ∧ r a = m := by
    obtain ⟨hav,har⟩ := Finset.mem_filter.mp ha
    obtain ⟨s,hs,has⟩ := (mem_vertexSupport P).mp hav
    exact ⟨((hc hs).2 has).1,har⟩
  have hU (x : P) (hx : x ∈ U) : x ∈ D ∧ m ≤ r x := by
    rcases hx with hx | hx
    · exact ⟨hx.1,(Nat.le_succ m).trans hx.2⟩
    · exact ⟨(hT x hx).1,by rw [(hT x hx).2]⟩
  have hcU : c ∈ onSet P U := by
    intro s hs
    refine ⟨(hc hs).1,?_⟩
    intro x hx
    have hcx := (hc hs).2 hx
    by_cases he : r x = m
    · exact Or.inr (Finset.mem_filter.mpr ⟨(mem_vertexSupport P).mpr ⟨s,hs,hx⟩,he⟩)
    · exact Or.inl ⟨hcx.1,by have hh : m ≤ r x := hcx.2; omega⟩
  have hset (a : P) (ha : a ∈ T) :
      {x | x ∈ U ∧ a < x} = {x | x ∈ D ∧ a < x} := by
    ext x
    refine ⟨fun hx => ⟨(hU x hx.1).1,hx.2⟩,fun hx => ⟨?_,hx.2⟩⟩
    have hh := hr hx.2
    have he := (hT a ha).2
    exact Or.inl ⟨hx.1,by omega⟩
  obtain ⟨c',d,hc',hn',hd',ha',hD,hDn,hdd⟩ := delete_finite_minimal P U T N
    (fun _ ha => Or.inr ha)
    (fun a ha x hx hxa => by
      apply le_antisymm hxa
      by_contra hnle
      have hlt : x < a := lt_of_le_not_ge hxa hnle
      have hrr := hr hlt
      have hlow := (hU x hx).2
      have hea := (hT a ha).2
      omega)
    (fun a ha => by
      obtain ⟨x,hx,hax⟩ := hup a (hT a ha).1 (hT a ha).2
      have he : x ∈ {x | x ∈ U ∧ a < x} := by rw [hset a ha]; exact ⟨hx,hax⟩
      exact ⟨x,he.1,he.2⟩)
    (fun a ha k hk => by rw [hset a ha]; exact hupper a (hT a ha).1 (hT a ha).2 k hk)
    hnN c hcU hn hd ha
  refine ⟨c',d,onSet_mono P ?_ hc',hn',hd',ha',onSet_mono P (fun x hx => (hU x hx).1) hD,hDn,hdd⟩
  intro x hx
  rcases hx.1 with hxU | hxT
  · exact hxU
  · exact False.elim (hx.2 hxT)

theorem raise_rank (r : P → ℕ) (hr : StrictMono r) (D : Set P) (M N : ℕ)
    (hup : ∀ a ∈ D, r a < M → ∃ x ∈ D, a < x)
    (hupper : ∀ a ∈ D, r a < M → ∀ k ≤ N, ExactSet P {x | x ∈ D ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P D) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P {x | x ∈ D ∧ M ≤ r x} ∧ Homogeneous P n c' ∧
      boundary P c' = 0 ∧ augmentation P c' = 0 ∧ d ∈ onSet P D ∧
      Homogeneous P (n+1) d ∧ boundary P d = c-c' := by
  have h : ∀ j ≤ M, ∃ c' d : Chain P, c' ∈ onSet P {x | x ∈ D ∧ j ≤ r x} ∧
      Homogeneous P n c' ∧ boundary P c' = 0 ∧ augmentation P c' = 0 ∧ d ∈ onSet P D ∧
      Homogeneous P (n+1) d ∧ boundary P d = c-c' := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨c,0,onSet_mono P (V := {x | x ∈ D ∧ 0 ≤ r x}) (fun x hx => ⟨hx,Nat.zero_le _⟩) hc,hn,hd,ha,
        (onSet P D).zero_mem,supported_zero P _,?_⟩
      simp
    | succ j ih =>
      intro hj
      obtain ⟨cj,dj,hcj,hnj,hdj,haj,hDj,hDnj,hddj⟩ := ih (by omega)
      obtain ⟨c',d',hc',hn',hd',ha',hD',hDn',hdd'⟩ := raise_rank_step P r hr D j N
        (fun a ha hr => hup a ha (by omega))
        (fun a ha hr k hk => hupper a ha (by omega) k hk) hnN cj hcj hnj hdj haj
      refine ⟨c',dj+d',hc',hn',hd',ha',(onSet P D).add_mem hDj hD',
        supported_add P hDnj hDn',?_⟩
      rw [map_add,hddj,hdd']
      abel
  exact h M le_rfl
end

section
open OrderListChains
variable (P : Type*) [Preorder P] {Q : Type*} [Preorder Q]

theorem exactIn_of_upper_comparison (i : Q →o P) (r : P →o Q)
    (hir : ∀ x, x ≤ i (r x)) {n : ℕ} (h : ExactIn Q n) : ExactIn P n := by
  intro c hc hn hd ha
  have hrd : boundary Q (mapChain P r c) = 0 := by rw [boundary_mapChain,hd,map_zero]
  have hra : augmentation Q (mapChain P r c) = 0 := by rw [augmentation_mapChain,ha]
  obtain ⟨d,hdQ,hdn,hdd⟩ := h (mapChain P r c) (map_mem P r hc) (map_degree P r hn) hrd hra
  let f := i.comp r
  refine ⟨mapChain Q i d + comparison P OrderHom.id f c,
    (module P).add_mem (map_mem Q i hdQ) (comparison_mem P OrderHom.id f hir hc),
    supported_add P (map_degree Q i hdn) (comparison_degree P OrderHom.id f hn),?_⟩
  have hH := comparison_boundary P OrderHom.id f c
  rw [hd,map_zero,add_zero] at hH
  rw [map_add,boundary_mapChain,hdd,hH,mapChain_comp]
  have he : mapChain P (OrderHom.id : P →o P) c = c := mapChain_id P c
  rw [he]
  change mapChain P (i ∘ r) c + (c - mapChain P (i ∘ r) c) = c
  abel

theorem exactIn_of_bottom (b : P) (hb : ∀ x, b ≤ x) (n : ℕ) : ExactIn P n := by
  let i : PUnit.{1} →o P := ⟨fun _ => b,fun _ _ _ => le_rfl⟩
  let r : P →o PUnit.{1} := ⟨fun _ => PUnit.unit,fun _ _ _ => le_rfl⟩
  exact exactIn_of_comparison P i r hb (exactIn_of_top _ PUnit.unit (fun _ => le_rfl) n)

theorem carrier_section (p : Q →o P) (N : ℕ)
    (hne : ∀ a : P, ∃ q : Q, p q ≤ a)
    (hex : ∀ a : P, ∀ k ≤ N, ExactSet Q {q | p q ≤ a} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ module P)
    (hn : Homogeneous P n c) (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ z : Chain Q, ∃ d : Chain P, z ∈ module Q ∧ Homogeneous Q n z ∧
      boundary Q z = 0 ∧ augmentation Q z = 0 ∧ d ∈ module P ∧
      Homogeneous P (n+1) d ∧ boundary P d = c - mapChain Q p z := by
  classical
  let K : Simplex P → Set Q := fun s => {q | p q ≤ s.1}
  let L : Simplex P → Set P := fun s => {x | x ≤ s.1}
  let point : Simplex P → Chain Q := fun s => vertex Q ((hne s.1).choose)
  let fill := fun s k z => cycleFill Q (K s) k z
  let F := OrderBasedComplex.chosenExtend (based P) point fill
  have hvalid : ∀ s t, Descending P s → t ∈ (boundary P (Finsupp.single s 1)).support →
      Descending P t := fun _ _ hs ht => hs.boundary P ht
  have hface : ∀ s t, Descending P s → t ∈ (boundary P (Finsupp.single s 1)).support →
      t.1 ≤ s.1 := fun s t hs ht => hs.le_head P (boundary_vertices P s t ht (head_mem_vertices P t))
  have hpoint (s : Simplex P) (_ : Descending P s) : point s ∈ onSet Q (K s) ∧
      point s ∈ degreeModule Q 0 ∧ boundary Q (point s) = 0 ∧ augmentation Q (point s) = 1 := by
    refine ⟨?_,?_,boundary_vertex Q _,augmentation_vertex Q _⟩
    · apply supported_single
      exact ⟨List.pairwise_singleton _ _,by
        rw [vertices_vertex]
        exact Set.singleton_subset_iff.mpr (hne s.1).choose_spec⟩
    · exact supported_single Q (P := fun t => degree Q t = 0) rfl 1
  have hfill (s : Simplex P) (_ : Descending P s) (k : ℕ) (hk : k ≤ N) (z : Chain Q)
      (hz : z ∈ onSet Q (K s)) (hzdeg : z ∈ degreeModule Q k)
      (hzd : boundary Q z = 0) (hza : augmentation Q z = 0) :=
    cycleFill_spec Q (hex s.1 k hk) hz hzdeg hzd hza
  have hF (s : Simplex P) (hs : Descending P s) (hdeg : degree P s ≤ N+1) :
      F (Finsupp.single s 1) ∈ onSet Q (K s) ∧
      F (Finsupp.single s 1) ∈ degreeModule Q (degree P s) ∧
      boundary Q (F (Finsupp.single s 1)) = F (boundary P (Finsupp.single s 1)) ∧
      augmentation Q (F (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact OrderBasedComplex.chosen_spec (based P) point fill (boundary Q) (augmentation Q)
      (degreeModule Q) (Descending P) (fun s => onSet Q (K s)) N hvalid
      (fun s t hs ht => onSet_mono Q (fun _ hx => hx.trans (hface s t hs ht))) hpoint hfill s hs hdeg
  let G := (mapChain Q p).comp F
  have hG (s : Simplex P) (hs : Descending P s) (hdeg : degree P s ≤ N) :
      G (Finsupp.single s 1) ∈ onSet P (L s) ∧
      G (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P (G (Finsupp.single s 1)) = G (boundary P (Finsupp.single s 1)) ∧
      augmentation P (G (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    have hh := hF s hs (by omega)
    refine ⟨map_onSet Q p (fun q hq => hq) (fun _ _ _ _ hxy => p.monotone hxy) hh.1,
      map_degree Q p hh.2.1,?_,?_⟩
    · change boundary P (mapChain Q p _) = mapChain Q p _
      rw [boundary_mapChain,hh.2.2.1]
    · change augmentation P (mapChain Q p _) = _
      rw [augmentation_mapChain,hh.2.2.2]
  let fillL := fun s k z => cycleFill P (L s) k z
  let H := OrderBasedComplex.chosenHomotopy (based P) fillL LinearMap.id G
  have hI (s : Simplex P) (hs : Descending P s) (_ : degree P s ≤ N) :
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ onSet P (L s) ∧
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) =
        (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (boundary P (Finsupp.single s 1)) ∧
      augmentation P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact ⟨supported_single P ⟨hs,fun _ hx => hs.le_head P hx⟩ 1,
      supported_single P (P := fun t => degree P t = degree P s) rfl 1,rfl,rfl⟩
  have hH (s : Simplex P) (hs : Descending P s) (hdeg : degree P s ≤ N) :
      H (Finsupp.single s 1) ∈ onSet P (L s) ∧
      H (Finsupp.single s 1) ∈ degreeModule P (degree P s+1) ∧
      boundary P (H (Finsupp.single s 1)) + H (boundary P (Finsupp.single s 1)) =
        Finsupp.single s 1 - G (Finsupp.single s 1) ∧
      augmentation P (H (Finsupp.single s 1)) = 0 := by
    apply OrderBasedComplex.chosenHomotopy_spec (based P) fillL LinearMap.id G (boundary P)
      (augmentation P) (degreeModule P) (Descending P) (fun s => onSet P (L s)) N hvalid
      (fun s t hs ht => onSet_mono P (fun _ hx => hx.trans (hface s t hs ht))) hI hG ?_ s hs hdeg
    intro t ht k hk z hz hzdeg hzd hza
    exact cycleFill_spec P (exactSet_of_top P (U := L t) t.1 le_rfl (fun _ hx => hx) k) hz hzdeg hzd hza
  have hsd (s : Simplex P) (hs : s ∈ c.support) : degree P s ≤ N := (hn s hs).le.trans hnN
  refine ⟨F c,H c,?_,?_,?_,?_,?_,?_,?_⟩
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_le_module Q _ (hF s (hc hs) (by have hh := hsd s hs; omega)).1
  · apply OrderBasedComplex.map_mem_of_support F (degreeModule Q n)
    intro s hs
    rw [← hn s hs]
    exact (hF s (hc hs) (by have hh := hsd s hs; omega)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary Q).comp F) (F.comp (boundary P)) c
      (fun s hs => (hF s (hc hs) (by have hh := hsd s hs; omega)).2.2.1)
    simpa only [LinearMap.comp_apply,hd,map_zero] using he
  · have he := OrderBasedComplex.linear_eq_on_support ((augmentation Q).comp F) (augmentation P) c
      (fun s hs => (hF s (hc hs) (by have hh := hsd s hs; omega)).2.2.2)
    simpa only [LinearMap.comp_apply,ha] using he
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_le_module P _ (hH s (hc hs) (hsd s hs)).1
  · apply OrderBasedComplex.map_mem_of_support H (degreeModule P (n+1))
    intro s hs
    rw [← hn s hs]
    exact (hH s (hc hs) (hsd s hs)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary P).comp H+H.comp (boundary P))
      (LinearMap.id-G) c (fun s hs => (hH s (hc hs) (hsd s hs)).2.2.1)
    change boundary P (H c) = c - G c
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,hd,map_zero,add_zero,
      LinearMap.sub_apply,LinearMap.id_apply] using he
end

section
open OrderListChains
variable (P : Type*) [Preorder P]
theorem carrier_fill (U V : Set P) (K L : Simplex P → Set P) (N : ℕ)
    (hKne : ∀ s, Descending P s → vertices P s ⊆ U → (K s).Nonempty)
    (hKV : ∀ s, Descending P s → vertices P s ⊆ U → K s ⊆ V)
    (hLU : ∀ s, Descending P s → vertices P s ⊆ U → L s ⊆ U)
    (hKL : ∀ s, Descending P s → vertices P s ⊆ U → K s ⊆ L s)
    (hself : ∀ s, Descending P s → vertices P s ⊆ U → vertices P s ⊆ L s)
    (hfaceK : ∀ s t, Descending P s → vertices P s ⊆ U →
      t ∈ (boundary P (Finsupp.single s 1)).support → K t ⊆ K s)
    (hfaceL : ∀ s t, Descending P s → vertices P s ⊆ U →
      t ∈ (boundary P (Finsupp.single s 1)).support → L t ⊆ L s)
    (hKexact : ∀ s, Descending P s → vertices P s ⊆ U → ∀ k ≤ N, ExactSet P (K s) k)
    (hLexact : ∀ s, Descending P s → vertices P s ⊆ U → ∀ k ≤ N, ExactSet P (L s) k)
    (hVU : V ⊆ U)
    (hLV : ∀ s, Descending P s → vertices P s ⊆ V → L s ⊆ V)
    {n : ℕ} (hnN : n ≤ N) (c b : Chain P)
    (hcV : c ∈ onSet P V) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0)
    (hb : b ∈ onSet P U) (hbn : Homogeneous P (n+1) b) (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P V ∧ Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  classical
  have _ := hLU
  have _ := ha
  have hc : c ∈ onSet P U := onSet_mono P hVU hcV
  let valid : Simplex P → Prop := fun s => Descending P s ∧ vertices P s ⊆ U
  let p : Simplex P → P := fun s => if h : valid s then (hKne s h.1 h.2).choose else s.1
  let point : Simplex P → Chain P := fun s => vertex P (p s)
  let fill := fun s k z => cycleFill P (K s) k z
  let F := OrderBasedComplex.chosenExtend (based P) point fill
  have hvalid : ∀ s t, valid s → t ∈ (boundary P (Finsupp.single s 1)).support → valid t := by
    intro s t hs ht
    exact ⟨hs.1.boundary P ht,(boundary_vertices P s t ht).trans hs.2⟩
  have hpoint (s : Simplex P) (hs : valid s) : point s ∈ onSet P (K s) ∧
      point s ∈ degreeModule P 0 ∧ boundary P (point s) = 0 ∧ augmentation P (point s) = 1 := by
    have hp : p s ∈ K s := by
      dsimp only [p]
      rw [dite_eq_left hs]
      exact (hKne s hs.1 hs.2).choose_spec
    refine ⟨?_,?_,boundary_vertex P _,augmentation_vertex P _⟩
    · apply supported_single
      exact ⟨List.pairwise_singleton _ _,by rw [vertices_vertex]; exact Set.singleton_subset_iff.mpr hp⟩
    · change Homogeneous P 0 (Finsupp.single (simplexVertex P (p s)) 1)
      exact supported_single P (P := fun t => degree P t = 0) rfl 1
  have hfill (s : Simplex P) (hs : valid s) (k : ℕ) (hk : k ≤ N) (z : Chain P)
      (hz : z ∈ onSet P (K s)) (hzdeg : z ∈ degreeModule P k)
      (hzd : boundary P z = 0) (hza : augmentation P z = 0) :=
    cycleFill_spec P (hKexact s hs.1 hs.2 k hk) hz hzdeg hzd hza
  have hF (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N+1) :
      F (Finsupp.single s 1) ∈ onSet P (K s) ∧
      F (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P (F (Finsupp.single s 1)) = F (boundary P (Finsupp.single s 1)) ∧
      augmentation P (F (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact OrderBasedComplex.chosen_spec (based P) point fill (boundary P) (augmentation P)
      (degreeModule P) valid (fun s => onSet P (K s)) N hvalid
      (fun s t hs ht => onSet_mono P (hfaceK s t hs.1 hs.2 ht)) hpoint hfill s hs hdeg
  let fillL := fun s k z => cycleFill P (L s) k z
  let H := OrderBasedComplex.chosenHomotopy (based P) fillL LinearMap.id F
  have hI (s : Simplex P) (hs : valid s) (_ : degree P s ≤ N) :
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ onSet P (L s) ∧
      (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1) ∈ degreeModule P (degree P s) ∧
      boundary P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = (LinearMap.id : Chain P →ₗ[ℤ] Chain P) (boundary P (Finsupp.single s 1)) ∧
      augmentation P ((LinearMap.id : Chain P →ₗ[ℤ] Chain P) (Finsupp.single s 1)) = augmentation P (Finsupp.single s 1) := by
    exact ⟨supported_single P ⟨hs.1,hself s hs.1 hs.2⟩ 1,
      supported_single P (P := fun t => degree P t = degree P s) rfl 1,rfl,rfl⟩
  have hFL (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N) :=
    hF s hs (by omega)
  have hH (s : Simplex P) (hs : valid s) (hdeg : degree P s ≤ N) :
      H (Finsupp.single s 1) ∈ onSet P (L s) ∧
      H (Finsupp.single s 1) ∈ degreeModule P (degree P s+1) ∧
      boundary P (H (Finsupp.single s 1)) + H (boundary P (Finsupp.single s 1)) =
        Finsupp.single s 1 - F (Finsupp.single s 1) ∧
      augmentation P (H (Finsupp.single s 1)) = 0 := by
    apply OrderBasedComplex.chosenHomotopy_spec (based P) fillL LinearMap.id F (boundary P)
      (augmentation P) (degreeModule P) valid (fun s => onSet P (L s)) N hvalid
      (fun s t hs ht => onSet_mono P (hfaceL s t hs.1 hs.2 ht)) hI ?_ ?_ s hs hdeg
    · intro t ht htd
      exact ⟨onSet_mono P (hKL t ht.1 ht.2) (hFL t ht htd).1,(hFL t ht htd).2⟩
    · intro t ht k hk z hz hzdeg hzd hza
      exact cycleFill_spec P (hLexact t ht.1 ht.2 k hk) hz hzdeg hzd hza
  have hsd (s : Simplex P) (hs : s ∈ c.support) : degree P s ≤ N := (hn s hs).le.trans hnN
  have hbdg (s : Simplex P) (hs : s ∈ b.support) : degree P s ≤ N+1 := by rw [hbn s hs]; omega
  refine ⟨F b + H c, (onSet P V).add_mem ?_ ?_, supported_add P ?_ ?_, ?_⟩
  · apply OrderBasedComplex.map_mem_of_support
    intro t ht
    exact onSet_mono P (hKV t (hb ht).1 (hb ht).2) (hF t (hb ht) (hbdg t ht)).1
  · apply OrderBasedComplex.map_mem_of_support
    intro t ht
    exact onSet_mono P (hLV t (hcV ht).1 (hcV ht).2) (hH t (hc ht) (hsd t ht)).1
  · apply OrderBasedComplex.map_mem_of_support F (degreeModule P (n+1))
    intro t ht
    rw [← hbn t ht]
    exact (hF t (hb ht) (hbdg t ht)).2.1
  · apply OrderBasedComplex.map_mem_of_support H (degreeModule P (n+1))
    intro t ht
    rw [← hn t ht]
    exact (hH t (hc ht) (hsd t ht)).2.1
  · have hFb := OrderBasedComplex.linear_eq_on_support ((boundary P).comp F) (F.comp (boundary P)) b
      (fun t ht => (hF t (hb ht) (hbdg t ht)).2.2.1)
    have hHc := OrderBasedComplex.linear_eq_on_support ((boundary P).comp H+H.comp (boundary P))
      (LinearMap.id-F) c (fun t ht => (hH t (hc ht) (hsd t ht)).2.2.1)
    simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
      hd,map_zero,add_zero] at hHc
    simp only [LinearMap.comp_apply,hbd] at hFb
    rw [map_add,hFb,hHc]
    abel
end

open OrderListChains
variable (P : Type*) [PartialOrder P]
noncomputable def lowerCarrier (r : P → ℕ) (h : ℕ) (s : Simplex P) : Set P :=
  if r s.1 = h+1 then Set.Iio s.1 else vertices P s
noncomputable def lowerStar (r : P → ℕ) (h : ℕ) (s : Simplex P) : Set P :=
  if r s.1 = h+1 then Set.Iic s.1 else vertices P s

lemma lowerCarrier_face (r : P → ℕ) (hr : StrictMono r) (h : ℕ)
    {s t : Simplex P} (hs : Descending P s)
    (hsU : vertices P s ⊆ {x | r x ≤ h+1})
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    lowerCarrier P r h t ⊆ lowerCarrier P r h s := by
  classical
  have hv := boundary_vertices P s t ht
  have hts := hs.le_head P (hv (head_mem_vertices P t))
  have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
  have htr := hr.monotone hts
  have hdt := hs.boundary P ht
  unfold lowerCarrier
  split_ifs with hT hS hS
  · have he : t.1 = s.1 := by
      apply le_antisymm hts
      by_contra hn
      have hh := hr (lt_of_le_not_ge hts hn)
      omega
    simpa only [he] using (Set.Subset.rfl : Set.Iio s.1 ⊆ Set.Iio s.1)
  · omega
  · intro x hx
    have hxt := hdt.le_head P hx
    apply lt_of_le_of_ne (hxt.trans hts)
    intro he
    have hh := hr.monotone hxt
    rw [he] at hh
    omega
  · exact hv

lemma lowerStar_face (r : P → ℕ) (hr : StrictMono r) (h : ℕ)
    {s t : Simplex P} (hs : Descending P s)
    (hsU : vertices P s ⊆ {x | r x ≤ h+1})
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    lowerStar P r h t ⊆ lowerStar P r h s := by
  classical
  have hv := boundary_vertices P s t ht
  have hts := hs.le_head P (hv (head_mem_vertices P t))
  have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
  have htr := hr.monotone hts
  unfold lowerStar
  split_ifs with hT hS hS
  · exact fun _ hx => hx.trans hts
  · omega
  · exact fun _ hx => hs.le_head P (hv hx)
  · exact hv

theorem lower_filling (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, r a = h+1 → ∃ x, x < a)
    (hex : ∀ a, r a = h+1 → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (c b : Chain P)
    (hc : c ∈ onSet P {x | r x ≤ h}) (hcn : Homogeneous P n c)
    (hcd : boundary P c = 0) (hca : augmentation P c = 0)
    (hb : b ∈ onSet P {x | r x ≤ h+1}) (hbn : Homogeneous P (n+1) b)
    (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P {x | r x ≤ h} ∧
      Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  classical
  apply carrier_fill P {x | r x ≤ h+1} {x | r x ≤ h}
    (lowerCarrier P r h) (lowerStar P r h) N
    ?_ ?_ ?_ ?_ ?_ (fun _ _ hs hsU ht => lowerCarrier_face P r hr h hs hsU ht)
    (fun _ _ hs hsU ht => lowerStar_face P r hr h hs hsU ht) ?_ ?_ ?_ ?_
    hnN c b hc hcn hcd hca hb hbn hbd
  · intro s _ _
    unfold lowerCarrier
    split_ifs with he
    · exact hne s.1 he
    · exact ⟨s.1,head_mem_vertices P s⟩
  · intro s hs hsU x hx
    have hsr : r s.1 ≤ h+1 := hsU (head_mem_vertices P s)
    unfold lowerCarrier at hx
    split_ifs at hx with he
    · have hh := hr hx
      change r x ≤ h
      omega
    · have hh := hr.monotone (hs.le_head P hx)
      change r x ≤ h
      omega
  · intro s hs hsU x hx
    unfold lowerStar at hx
    split_ifs at hx with he
    · have hh := hr.monotone hx
      change r x ≤ h+1
      omega
    · exact hsU hx
  · intro s _ _ x hx
    unfold lowerCarrier lowerStar at *
    split_ifs at *
    · exact hx.le
    · exact hx
  · intro s hs _
    unfold lowerStar
    split_ifs
    · exact fun _ hx => hs.le_head P hx
    · exact Set.Subset.rfl
  · intro s hs _ k hk
    unfold lowerCarrier
    split_ifs with he
    · exact hex s.1 he k hk
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro s hs _ k _
    unfold lowerStar
    split_ifs
    · exact exactSet_of_top P (U := Set.Iic s.1) s.1 le_rfl (fun _ hx => hx) k
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro x hx
    change r x ≤ h+1
    change r x ≤ h at hx
    omega
  · intro s _ hsV
    have hsr := hsV (head_mem_vertices P s)
    have he : r s.1 ≠ h+1 := by change r s.1 ≤ h at hsr; omega
    simpa only [lowerStar,ite_eq_right he] using hsV
end OrderChains

end

end OAI
