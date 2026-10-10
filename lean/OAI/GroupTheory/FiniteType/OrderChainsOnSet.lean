import Mathlib
import OAI.GroupTheory.FiniteType.OrderChainsExactInOfTop

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
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
def onSet (U : Set P) : Submodule ℤ (Chain P) :=
  Finsupp.supported ℤ ℤ {s | Descending P s ∧ vertices P s ⊆ U}
lemma onSet_mono {U V : Set P} (h : U ⊆ V) : onSet P U ≤ onSet P V :=
  fun _ hc _ hs => ⟨(hc hs).1, fun _ hx => h ((hc hs).2 hx)⟩
lemma onSet_le_module (U : Set P) : onSet P U ≤ module P :=
  fun _ hc _ hs => (hc hs).1
lemma boundary_onSet {U : Set P} {c : Chain P} (hc : c ∈ onSet P U) :
    boundary P c ∈ onSet P U := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs t ht
  exact ⟨(hc hs).1.boundary P ht,(boundary_vertices P s t ht).trans (hc hs).2⟩
lemma map_onSet {Q : Type*} [Preorder Q] (f : P → Q) {U : Set P} {V : Set Q}
    (hf : ∀ x ∈ U, f x ∈ V) (hm : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → f x ≤ f y)
    {c : Chain P} (hc : c ∈ onSet P U) : mapChain P f c ∈ onSet Q V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  rw [mapChain_single]
  apply supported_single
  constructor
  · change ((list P s).map f).Pairwise _
    rw [List.pairwise_map]
    apply (hc hs).1.imp_of_mem
    intro x y hx hy hxy
    exact hm y ((hc hs).2 ((mem_list P s y).mp hy))
      x ((hc hs).2 ((mem_list P s x).mp hx)) hxy
  · intro y hy
    rcases hy with rfl | hy
    · exact hf s.1 ((hc hs).2 (head_mem_vertices P s))
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
      exact hf x ((hc hs).2 (Or.inr hx))

def ExactSet (U : Set P) (n : ℕ) : Prop := ∀ c : Chain P, c ∈ onSet P U →
  Homogeneous P n c → boundary P c = 0 → augmentation P c = 0 →
  ∃ d : Chain P, d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧ boundary P d = c

noncomputable def project (U : Set P) (u : U) (x : P) : U := by
  classical
  exact if h : x ∈ U then ⟨x,h⟩ else u
lemma project_val (P : Type*) [Preorder P] {U : Set P} (u : U) {x : P} (hx : x ∈ U) :
    (project P U u x).val = x := by
  classical
  simp [project,hx]
lemma project_include {U : Set P} (u v : U) : project P U u v = v := by
  apply Subtype.ext
  exact project_val P u v.property
lemma exactSet_of_subtype {U : Set P} (u : U) {n : ℕ} (h : ExactIn U n) :
    ExactSet P U n := by
  intro c hc hn hd ha
  have hp := map_onSet P (project P U u) (V := Set.univ) (fun _ _ => Set.mem_univ _)
    (fun x hx y hy hxy => by
      change (project P U u x).val ≤ (project P U u y).val
      simpa only [project_val P u hx,project_val P u hy] using hxy) hc
  have hpd : boundary U (mapChain P (project P U u) c) = 0 := by
    rw [boundary_mapChain,hd,map_zero]
  have hpa : augmentation U (mapChain P (project P U u) c) = 0 := by
    rw [augmentation_mapChain,ha]
  obtain ⟨d,hdU,hdn,hdd⟩ := h _ (onSet_le_module U _ hp)
    (map_degree P _ hn) hpd hpa
  have hdset : d ∈ onSet U Set.univ := fun s hs => ⟨hdU hs,Set.subset_univ _⟩
  refine ⟨mapChain U Subtype.val d,map_onSet U Subtype.val
      (fun x _ => x.property) (fun _ _ _ _ hxy => hxy) hdset,map_degree U _ hdn,?_⟩
  rw [boundary_mapChain,hdd,mapChain_comp]
  have he := mapChain_eq_on P (Subtype.val ∘ project P U u) id
    (c := c) (fun s hs x hx => project_val P u ((hc hs).2 hx))
  rw [he,mapChain_id]

lemma cone_onSet_top {U : Set P} (u : P) (hu : u ∈ U) (ht : ∀ x ∈ U, x ≤ u)
    {c : Chain P} (hc : c ∈ onSet P U) : cone P u c ∈ onSet P U := by
  change Supported P (fun s => Descending P s ∧ vertices P s ⊆ U) (cone P u c)
  refine supported_cone P (P := fun s => Descending P s ∧ vertices P s ⊆ U) u ?_ hc
  intro s hs
  constructor
  · change (u :: list P s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun x hx => ht x (hs.2 ((mem_list P s x).mp hx)),hs.1⟩
  · rw [vertices_cone]
    exact Set.insert_subset hu hs.2
lemma exactSet_of_top {U : Set P} (u : P) (hu : u ∈ U) (ht : ∀ x ∈ U, x ≤ u)
    (n : ℕ) : ExactSet P U n := by
  intro c hc hn hd ha
  refine ⟨cone P u c,cone_onSet_top P u hu ht hc,cone_mem_degreeModule P _ hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]

noncomputable def cycleFill (U : Set P) (n : ℕ) (c : Chain P) : Chain P := by
  classical
  exact if h : ∃ d : Chain P, d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧ boundary P d = c
    then Classical.choose h else 0
lemma cycleFill_spec {U : Set P} {n : ℕ} (hU : ExactSet P U n) {c : Chain P}
    (hc : c ∈ onSet P U) (hn : Homogeneous P n c) (hd : boundary P c = 0)
    (ha : augmentation P c = 0) :
    cycleFill P U n c ∈ onSet P U ∧ Homogeneous P (n+1) (cycleFill P U n c) ∧
    boundary P (cycleFill P U n c) = c ∧ augmentation P (cycleFill P U n c) = 0 := by
  have he := hU c hc hn hd ha
  classical
  simp only [cycleFill,dite_eq_left he]
  exact ⟨(Classical.choose_spec he).1,(Classical.choose_spec he).2.1,
    (Classical.choose_spec he).2.2,augmentation_of_positive P (n := n+1) (by omega) (Classical.choose_spec he).2.1⟩

lemma exactSet_of_bottom {U : Set P} (u : P) (hu : u ∈ U)
    (hb : ∀ x ∈ U, u ≤ x) (n : ℕ) : ExactSet P U n := by
  let i : PUnit.{1} →o U := ⟨fun _ => ⟨u,hu⟩,fun _ _ _ => le_rfl⟩
  let r : U →o PUnit.{1} := ⟨fun _ => PUnit.unit,fun _ _ _ => le_rfl⟩
  apply exactSet_of_subtype P ⟨u,hu⟩
  apply exactIn_of_comparison U i r (fun x => hb x x.property)
  exact exactIn_of_top PUnit.{1} PUnit.unit (fun _ => le_rfl) n

lemma Descending.comparable {s : Simplex P} (hs : Descending P s) {x y : P}
    (hx : x ∈ vertices P s) (hy : y ∈ vertices P s) : x ≤ y ∨ y ≤ x := by
  have h (l : List P) (hl : l.Pairwise (fun a b => b ≤ a)) :
      ∀ x ∈ l, ∀ y ∈ l, x ≤ y ∨ y ≤ x := by
    induction l with
    | nil => simp
    | cons a l ih =>
      obtain ⟨hal,hl⟩ := List.pairwise_cons.mp hl
      intro x hx y hy
      rcases List.mem_cons.mp hx with rfl | hxTail
      · rcases List.mem_cons.mp hy with rfl | hyTail
        · exact Or.inl le_rfl
        · exact Or.inr (hal y hyTail)
      · rcases List.mem_cons.mp hy with rfl | hyTail
        · exact Or.inl (hal x hxTail)
        · exact ih hl x hxTail y hyTail
  exact h (list P s) hs x ((mem_list P s x).mpr hx) y ((mem_list P s y).mpr hy)

theorem carrier_move (U V : Set P) (K L : Simplex P → Set P) (N : ℕ)
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
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P U) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P V ∧ Homogeneous P n c' ∧ boundary P c' = 0 ∧
      augmentation P c' = 0 ∧ d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧
      boundary P d = c-c' := by
  classical
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
  have hsvalid (s : Simplex P) (hs : s ∈ c.support) : valid s := hc hs
  have hsd (s : Simplex P) (hs : s ∈ c.support) : degree P s ≤ N := (hn s hs).le.trans hnN
  refine ⟨F c,H c,?_,?_,?_,?_,?_,?_,?_⟩
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_mono P (hKV s (hc hs).1 (hc hs).2) (hFL s (hsvalid s hs) (hsd s hs)).1
  · apply OrderBasedComplex.map_mem_of_support F (degreeModule P n)
    intro s hs
    rw [← hn s hs]
    exact (hFL s (hsvalid s hs) (hsd s hs)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary P).comp F) (F.comp (boundary P)) c
      (fun s hs => (hFL s (hsvalid s hs) (hsd s hs)).2.2.1)
    simpa only [LinearMap.comp_apply,hd,map_zero] using he
  · have he := OrderBasedComplex.linear_eq_on_support ((augmentation P).comp F) (augmentation P) c
      (fun s hs => (hFL s (hsvalid s hs) (hsd s hs)).2.2.2)
    simpa only [LinearMap.comp_apply,ha] using he
  · apply OrderBasedComplex.map_mem_of_support
    intro s hs
    exact onSet_mono P (hLU s (hc hs).1 (hc hs).2) (hH s (hsvalid s hs) (hsd s hs)).1
  · apply OrderBasedComplex.map_mem_of_support H (degreeModule P (n+1))
    intro s hs
    rw [← hn s hs]
    exact (hH s (hsvalid s hs) (hsd s hs)).2.1
  · have he := OrderBasedComplex.linear_eq_on_support ((boundary P).comp H+H.comp (boundary P))
      (LinearMap.id-F) c (fun s hs => (hH s (hsvalid s hs) (hsd s hs)).2.2.1)
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,hd,map_zero,add_zero,
      LinearMap.sub_apply,LinearMap.id_apply] using he
end

section
open OrderListChains
variable (P : Type*) [PartialOrder P]
noncomputable def deleteCarrier (U : Set P) (a : P) (s : Simplex P) : Set P := by
  classical
  exact if a ∈ vertices P s then {x | x ∈ U ∧ a < x} else vertices P s
noncomputable def starCarrier (U : Set P) (a : P) (s : Simplex P) : Set P := by
  classical
  exact if a ∈ vertices P s then {x | x ∈ U ∧ a ≤ x} else vertices P s
lemma Descending.above_min {U : Set P} {a : P}
    (hmin : ∀ x ∈ U, x ≤ a → x = a) {s : Simplex P}
    (hs : Descending P s) (hsU : vertices P s ⊆ U) (ha : a ∈ vertices P s) :
    ∀ x ∈ vertices P s, a ≤ x := by
  intro x hx
  rcases hs.comparable P ha hx with h | h
  · exact h
  · rw [hmin x (hsU hx) h]
lemma deleteCarrier_face {U : Set P} {a : P} (hmin : ∀ x ∈ U, x ≤ a → x = a)
    {s t : Simplex P} (hs : Descending P s) (hsU : vertices P s ⊆ U)
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    deleteCarrier P U a t ⊆ deleteCarrier P U a s := by
  classical
  have hts := boundary_vertices P s t ht
  unfold deleteCarrier
  split_ifs with hat has has
  · exact Set.Subset.rfl
  · exact False.elim (has (hts hat))
  · intro x hx
    exact ⟨hsU (hts hx),lt_of_le_of_ne (hs.above_min P hmin hsU has x (hts hx))
      (fun h => hat (h ▸ hx))⟩
  · exact hts
lemma starCarrier_face {U : Set P} {a : P} (hmin : ∀ x ∈ U, x ≤ a → x = a)
    {s t : Simplex P} (hs : Descending P s) (hsU : vertices P s ⊆ U)
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) :
    starCarrier P U a t ⊆ starCarrier P U a s := by
  classical
  have hts := boundary_vertices P s t ht
  unfold starCarrier
  split_ifs with hat has has
  · exact Set.Subset.rfl
  · exact False.elim (has (hts hat))
  · intro x hx
    exact ⟨hsU (hts hx),hs.above_min P hmin hsU has x (hts hx)⟩
  · exact hts

theorem delete_minimal (U : Set P) (a : P) (haU : a ∈ U)
    (hmin : ∀ x ∈ U, x ≤ a → x = a) (N : ℕ)
    (hup : ∃ x ∈ U, a < x)
    (hupper : ∀ k ≤ N, ExactSet P {x | x ∈ U ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P U) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P (U \ {a}) ∧ Homogeneous P n c' ∧ boundary P c' = 0 ∧
      augmentation P c' = 0 ∧ d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧
      boundary P d = c-c' := by
  classical
  apply carrier_move P U (U \ {a}) (deleteCarrier P U a) (starCarrier P U a) N
    ?_ ?_ ?_ ?_ ?_ (fun _ _ hs hsU ht => deleteCarrier_face P hmin hs hsU ht)
    (fun _ _ hs hsU ht => starCarrier_face P hmin hs hsU ht) ?_ ?_ hnN c hc hn hd ha
  · intro s _ _
    unfold deleteCarrier
    split_ifs
    · exact hup
    · exact ⟨s.1,head_mem_vertices P s⟩
  · intro s _ hsU x hx
    unfold deleteCarrier at hx
    split_ifs at hx with has
    · exact ⟨hx.1,fun h => (ne_of_lt hx.2) h.symm⟩
    · exact ⟨hsU hx,fun h => has (h ▸ hx)⟩
  · intro s _ hsU x hx
    unfold starCarrier at hx
    split_ifs at hx
    · exact hx.1
    · exact hsU hx
  · intro s _ _
    unfold deleteCarrier starCarrier
    split_ifs
    · exact fun _ hx => ⟨hx.1,hx.2.le⟩
    · exact Set.Subset.rfl
  · intro s hs hsU
    unfold starCarrier
    split_ifs with has
    · exact fun x hx => ⟨hsU hx,hs.above_min P hmin hsU has x hx⟩
    · exact Set.Subset.rfl
  · intro s hs hsU k hk
    unfold deleteCarrier
    split_ifs
    · exact hupper k hk
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
  · intro s hs hsU k _
    unfold starCarrier
    split_ifs
    · exact exactSet_of_bottom P (U := {x | x ∈ U ∧ a ≤ x}) a ⟨haU,le_rfl⟩ (fun _ hx => hx.2) k
    · exact exactSet_of_top P s.1 (head_mem_vertices P s) (fun _ hx => hs.le_head P hx) k
end

open OrderListChains
variable (P : Type*) [PartialOrder P]

theorem delete_finite_minimal (U : Set P) (T : Finset P) (N : ℕ)
    (hTU : ∀ a ∈ T, a ∈ U) (hmin : ∀ a ∈ T, ∀ x ∈ U, x ≤ a → x = a)
    (hup : ∀ a ∈ T, ∃ x ∈ U, a < x)
    (hupper : ∀ a ∈ T, ∀ k ≤ N, ExactSet P {x | x ∈ U ∧ a < x} k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P) (hc : c ∈ onSet P U) (hn : Homogeneous P n c)
    (hd : boundary P c = 0) (ha : augmentation P c = 0) :
    ∃ c' d : Chain P, c' ∈ onSet P (U \ (T : Set P)) ∧ Homogeneous P n c' ∧ boundary P c' = 0 ∧
      augmentation P c' = 0 ∧ d ∈ onSet P U ∧ Homogeneous P (n+1) d ∧
      boundary P d = c-c' := by
  classical
  induction T using Finset.induction_on generalizing U c with
  | empty =>
    refine ⟨c,0,?_,hn,hd,ha,(onSet P U).zero_mem,supported_zero P _,?_⟩
    · simpa only [Finset.coe_empty,Set.sdiff_empty] using hc
    · simp
  | @insert a T hat ih =>
    have hTa : a ∈ insert a T := Finset.mem_insert_self _ _
    obtain ⟨c1,d1,hc1,hn1,hd1,ha1,hD1,hDn1,hdd1⟩ := delete_minimal P U a (hTU a hTa)
      (hmin a hTa) N (hup a hTa) (hupper a hTa) hnN c hc hn hd ha
    have hmem (b : P) (hb : b ∈ T) : b ∈ insert a T := Finset.mem_insert_of_mem hb
    have hne (b : P) (hb : b ∈ T) : b ≠ a := by intro he; exact hat (he ▸ hb)
    have havoid (b : P) (hb : b ∈ T) (x : P) (hxU : x ∈ U) (hbx : b < x) : x ≠ a := by
      intro he
      subst x
      exact hne b hb (hmin a hTa b (hTU b (hmem b hb)) hbx.le)
    have hset (b : P) (hb : b ∈ T) :
        {x | x ∈ U \ {a} ∧ b < x} = {x | x ∈ U ∧ b < x} := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,havoid b hb x hx.1 hx.2⟩,hx.2⟩⟩
    obtain ⟨c2,d2,hc2,hn2,hd2,ha2,hD2,hDn2,hdd2⟩ := ih (U \ {a})
      (fun b hb => ⟨hTU b (hmem b hb),hne b hb⟩)
      (fun b hb x hx hxb => hmin b (hmem b hb) x hx.1 hxb)
      (fun b hb => by
        obtain ⟨x,hx,hbx⟩ := hup b (hmem b hb)
        exact ⟨x,⟨hx,havoid b hb x hx hbx⟩,hbx⟩)
      (fun b hb k hk => by rw [hset b hb]; exact hupper b (hmem b hb) k hk)
      c1 hc1 hn1 hd1 ha1
    refine ⟨c2,d1+d2,?_,hn2,hd2,ha2,?_,supported_add P hDn1 hDn2,?_⟩
    · apply onSet_mono P _ hc2
      intro x hx
      refine ⟨hx.1.1,?_⟩
      intro hxi
      rcases Finset.mem_insert.mp hxi with he | he
      · exact hx.1.2 he
      · exact hx.2 he
    · exact (onSet P U).add_mem hD1 (onSet_mono P Set.sdiff_subset hD2)
    · rw [map_add,hdd1,hdd2]
      abel
end OrderChains

end

end OAI
