import Mathlib
import OAI.GroupTheory.FiniteType.OrderListChainsBased

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
def Descending (s : Simplex P) : Prop := (list P s).Pairwise (fun a b => b ≤ a)
def module : Submodule ℤ (Chain P) := Finsupp.supported ℤ ℤ {s | Descending P s}
def carrier (x : P) : Submodule ℤ (Chain P) :=
  Finsupp.supported ℤ ℤ {s | Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x}
lemma Descending.le_head {s : Simplex P} (hs : Descending P s) {v : P}
    (hv : v ∈ vertices P s) : v ≤ s.1 := by
  rcases hv with rfl | hv
  · exact le_rfl
  · exact (List.pairwise_cons.mp hs).1 v hv
lemma Descending.boundary {s t : Simplex P} (hs : Descending P s)
    (ht : t ∈ (boundary P (Finsupp.single s 1)).support) : Descending P t :=
  hs.sublist (boundary_sublist P s t ht)
lemma carrier_le_module (x : P) : carrier P x ≤ module P := fun _ hc _ hs => (hc hs).1
lemma carrier_mono {x y : P} (h : x ≤ y) : carrier P x ≤ carrier P y :=
  fun _ hc _ hs => ⟨(hc hs).1,fun v hv => ((hc hs).2 v hv).trans h⟩
lemma cone_carrier (x : P) {c : Chain P} (hc : c ∈ carrier P x) :
    cone P x c ∈ carrier P x := by
  refine supported_cone P (P := fun s => Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x)
    (Q := fun s => Descending P s ∧ ∀ v ∈ vertices P s, v ≤ x) x ?_ hc
  intro s hs
  constructor
  · change (x :: list P s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun v hv => hs.2 v ((mem_list P s v).mp hv),hs.1⟩
  · rw [vertices_cone]
    intro v hv
    rcases hv with rfl | hv
    · exact le_rfl
    · exact hs.2 v hv
lemma boundary_mem {c : Chain P} (hc : c ∈ module P) : boundary P c ∈ module P := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs t ht
  exact (hc hs).boundary P ht

variable {Q : Type*} [Preorder Q]
lemma Descending.map (f : P →o Q) {s : Simplex P} (hs : Descending P s) :
    Descending Q (f s.1,s.2.map f) := by
  change ((list P s).map f).Pairwise _
  exact List.Pairwise.map f (fun a b h => f.monotone h) hs
lemma Descending.map_carrier (f g : P →o Q) (hfg : ∀ x, f x ≤ g x)
    {s : Simplex P} (hs : Descending P s) :
    mapChain P f (Finsupp.single s 1) ∈ carrier Q (g s.1) := by
  rw [mapChain_single]
  apply supported_single
  refine ⟨hs.map P f,?_⟩
  intro v hv
  rcases hv with rfl | hv
  · exact hfg s.1
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact (f.monotone (hs.le_head P (Or.inr hw))).trans (hfg _)
lemma map_mem (f : P →o Q) {c : Chain P} (hc : c ∈ module P) :
    mapChain P f c ∈ module Q := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  exact carrier_le_module Q _ ((hc hs).map_carrier P f f (fun _ => le_rfl))
lemma map_degree (P : Type*) [Preorder P] {Q : Type*} [Preorder Q]
    (f : P → Q) {n : ℕ} {c : Chain P} (hc : Homogeneous P n c) :
    Homogeneous Q n (mapChain P f c) := by
  refine supported_linearMap P (P := fun s => degree P s = n)
    (Q := fun s => degree Q s = n) (mapChain P f) ?_ hc
  intro s hs
  rw [mapChain_single]
  apply supported_single
  simpa [degree] using hs

noncomputable def comparison (f g : P →o Q) : Chain P →ₗ[ℤ] Chain Q :=
  OrderBasedComplex.homotopy (based P) (boundary Q) (augmentation Q)
    (fun s => contraction Q (g s.1)) (mapChain P f) (mapChain P g)
lemma comparison_boundary (f g : P →o Q) (c : Chain P) :
    boundary Q (comparison P f g c) + comparison P f g (boundary P c) =
      mapChain P f c - mapChain P g c := by
  apply OrderBasedComplex.d_homotopy
  · exact fun c => boundary_mapChain P f c
  · exact fun c => boundary_mapChain P g c
  · intro c
    rw [augmentation_mapChain,augmentation_mapChain]
lemma comparison_mem (f g : P →o Q) (hfg : ∀ x, f x ≤ g x)
    {c : Chain P} (hc : c ∈ module P) : comparison P f g c ∈ module Q := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  apply carrier_le_module Q (g s.1)
  apply OrderBasedComplex.homotopy_mem_on (based P) (boundary Q) (augmentation Q)
    (fun s => contraction Q (g s.1)) (mapChain P f) (mapChain P g) (Descending P)
    (fun _ _ h ht => h.boundary P ht) (fun s => carrier Q (g s.1))
    _ _ _ _ s (hc hs)
  · intro s hs
    exact hs.map_carrier P f g hfg
  · intro s hs
    exact hs.map_carrier P g g (fun _ => le_rfl)
  · intro s _ c hc
    exact cone_carrier Q (g s.1) hc
  · intro s t hs ht
    exact carrier_mono Q (g.monotone (hs.le_head P
      (boundary_vertices P s t ht (head_mem_vertices P t))))
lemma comparison_degree (f g : P →o Q) {n : ℕ} {c : Chain P} (hc : Homogeneous P n c) :
    Homogeneous Q (n+1) (comparison P f g c) := by
  apply OrderBasedComplex.map_mem_of_support (comparison P f g) (degreeModule Q (n+1)) c
  intro s hs
  rw [← hc s hs]
  apply OrderBasedComplex.homotopy_degree (based P) (boundary Q) (augmentation Q)
    (fun s => contraction Q (g s.1)) (mapChain P f) (mapChain P g) (degreeModule Q)
  · intro s
    exact map_degree P f (supported_single P (P := fun t => degree P t = degree P s) rfl 1)
  · intro s
    exact map_degree P g (supported_single P (P := fun t => degree P t = degree P s) rfl 1)
  · intro s n c hc
    exact cone_mem_degreeModule Q _ hc

lemma mapChain_comp (P : Type*) [Preorder P] {Q : Type*} [Preorder Q]
    {R : Type*} (f : P → Q) (g : Q → R) (c : Chain P) :
    mapChain Q g (mapChain P f c) = mapChain P (g ∘ f) c := by
  have h : (mapChain Q g).comp (mapChain P f) = mapChain P (g ∘ f) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply,mapChain_single,List.map_map,Function.comp_apply]
  exact LinearMap.congr_fun h c
lemma mapChain_id (P : Type*) [Preorder P] (c : Chain P) : mapChain P id c = c := by
  have h : mapChain P id = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [mapChain_single,id_eq,List.map_id,LinearMap.id_coe]
  exact LinearMap.congr_fun h c

def ExactIn (n : ℕ) : Prop := ∀ c : Chain P, c ∈ module P → Homogeneous P n c →
  boundary P c = 0 → augmentation P c = 0 →
  ∃ d : Chain P, d ∈ module P ∧ Homogeneous P (n+1) d ∧ boundary P d = c

theorem exactIn_of_comparison (i : Q →o P) (r : P →o Q)
    (hir : ∀ x, i (r x) ≤ x) {n : ℕ} (h : ExactIn Q n) : ExactIn P n := by
  intro c hc hn hd ha
  have hrd : boundary Q (mapChain P r c) = 0 := by
    rw [boundary_mapChain,hd,map_zero]
  have hra : augmentation Q (mapChain P r c) = 0 := by rw [augmentation_mapChain,ha]
  obtain ⟨d,hdQ,hdn,hdd⟩ := h (mapChain P r c) (map_mem P r hc) (map_degree P r hn) hrd hra
  let f := i.comp r
  refine ⟨mapChain Q i d - comparison P f OrderHom.id c,
    (module P).sub_mem (map_mem Q i hdQ) (comparison_mem P f OrderHom.id hir hc),
    supported_sub P (map_degree Q i hdn) (comparison_degree P f OrderHom.id hn),?_⟩
  have hH := comparison_boundary P f OrderHom.id c
  rw [hd,map_zero,add_zero] at hH
  rw [map_sub,boundary_mapChain,hdd,hH,mapChain_comp]
  have he : mapChain P (OrderHom.id : P →o P) c = c := mapChain_id P c
  rw [he]
  change mapChain P (i ∘ r) c - (mapChain P (i ∘ r) c - c) = c
  abel
end

open OrderListChains
variable {P Q : Type*} [Preorder P] [Preorder Q]
lemma exactIn_of_orderIso (e : P ≃o Q) {n : ℕ} (h : ExactIn Q n) : ExactIn P n :=
  exactIn_of_comparison P ⟨e.symm,e.symm.monotone⟩ ⟨e,e.monotone⟩ (fun x => le_of_eq (e.symm_apply_apply x)) h
end OrderChains

namespace SteinChains
open OrderListChains
variable (V : Type*) [Fintype V]
                                                                      
def ProperFace := {F : Finset V // F ≠ ∅ ∧ F ≠ Finset.univ}
instance : PartialOrder (ProperFace V) := inferInstanceAs
  (PartialOrder {F : Finset V // F ≠ ∅ ∧ F ≠ Finset.univ})
def properInclude : ProperFace V →o Face V where
  toFun F := ⟨F.val,Finset.nonempty_iff_ne_empty.mpr F.property.1⟩
  monotone' := fun _ _ h => h

noncomputable def properProject (v : V) (hv : 1 < Fintype.card V) : Face V → ProperFace V := by
  classical
  exact fun F => if h : F.val ≠ Finset.univ then ⟨F.val,Finset.nonempty_iff_ne_empty.mp F.property,h⟩
    else ⟨{v},by
      constructor
      · exact Finset.singleton_nonempty _ |>.ne_empty
      · intro he
        have hh := congrArg Finset.card he
        simp only [Finset.card_singleton,Finset.card_univ] at hh
        omega⟩
lemma properProject_val (v : V) (hv : 1 < Fintype.card V) (F : Face V)
    (hF : F.val ≠ Finset.univ) : (properProject V v hv F).val = F.val := by
  classical
  simp [properProject, hF]
lemma project_include (v : V) (hv : 1 < Fintype.card V) (F : ProperFace V) :
    properProject V v hv (properInclude V F) = F := by
  apply Subtype.ext
  exact properProject_val V v hv _ F.property.2

lemma properInclude_mem {c : Chain (ProperFace V)} (hc : c ∈ OrderChains.module (ProperFace V)) :
    mapChain (ProperFace V) (properInclude V) c ∈ (boundaryComplex V Finset.univ).faceModule V := by
  classical
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  rw [mapChain_single]
  apply supported_single
  refine ⟨OrderChains.Descending.map _ (properInclude V) (hc hs),?_⟩
  intro F hF
  have hproper (E : ProperFace V) : (properInclude V E).val ⊆ Finset.univ ∧
      (properInclude V E).val.card < Finset.univ.card :=
    ⟨Finset.subset_univ _,Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _,E.property.2⟩)⟩
  rcases hF with rfl | hF
  · exact hproper s.1
  · obtain ⟨E,_,rfl⟩ := List.mem_map.mp hF
    exact hproper E

lemma properProject_mem (v : V) (hv : 1 < Fintype.card V) {c : Chain (Face V)}
    (hc : c ∈ (boundaryComplex V Finset.univ).faceModule V) :
    mapChain (Face V) (properProject V v hv) c ∈ OrderChains.module (ProperFace V) := by
  classical
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  rw [mapChain_single]
  apply supported_single
  change ((list (Face V) s).map (properProject V v hv)).Pairwise _
  rw [List.pairwise_map]
  apply (hc hs).1.imp_of_mem
  intro F E hF hE hEF
  change (properProject V v hv E).val ⊆ (properProject V v hv F).val
  have hne (D : Face V) (hD : D ∈ list (Face V) s) : D.val ≠ Finset.univ := by
    have hh := ((hc hs).2 D ((mem_list _ s D).mp hD)).2
    intro he
    rw [he] at hh
    exact (lt_irrefl _ hh)
  rw [properProject_val V v hv E (hne E hE),properProject_val V v hv F (hne F hF)]
  exact hEF

theorem properFace_exactIn {n : ℕ} (hn : n+2 < Fintype.card V) :
    OrderChains.ExactIn (ProperFace V) n := by
  classical
  have hv : 1 < Fintype.card V := by omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  intro c hc hcdeg hcd hca
  let e := properInclude V
  have hz : boundary (Face V) (mapChain _ e c) = 0 := by rw [boundary_mapChain,hcd,map_zero]
  have ha : augmentation (Face V) (mapChain _ e c) = 0 := by rw [augmentation_mapChain,hca]
  obtain ⟨d,hdK,hdn,hdd⟩ := boundary_face_cycle_bounds V
    (T := Finset.univ) (by simpa only [Finset.card_univ] using hn)
    (properInclude_mem V hc) (OrderChains.map_degree _ e hcdeg) hz ha
  refine ⟨mapChain (Face V) (properProject V v hv) d,properProject_mem V v hv hdK,
    OrderChains.map_degree _ _ hdn,?_⟩
  rw [boundary_mapChain,hdd,OrderChains.mapChain_comp]
  have he : properProject V v hv ∘ e = id := funext (project_include V v hv)
  rw [he,OrderChains.mapChain_id]
end SteinChains

end

end OAI
