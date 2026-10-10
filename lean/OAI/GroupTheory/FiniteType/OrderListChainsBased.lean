import Mathlib
import OAI.GroupTheory.FiniteType.OrderBasedComplex
import OAI.GroupTheory.FiniteType.OrderListChains

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
variable (G : Type*)
def based : OrderBasedComplex.Data (Simplex G) where
  degree := degree G
  d := boundary G
  aug := augmentation G
  d_squared := boundary_boundary G
  lowers := boundary_lowers G
  aug_single s := by simp only [augmentation_single, degree, List.length_eq_zero_iff]
  aug_d := augmentation_boundary G

def contraction (a : G) : OrderBasedComplex.Contraction (boundary G) (augmentation G) where
  point := vertex G a
  cone := cone G a
  d_point := boundary_vertex G a
  aug_point := augmentation_vertex G a
  aug_cone := augmentation_cone G a
  identity c := by rw [boundary_cone, K_apply]; abel

end OrderListChains

namespace OrderBasedComplex
variable {B M : Type*} [AddCommGroup M] (C : Data B)
  (d : M →ₗ[ℤ] M) (aug : M →ₗ[ℤ] ℤ) (T : B → Contraction d aug)

lemma homotopy_mem_on (F G : (B →₀ ℤ) →ₗ[ℤ] M) (P : B → Prop)
    (hP : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → P t)
    (K : B → Submodule ℤ M)
    (hF : ∀ b, P b → F (Finsupp.single b 1) ∈ K b)
    (hG : ∀ b, P b → G (Finsupp.single b 1) ∈ K b)
    (hcone : ∀ b, P b → ∀ c, c ∈ K b → (T b).cone c ∈ K b)
    (hface : ∀ b t, P b → t ∈ (C.d (Finsupp.single b 1)).support → K t ≤ K b)
    (b : B) (hb : P b) : homotopy C d aug T F G (Finsupp.single b 1) ∈ K b := by
  have help (n : ℕ) : ∀ b, C.degree b = n → P b →
      homotopy C d aug T F G (Finsupp.single b 1) ∈ K b := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hn hp
      rw [homotopy_equation]
      apply hcone b hp
      apply (K b).sub_mem ((K b).sub_mem (hF b hp) (hG b hp))
      apply map_mem_of_support
      intro t ht
      apply hface b t hp ht
      have hlt := C.lowers b t ht
      exact ih (C.degree t) (by omega) t rfl (hP b t hp ht)
  exact help (C.degree b) b rfl hb
end OrderBasedComplex

namespace OrderListChains
variable (V : Type*)

def list (s : Simplex V) : List V := s.1 :: s.2
@[simp] lemma list_vertex (v : V) : list V (simplexVertex V v) = [v] := rfl
@[simp] lemma list_cone (v : V) (s : Simplex V) :
    list V (simplexCone V v s) = v :: list V s := rfl
lemma mem_list (s : Simplex V) (v : V) : v ∈ list V s ↔ v ∈ vertices V s := by
  simp only [list,List.mem_cons,mem_vertices]

lemma boundary_sublist (s : Simplex V) :
    Supported V (fun t => List.Sublist (list V t) (list V s)) (boundary V (Finsupp.single s 1)) := by
  rcases s with ⟨a,l⟩
  induction l generalizing a with
  | nil =>
    change Supported V _ (boundary V (vertex V a))
    rw [boundary_vertex]
    exact supported_zero V _
  | cons b l ih =>
    rw [single_cons,boundary_cone]
    apply supported_sub
    · apply supported_sub
      · apply supported_single
        exact List.Sublist.cons _ (List.Sublist.refl _)
      · refine supported_cone V (Q := fun t => List.Sublist (list V t) (list V (a,b::l))) a ?_ (ih b)
        intro t ht
        exact List.Sublist.cons_cons _ ht
    · rw [K_apply,augmentation_single]
      by_cases hl : l = []
      · subst l
        rw [ite_eq_left rfl,one_smul]
        apply supported_single
        exact List.Sublist.cons_cons _ (List.nil_sublist _)
      · rw [ite_eq_right hl,zero_smul]
        exact supported_zero V _

noncomputable def finiteVertices (s : Simplex V) : Finset V := by
  classical
  exact (list V s).toFinset
lemma finiteVertices_nonempty (s : Simplex V) : (finiteVertices V s).Nonempty := by
  classical
  exact ⟨s.1,by simp [finiteVertices,list]⟩
lemma mem_finiteVertices (s : Simplex V) (v : V) :
    v ∈ finiteVertices V s ↔ v ∈ vertices V s := by
  classical
  simp only [finiteVertices,List.mem_toFinset,mem_list]
lemma finiteVertices_card_le (s : Simplex V) : (finiteVertices V s).card ≤ degree V s + 1 := by
  classical
  exact List.toFinset_card_le (list V s)
lemma finiteVertices_boundary {s t : Simplex V}
    (ht : t ∈ (boundary V (Finsupp.single s 1)).support) :
    finiteVertices V t ⊆ finiteVertices V s := by
  intro v hv
  rw [mem_finiteVertices] at hv ⊢
  exact boundary_vertices V s t ht hv

end OrderListChains

namespace SteinChains
section
open OrderListChains
variable (V : Type*)
abbrev Face := {F : Finset V // F.Nonempty}
noncomputable def simplexFace (s : Simplex V) : Face V :=
  ⟨finiteVertices V s,finiteVertices_nonempty V s⟩

noncomputable def bary : Chain V →ₗ[ℤ] Chain (Face V) :=
  OrderBasedComplex.extend (based V) (boundary (Face V)) (augmentation (Face V))
    (fun s => contraction (Face V) (simplexFace V s))

lemma boundary_bary (c : Chain V) : boundary (Face V) (bary V c) = bary V (boundary V c) :=
  OrderBasedComplex.d_extend _ _ _ _ _
lemma augmentation_bary (c : Chain V) : augmentation (Face V) (bary V c) = augmentation V c :=
  OrderBasedComplex.aug_extend _ _ _ _ _
lemma bary_degree {n : ℕ} {c : Chain V} (hc : Homogeneous V n c) :
    Homogeneous (Face V) n (bary V c) := by
  apply OrderBasedComplex.map_mem_of_support (bary V) (degreeModule (Face V) n) c
  intro s hs
  rw [← hc s hs]
  exact OrderBasedComplex.extend_degree _ _ _ _ (degreeModule (Face V))
    (fun _ _ => vertex_mem_degreeModule _ _) (fun _ _ _ h => cone_mem_degreeModule _ _ h) s

def Descending (s : Simplex (Face V)) : Prop := (list (Face V) s).Pairwise (fun F E => E ≤ F)

def faceCarrier (T : Finset V) : Submodule ℤ (Chain (Face V)) :=
  Finsupp.supported ℤ ℤ {s | Descending V s ∧ ∀ F ∈ vertices (Face V) s, F.val ⊆ T}

lemma faceCarrier_mono {T U : Finset V} (h : T ⊆ U) : faceCarrier V T ≤ faceCarrier V U := by
  intro c hc s hs
  exact ⟨(hc hs).1,fun F hF => ((hc hs).2 F hF).trans h⟩

lemma vertex_mem_faceCarrier (F : Face V) : vertex (Face V) F ∈ faceCarrier V F.val := by
  apply supported_single
  constructor
  · simp [Descending]
  · intro E hE
    have hh : E = F := by simpa [vertices,simplexVertex] using hE
    subst E
    exact Finset.Subset.refl _

lemma cone_mem_faceCarrier (F : Face V) {c : Chain (Face V)}
    (hc : c ∈ faceCarrier V F.val) : cone (Face V) F c ∈ faceCarrier V F.val := by
  apply supported_cone (Face V) (P := fun s => Descending V s ∧
    ∀ E ∈ vertices (Face V) s, E.val ⊆ F.val) (Q := fun s => Descending V s ∧
    ∀ E ∈ vertices (Face V) s, E.val ⊆ F.val) F _ hc
  intro s hs
  constructor
  · change (F :: list (Face V) s).Pairwise _
    rw [List.pairwise_cons]
    exact ⟨fun E hE => hs.2 E ((mem_list _ s E).mp hE),hs.1⟩
  · rw [vertices_cone]
    intro E hE
    rcases hE with rfl | hE
    · exact Finset.Subset.refl _
    · exact hs.2 E hE

lemma bary_mem_faceCarrier (s : Simplex V) :
    bary V (Finsupp.single s 1) ∈ faceCarrier V (finiteVertices V s) := by
  apply OrderBasedComplex.extend_mem _ _ _ _ (fun s => faceCarrier V (finiteVertices V s))
  · intro s _
    exact vertex_mem_faceCarrier V (simplexFace V s)
  · intro s c hc
    exact cone_mem_faceCarrier V (simplexFace V s) hc
  · intro s t ht
    exact faceCarrier_mono V (finiteVertices_boundary V ht)

noncomputable def choose (F : Face V) : V := F.property.choose
lemma choose_mem (F : Face V) : choose V F ∈ F.val := F.property.choose_spec
noncomputable def select : Chain (Face V) →ₗ[ℤ] Chain V := mapChain (Face V) (choose V)

noncomputable def unionFace (s : Simplex (Face V)) : Face V := by
  classical
  refine ⟨(finiteVertices (Face V) s).biUnion Subtype.val,?_⟩
  obtain ⟨v,hv⟩ := s.1.property
  exact ⟨v,Finset.mem_biUnion.mpr ⟨s.1,(mem_finiteVertices _ s _).mpr (head_mem_vertices _ _),hv⟩⟩

lemma mem_unionFace (s : Simplex (Face V)) (v : V) :
    v ∈ (unionFace V s).val ↔ ∃ F ∈ vertices (Face V) s, v ∈ F.val := by
  classical
  simp only [unionFace,Finset.mem_biUnion,mem_finiteVertices]

lemma face_subset_unionFace (s : Simplex (Face V)) (F : Face V)
    (hF : F ∈ vertices (Face V) s) : F.val ⊆ (unionFace V s).val :=
  fun _ hv => (mem_unionFace V s _).mpr ⟨F,hF,hv⟩

lemma unionFace_mono {s t : Simplex (Face V)}
    (h : vertices (Face V) s ⊆ vertices (Face V) t) :
    (unionFace V s).val ⊆ (unionFace V t).val := by
  intro v hv
  obtain ⟨F,hF,hv⟩ := (mem_unionFace V s v).mp hv
  exact (mem_unionFace V t v).mpr ⟨F,h hF,hv⟩

lemma Descending.face_le_head {s : Simplex (Face V)} (h : Descending V s)
    {F : Face V} (hF : F ∈ vertices (Face V) s) : F ≤ s.1 := by
  rcases hF with rfl | hF
  · exact le_refl _
  · exact (List.pairwise_cons.mp h).1 F hF

lemma Descending.unionFace_eq {s : Simplex (Face V)} (h : Descending V s) :
    unionFace V s = s.1 := by
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨F,hF,hv⟩ := (mem_unionFace V s v).mp hv
    exact h.face_le_head V hF hv
  · exact face_subset_unionFace V s s.1 (head_mem_vertices _ _)

lemma Descending.boundary {s t : Simplex (Face V)} (h : Descending V s)
    (ht : t ∈ (boundary (Face V) (Finsupp.single s 1)).support) : Descending V t :=
  h.sublist (boundary_sublist (Face V) s t ht)

lemma selected_vertices_subset (s : Simplex (Face V)) :
    finiteVertices V (choose V s.1,s.2.map (choose V)) ⊆ (unionFace V s).val := by
  intro v hv
  rw [mem_finiteVertices] at hv
  rcases hv with rfl | hv
  · exact face_subset_unionFace V s s.1 (head_mem_vertices _ _) (choose_mem V _)
  · obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hv
    exact face_subset_unionFace V s F (Or.inr hF) (choose_mem V _)

noncomputable def barySelect : Chain (Face V) →ₗ[ℤ] Chain (Face V) := (bary V).comp (select V)

lemma barySelect_mem_carrier (s : Simplex (Face V)) :
    barySelect V (Finsupp.single s 1) ∈ faceCarrier V (unionFace V s).val := by
  change bary V (mapChain _ _ (Finsupp.single s 1)) ∈ _
  rw [mapChain_single]
  exact faceCarrier_mono V (selected_vertices_subset V s) (bary_mem_faceCarrier V _)

noncomputable def backHomotopy : Chain (Face V) →ₗ[ℤ] Chain (Face V) :=
  OrderBasedComplex.homotopy (based (Face V)) (boundary (Face V)) (augmentation (Face V))
    (fun s => contraction (Face V) (unionFace V s)) LinearMap.id (barySelect V)

lemma boundary_backHomotopy (c : Chain (Face V)) :
    boundary (Face V) (backHomotopy V c) + backHomotopy V (boundary (Face V) c) =
      c - barySelect V c := by
  apply OrderBasedComplex.d_homotopy
  · intro d; rfl
  · intro d
    change boundary _ (bary V (mapChain _ _ d)) = bary V (mapChain _ _ (boundary _ d))
    rw [boundary_bary,boundary_mapChain]
  · intro d
    change augmentation _ d = augmentation _ (bary V (mapChain _ _ d))
    rw [augmentation_bary,augmentation_mapChain]

lemma backHomotopy_mem_carrier {s : Simplex (Face V)} (hs : Descending V s) :
    backHomotopy V (Finsupp.single s 1) ∈ faceCarrier V (unionFace V s).val := by
  apply OrderBasedComplex.homotopy_mem_on (based (Face V)) (boundary (Face V))
    (augmentation (Face V)) (fun s => contraction (Face V) (unionFace V s))
    LinearMap.id (barySelect V) (Descending V)
    (fun _ _ h ht => h.boundary V ht) (fun s => faceCarrier V (unionFace V s).val)
    _ _ _ _ s hs
  · intro s hs
    apply supported_single
    exact ⟨hs,fun F hF => face_subset_unionFace V s F hF⟩
  · intro s _
    exact barySelect_mem_carrier V s
  · intro s _ c hc
    exact cone_mem_faceCarrier V (unionFace V s) hc
  · intro s t _ ht
    exact faceCarrier_mono V (unionFace_mono V (boundary_vertices (Face V) s t ht))

lemma select_degree {n : ℕ} {c : Chain (Face V)} (hc : Homogeneous (Face V) n c) :
    Homogeneous V n (select V c) := by
  apply supported_linearMap (Face V) (P := fun s => degree (Face V) s = n)
    (Q := fun s => degree V s = n) (select V) _ hc
  intro s hs
  change Supported V _ (mapChain _ _ (Finsupp.single s 1))
  rw [mapChain_single]
  apply supported_single
  simpa [degree] using hs

lemma backHomotopy_degree {n : ℕ} {c : Chain (Face V)} (hc : Homogeneous (Face V) n c) :
    Homogeneous (Face V) (n+1) (backHomotopy V c) := by
  apply OrderBasedComplex.map_mem_of_support (backHomotopy V) (degreeModule (Face V) (n+1)) c
  intro s hs
  rw [← hc s hs]
  apply OrderBasedComplex.homotopy_degree (based (Face V)) (boundary (Face V))
    (augmentation (Face V)) (fun s => contraction (Face V) (unionFace V s))
    LinearMap.id (barySelect V) (degreeModule (Face V))
  · intro t
    exact supported_single (Face V) (P := fun s => degree (Face V) s = degree (Face V) t) rfl 1
  · intro t
    apply bary_degree
    apply select_degree
    exact supported_single (Face V) (P := fun s => degree (Face V) s = degree (Face V) t) rfl 1
  · intro t n d hd
    exact cone_mem_degreeModule _ _ hd
end

open OrderListChains
variable (V : Type*)

structure Complex where
  faces : Set (Finset V)
  down : ∀ {F E}, F ∈ faces → E ⊆ F → E ∈ faces

namespace Complex
variable (K : Complex V)
def tupleModule : Submodule ℤ (Chain V) :=
  Finsupp.supported ℤ ℤ {s | finiteVertices V s ∈ K.faces}
def faceModule : Submodule ℤ (Chain (Face V)) :=
  Finsupp.supported ℤ ℤ {s | Descending V s ∧ ∀ F ∈ vertices (Face V) s, F.val ∈ K.faces}

lemma carrier_le {F : Finset V} (hF : F ∈ K.faces) :
    faceCarrier V F ≤ K.faceModule V := by
  intro c hc s hs
  exact ⟨(hc hs).1,fun E hE => K.down hF ((hc hs).2 E hE)⟩

lemma bary_mem {c : Chain V} (hc : c ∈ K.tupleModule V) :
    bary V c ∈ K.faceModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  exact K.carrier_le V (hc hs) (bary_mem_faceCarrier V s)

lemma unionFace_mem {s : Simplex (Face V)}
    (hs : Descending V s ∧ ∀ F ∈ vertices (Face V) s, F.val ∈ K.faces) :
    (unionFace V s).val ∈ K.faces := by
  rw [hs.1.unionFace_eq V]
  exact hs.2 _ (head_mem_vertices _ _)

lemma select_mem {c : Chain (Face V)} (hc : c ∈ K.faceModule V) :
    select V c ∈ K.tupleModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  change Supported V _ (mapChain _ _ (Finsupp.single s 1))
  rw [mapChain_single]
  exact supported_single V (K.down (K.unionFace_mem V (hc hs))
    (selected_vertices_subset V s)) 1

lemma backHomotopy_mem {c : Chain (Face V)} (hc : c ∈ K.faceModule V) :
    backHomotopy V c ∈ K.faceModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs
  exact K.carrier_le V (K.unionFace_mem V (hc hs))
    (backHomotopy_mem_carrier V (hc hs).1)

lemma tuple_boundary_mem {c : Chain V} (hc : c ∈ K.tupleModule V) :
    boundary V c ∈ K.tupleModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs t ht
  exact K.down (hc hs) (finiteVertices_boundary V ht)

lemma face_boundary_mem {c : Chain (Face V)} (hc : c ∈ K.faceModule V) :
    boundary (Face V) c ∈ K.faceModule V := by
  apply OrderBasedComplex.map_mem_of_support
  intro s hs t ht
  exact ⟨(hc hs).1.boundary V ht,fun F hF =>
    (hc hs).2 F (boundary_vertices _ s t ht hF)⟩

theorem face_cycle_bounds {n : ℕ}
    (hfill : ∀ c : Chain V, c ∈ K.tupleModule V → Homogeneous V n c →
      boundary V c = 0 → augmentation V c = 0 →
      ∃ d : Chain V, d ∈ K.tupleModule V ∧ Homogeneous V (n+1) d ∧ boundary V d = c)
    {c : Chain (Face V)} (hc : c ∈ K.faceModule V)
    (hn : Homogeneous (Face V) n c) (hd : boundary (Face V) c = 0)
    (ha : augmentation (Face V) c = 0) :
    ∃ d : Chain (Face V), d ∈ K.faceModule V ∧ Homogeneous (Face V) (n+1) d ∧
      boundary (Face V) d = c := by
  have hsd : boundary V (select V c) = 0 := by
    change boundary V (mapChain _ _ c) = 0
    rw [boundary_mapChain,hd,map_zero]
  have hsa : augmentation V (select V c) = 0 := by
    change augmentation V (mapChain _ _ c) = 0
    rw [augmentation_mapChain,ha]
  obtain ⟨d,hdK,hdn,hdd⟩ := hfill (select V c) (K.select_mem V hc)
    (select_degree V hn) hsd hsa
  refine ⟨backHomotopy V c + bary V d,
    (K.faceModule V).add_mem (K.backHomotopy_mem V hc) (K.bary_mem V hdK),
    supported_add _ (backHomotopy_degree V hn) (bary_degree V hdn),?_⟩
  have hH := boundary_backHomotopy V c
  rw [hd,map_zero,add_zero] at hH
  rw [map_add,hH,boundary_bary,hdd]
  change c - barySelect V c + barySelect V c = c
  abel
end Complex

def fullComplex (T : Finset V) : Complex V where
  faces := {F | F ⊆ T}
  down := fun h h' => h'.trans h

def boundaryComplex (T : Finset V) : Complex V where
  faces := {F | F ⊆ T ∧ F.card < T.card}
  down := fun h h' => ⟨h'.trans h.1,lt_of_le_of_lt (Finset.card_le_card h') h.2⟩

open Classical in
lemma finiteVertices_cone (v : V) (s : Simplex V) :
    finiteVertices V (simplexCone V v s) = insert v (finiteVertices V s) := by
  classical
  ext w
  simp only [mem_finiteVertices,vertices_cone,Set.mem_insert_iff,Finset.mem_insert]

lemma cone_mem_boundary {T : Finset V} {v : V} (hv : v ∈ T) {n : ℕ}
    (hn : n+2 < T.card) {c : Chain V}
    (hc : c ∈ (boundaryComplex V T).tupleModule V) (hd : Homogeneous V n c) :
    cone V v c ∈ (boundaryComplex V T).tupleModule V := by
  classical
  change Supported V (fun s => finiteVertices V s ⊆ T ∧ (finiteVertices V s).card < T.card) (cone V v c)
  refine supported_cone V (P := fun s => finiteVertices V s ⊆ T ∧ degree V s = n)
    (Q := fun s => finiteVertices V s ⊆ T ∧ (finiteVertices V s).card < T.card) v ?_ ?_
  · intro s hs
    rw [finiteVertices_cone]
    refine ⟨Finset.insert_subset hv hs.1,?_⟩
    have hcard := Finset.card_insert_le v (finiteVertices V s)
    have hb := finiteVertices_card_le V s
    rw [hs.2] at hb
    omega
  · intro s hs
    exact ⟨(hc hs).1,hd s hs⟩

theorem boundary_face_cycle_bounds {T : Finset V} {n : ℕ} (hn : n+2 < T.card)
    {c : Chain (Face V)} (hc : c ∈ (boundaryComplex V T).faceModule V)
    (hd : Homogeneous (Face V) n c) (hz : boundary (Face V) c = 0)
    (ha : augmentation (Face V) c = 0) :
    ∃ d : Chain (Face V), d ∈ (boundaryComplex V T).faceModule V ∧
      Homogeneous (Face V) (n+1) d ∧ boundary (Face V) d = c := by
  apply Complex.face_cycle_bounds V (boundaryComplex V T) _ hc hd hz ha
  intro c hc hd hz ha
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
  refine ⟨cone V v c,cone_mem_boundary V hv hn hc hd,cone_mem_degreeModule V v hd,?_⟩
  rw [boundary_cone,hz,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]

theorem full_face_cycle_bounds {T : Finset V} (hT : T.Nonempty) {n : ℕ}
    {c : Chain (Face V)} (hc : c ∈ (fullComplex V T).faceModule V)
    (hd : Homogeneous (Face V) n c) (hz : boundary (Face V) c = 0)
    (ha : augmentation (Face V) c = 0) :
    ∃ d : Chain (Face V), d ∈ (fullComplex V T).faceModule V ∧
      Homogeneous (Face V) (n+1) d ∧ boundary (Face V) d = c := by
  classical
  apply Complex.face_cycle_bounds V (fullComplex V T) _ hc hd hz ha
  intro c hc hd hz ha
  obtain ⟨v,hv⟩ := hT
  refine ⟨cone V v c,?_,cone_mem_degreeModule V v hd,?_⟩
  · change Supported V (fun s => finiteVertices V s ⊆ T) (cone V v c)
    refine supported_cone V (P := fun s => finiteVertices V s ⊆ T)
      (Q := fun s => finiteVertices V s ⊆ T) v ?_ hc
    intro s hs
    rw [finiteVertices_cone]
    exact Finset.insert_subset hv hs
  · rw [boundary_cone,hz,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]
end SteinChains

end

end OAI
