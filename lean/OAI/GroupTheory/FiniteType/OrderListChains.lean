import Mathlib
import OAI.GroupTheory.FiniteType.TwistedBrin

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
section

variable (G : Type*)

abbrev Simplex := G × List G
abbrev Chain := Simplex G →₀ ℤ

def simplexVertex (a : G) : Simplex G := (a, [])
def simplexCone (a : G) (s : Simplex G) : Simplex G := (a, s.1 :: s.2)
def vertex (a : G) : Chain G := Finsupp.single (simplexVertex G a) 1

def cone (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lmapDomain ℤ ℤ (simplexCone G a)

@[simp] lemma cone_single (a : G) (s : Simplex G) (r : ℤ) :
    cone G a (Finsupp.single s r) = Finsupp.single (simplexCone G a s) r := by
  simp [cone]

lemma single_cons (a b : G) (l : List G) (r : ℤ) :
    Finsupp.single (a,b::l) r = cone G a (Finsupp.single (b,l) r) :=
  (cone_single G a (b,l) r).symm

def augmentation : Chain G →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun s : Simplex G => if s.2 = [] then 1 else 0)

@[simp] lemma augmentation_single (s : Simplex G) (r : ℤ) :
    augmentation G (Finsupp.single s r) = if s.2 = [] then r else 0 := by
  simp only [augmentation, Finsupp.linearCombination_single, smul_eq_mul]
  split_ifs <;> simp

@[simp] lemma augmentation_vertex (a : G) : augmentation G (vertex G a) = 1 := by
  simp [vertex, simplexVertex]

@[simp] lemma augmentation_cone (a : G) (c : Chain G) :
    augmentation G (cone G a c) = 0 := by
  have h : augmentation G ∘ₗ cone G a = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

def K (a : G) : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.lsingle (simplexVertex G a) ∘ₗ augmentation G

@[simp] lemma K_apply (a : G) (c : Chain G) : K G a c = augmentation G c • vertex G a := by
  simp [K, vertex]

@[simp] lemma augmentation_K (a : G) (c : Chain G) :
    augmentation G (K G a c) = augmentation G c := by
  simp

private def boundaryAux (a : G) : List G → Chain G
  | [] => 0
  | b :: l => Finsupp.single (b,l) 1 - cone G a (boundaryAux b l) -
    (if l = [] then vertex G a else 0)

def boundary : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s => boundaryAux G s.1 s.2)

@[simp] lemma boundary_single (s : Simplex G) (r : ℤ) :
    boundary G (Finsupp.single s r) = r • boundaryAux G s.1 s.2 := by
  simp [boundary]

@[simp] lemma boundary_vertex (a : G) : boundary G (vertex G a) = 0 := by
  simp [vertex, simplexVertex, boundaryAux]

@[simp] lemma boundary_K (a : G) (c : Chain G) : boundary G (K G a c) = 0 := by
  simp

lemma boundary_cone (a : G) (c : Chain G) :
    boundary G (cone G a c) = c - cone G a (boundary G c) - K G a c := by
  have h : boundary G ∘ₗ cone G a = LinearMap.id - cone G a ∘ₗ boundary G - K G a := by
    apply Finsupp.lhom_ext
    rintro ⟨b,l⟩ r
    simp only [LinearMap.comp_apply, cone_single, boundary_single, simplexCone, boundaryAux,
      LinearMap.sub_apply, LinearMap.id_apply, K_apply, augmentation_single, map_smul]
    split_ifs <;> simp [smul_sub, Finsupp.smul_single]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_boundary (c : Chain G) : augmentation G (boundary G c) = 0 := by
  have h : augmentation G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    rintro ⟨a,l⟩ r
    cases l with
    | nil => simp [boundaryAux]
    | cons b l =>
      change augmentation G (boundary G (Finsupp.single (a,b::l) r)) = 0
      rw [single_cons]
      rw [boundary_cone]
      simp only [map_sub, augmentation_cone, augmentation_K, sub_zero, sub_self]
  exact LinearMap.congr_fun h c

@[simp] lemma K_boundary (a : G) (c : Chain G) : K G a (boundary G c) = 0 := by
  simp

@[simp] lemma boundary_boundary (c : Chain G) : boundary G (boundary G c) = 0 := by
  have hb (l : List G) (a : G) :
      boundary G (boundary G (Finsupp.single (a,l) 1)) = 0 := by
    induction l generalizing a with
    | nil =>
      change boundary G (boundary G (vertex G a)) = 0
      rw [boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [boundary_cone, map_sub, map_sub, boundary_cone, ih b]
      simp only [map_zero, K_boundary, boundary_K, sub_zero, sub_self]
  have h : boundary G ∘ₗ boundary G = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hr, map_smul, hb s.2 s.1,
      smul_zero]
  exact LinearMap.congr_fun h c

def degree (s : Simplex G) : ℕ := s.2.length

def Homogeneous (n : ℕ) (c : Chain G) : Prop :=
  ∀ s ∈ c.support, degree G s = n

def mapChain {H : Type*} (f : G → H) : Chain G →ₗ[ℤ] Chain H :=
  Finsupp.lmapDomain ℤ ℤ (fun s => (f s.1, s.2.map f))

@[simp] lemma mapChain_single {H : Type*} (f : G → H) (s : Simplex G) (r : ℤ) :
    mapChain G f (Finsupp.single s r) = Finsupp.single (f s.1, s.2.map f) r := by
  simp [mapChain]

@[simp] lemma mapChain_vertex {H : Type*} (f : G → H) (a : G) :
    mapChain G f (vertex G a) = vertex H (f a) := by
  simp [vertex, simplexVertex]

lemma mapChain_cone {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (cone G a c) = cone H (f a) (mapChain G f c) := by
  have h : mapChain G f ∘ₗ cone G a = cone H (f a) ∘ₗ mapChain G f := by
    apply Finsupp.lhom_ext
    intro s r
    simp [simplexCone]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    augmentation H (mapChain G f c) = augmentation G c := by
  have h : augmentation H ∘ₗ mapChain G f = augmentation G := by
    apply Finsupp.lhom_ext
    intro s r
    simp
  exact LinearMap.congr_fun h c

lemma mapChain_K {H : Type*} (f : G → H) (a : G) (c : Chain G) :
    mapChain G f (K G a c) = K H (f a) (mapChain G f c) := by
  simp

lemma boundary_mapChain {H : Type*} (f : G → H) (c : Chain G) :
    boundary H (mapChain G f c) = mapChain G f (boundary G c) := by
  have hb (l : List G) (a : G) :
      boundary H (mapChain G f (Finsupp.single (a,l) 1)) =
        mapChain G f (boundary G (Finsupp.single (a,l) 1)) := by
    induction l generalizing a with
    | nil =>
      change boundary H (mapChain G f (vertex G a)) = mapChain G f (boundary G (vertex G a))
      rw [mapChain_vertex, boundary_vertex, boundary_vertex, map_zero]
    | cons b l ih =>
      rw [single_cons]
      rw [mapChain_cone, boundary_cone, boundary_cone, map_sub, map_sub,
        mapChain_cone, mapChain_K, ih b]
  have he : boundary H ∘ₗ mapChain G f = mapChain G f ∘ₗ boundary G := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, hr, map_smul, hb s.2 s.1]
  exact LinearMap.congr_fun he c

def sign : Chain G →ₗ[ℤ] Chain G :=
  Finsupp.linearCombination ℤ (fun s : Simplex G => (-1 : ℤ) ^ degree G s • Finsupp.single s 1)

@[simp] lemma sign_single (s : Simplex G) (r : ℤ) :
    sign G (Finsupp.single s r) = (-1 : ℤ) ^ degree G s • Finsupp.single s r := by
  simp [sign, mul_comm]

@[simp] lemma sign_vertex (a : G) : sign G (vertex G a) = vertex G a := by
  simp [vertex, degree, simplexVertex]

lemma sign_cone (a : G) (c : Chain G) : sign G (cone G a c) = -cone G a (sign G c) := by
  have h : sign G ∘ₗ cone G a = -(cone G a ∘ₗ sign G) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, cone_single, sign_single,
      map_smul, degree, simplexCone, List.length_cons, pow_succ, mul_neg_one, neg_smul]
  exact LinearMap.congr_fun h c

@[simp] lemma augmentation_sign (c : Chain G) : augmentation G (sign G c) = augmentation G c := by
  have h : augmentation G ∘ₗ sign G = augmentation G := by
    apply Finsupp.lhom_ext
    rintro ⟨a,l⟩ r
    simp only [LinearMap.comp_apply, sign_single, map_smul, augmentation_single]
    cases l <;> simp [degree]
  exact LinearMap.congr_fun h c

@[simp] lemma sign_K (a : G) (c : Chain G) : sign G (K G a c) = K G a c := by
  simp

@[simp] lemma K_sign (a : G) (c : Chain G) : K G a (sign G c) = K G a c := by
  simp

lemma boundary_sign (c : Chain G) : boundary G (sign G c) = -sign G (boundary G c) := by
  have hb (l : List G) (a : G) : boundary G (sign G (Finsupp.single (a,l) 1)) =
      -sign G (boundary G (Finsupp.single (a,l) 1)) := by
    induction l generalizing a with
    | nil =>
      change boundary G (sign G (vertex G a)) = -sign G (boundary G (vertex G a))
      rw [sign_vertex, boundary_vertex, map_zero, neg_zero]
    | cons b l ih =>
      rw [single_cons, sign_cone, map_neg, boundary_cone, boundary_cone,
        map_sub, map_sub, ih b, map_neg, K_sign, sign_cone, sign_K]
  have h : boundary G ∘ₗ sign G = -(sign G ∘ₗ boundary G) := by
    apply Finsupp.lhom_ext
    intro s r
    have hr : Finsupp.single s r = r • Finsupp.single s 1 := by simp
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, hr, map_smul,
      hb s.2 s.1, smul_neg]
  exact LinearMap.congr_fun h c

def Supported (P : Simplex G → Prop) (c : Chain G) : Prop := ∀ s ∈ c.support, P s

lemma supported_zero (P : Simplex G → Prop) : Supported G P 0 := by simp [Supported]

lemma supported_add {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c+d) := by
  classical
  intro s hs
  obtain hs | hs := Finset.mem_union.mp (Finsupp.support_add hs)
  · exact hc s hs
  · exact hd s hs

lemma supported_neg {P : Simplex G → Prop} {c : Chain G}
    (hc : Supported G P c) : Supported G P (-c) := by
  simpa only [Supported, Finsupp.support_neg] using hc

lemma supported_sub {P : Simplex G → Prop} {c d : Chain G}
    (hc : Supported G P c) (hd : Supported G P d) : Supported G P (c-d) := by
  rw [sub_eq_add_neg]
  exact supported_add G hc (supported_neg G hd)

lemma supported_smul {P : Simplex G → Prop} {c : Chain G}
    (r : ℤ) (hc : Supported G P c) : Supported G P (r • c) :=
  fun s hs => hc s (Finsupp.support_smul hs)

lemma supported_single {P : Simplex G → Prop} {s : Simplex G} (hs : P s) (r : ℤ) :
    Supported G P (Finsupp.single s r) := by
  classical
  intro t ht
  have h : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  simpa only [h] using hs

lemma supported_mono {P Q : Simplex G → Prop} (hPQ : ∀ s, P s → Q s) {c : Chain G}
    (hc : Supported G P c) : Supported G Q c := fun s hs => hPQ s (hc s hs)

lemma supported_sum {ι : Type*} (t : Finset ι) {P : Simplex G → Prop}
    (c : ι → Chain G) (hc : ∀ i ∈ t, Supported G P (c i)) :
    Supported G P (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supported_zero G P
  | @insert i t hit ih =>
    rw [Finset.sum_insert hit]
    exact supported_add G (hc i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj)))

lemma supported_linearMap {H : Type*} {P : Simplex G → Prop} {Q : Simplex H → Prop}
    (T : Chain G →ₗ[ℤ] Chain H)
    (hT : ∀ s, P s → Supported H Q (T (Finsupp.single s 1)))
    {c : Chain G} (hc : Supported G P c) : Supported H Q (T c) := by
  classical
  have he : T c = ∑ s ∈ c.support, (c s) • T (Finsupp.single s 1) := by
    conv_lhs => rw [← Finsupp.sum_single c]
    rw [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [he]
  exact supported_sum H c.support _ (fun s hs => supported_smul H _ (hT s (hc s hs)))

end

variable (G : Type*)

def vertices (s : Simplex G) : Set G := {a | a = s.1 ∨ a ∈ s.2}

@[simp] lemma mem_vertices (s : Simplex G) (a : G) :
    a ∈ vertices G s ↔ a = s.1 ∨ a ∈ s.2 := Iff.rfl

lemma head_mem_vertices (s : Simplex G) : s.1 ∈ vertices G s := Or.inl rfl

lemma vertices_vertex (a : G) : vertices G (simplexVertex G a) = {a} := by
  ext x
  simp [vertices, simplexVertex]

lemma vertices_cone (a : G) (s : Simplex G) :
    vertices G (simplexCone G a s) = insert a (vertices G s) := by
  ext x
  simp [vertices, simplexCone]

lemma degree_cone (a : G) (s : Simplex G) :
    degree G (simplexCone G a s) = degree G s + 1 := rfl

lemma supported_cone {P Q : Simplex G → Prop} (a : G)
    (h : ∀ s, P s → Q (simplexCone G a s)) {c : Chain G}
    (hc : Supported G P c) : Supported G Q (cone G a c) := by
  refine supported_linearMap G (Q := Q) (cone G a) ?_ hc
  intro s hs
  rw [cone_single]
  exact supported_single G (h s hs) 1

theorem boundary_faces (s : Simplex G) :
    Supported G (fun t => degree G t + 1 = degree G s ∧ vertices G t ⊆ vertices G s)
      (boundary G (Finsupp.single s 1)) := by
  rcases s with ⟨a,l⟩
  induction l generalizing a with
  | nil =>
    change Supported G _ (boundary G (vertex G a))
    rw [boundary_vertex]
    exact supported_zero G _
  | cons b l ih =>
    rw [single_cons, boundary_cone]
    apply supported_sub
    · apply supported_sub
      · apply supported_single
        constructor
        · rfl
        · intro x hx
          exact Or.inr (by simpa only [vertices, Set.mem_ofPred_eq, List.mem_cons] using hx)
      · refine supported_cone G
          (Q := fun t => degree G t + 1 = degree G (a, b::l) ∧
            vertices G t ⊆ vertices G (a, b::l)) a ?_ (ih b)
        intro t ht
        constructor
        · change degree G t + 1 + 1 = l.length + 1
          exact congrArg (· + 1) ht.1
        · rw [vertices_cone]
          intro x hx
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (by simpa only [vertices, Set.mem_ofPred_eq, List.mem_cons] using ht.2 hx)
    · rw [K_apply, augmentation_single]
      by_cases hl : l = []
      · subst l
        rw [ite_eq_left rfl, one_smul]
        apply supported_single
        constructor
        · rfl
        · intro x hx
          exact Or.inl (by simpa only [vertices_vertex, Set.mem_singleton_iff] using hx)
      · rw [ite_eq_right hl, zero_smul]
        exact supported_zero G _

lemma boundary_lowers (s t : Simplex G)
    (ht : t ∈ (boundary G (Finsupp.single s 1)).support) :
    degree G t + 1 = degree G s := (boundary_faces G s t ht).1

lemma boundary_vertices (s t : Simplex G)
    (ht : t ∈ (boundary G (Finsupp.single s 1)).support) :
    vertices G t ⊆ vertices G s := (boundary_faces G s t ht).2

def vertexModule (V : Set G) : Submodule ℤ (Chain G) :=
  Finsupp.supported ℤ ℤ {s | vertices G s ⊆ V}

lemma mem_vertexModule {V : Set G} {c : Chain G} :
    c ∈ vertexModule G V ↔ Supported G (fun s => vertices G s ⊆ V) c := by
  rfl

lemma vertex_mem_vertexModule {V : Set G} {a : G} (ha : a ∈ V) :
    vertex G a ∈ vertexModule G V := by
  apply (mem_vertexModule G).mpr
  apply supported_single
  rw [vertices_vertex]
  exact Set.singleton_subset_iff.mpr ha

lemma cone_mem_vertexModule {V : Set G} {a : G} (ha : a ∈ V) {c : Chain G}
    (hc : c ∈ vertexModule G V) : cone G a c ∈ vertexModule G V := by
  apply (mem_vertexModule G).mpr
  refine supported_cone G (Q := fun s => vertices G s ⊆ V) a ?_
    ((mem_vertexModule G).mp hc)
  intro s hs
  rw [vertices_cone]
  exact Set.insert_subset ha hs

lemma boundary_mem_vertexModule {V : Set G} {c : Chain G}
    (hc : c ∈ vertexModule G V) : boundary G c ∈ vertexModule G V := by
  apply (mem_vertexModule G).mpr
  refine supported_linearMap G (Q := fun s => vertices G s ⊆ V) (boundary G) ?_
    ((mem_vertexModule G).mp hc)
  intro s hs
  exact fun t ht => (boundary_vertices G s t ht).trans hs

lemma vertexModule_mono {V W : Set G} (h : V ⊆ W) : vertexModule G V ≤ vertexModule G W := by
  intro c hc
  exact (mem_vertexModule G).mpr
    (supported_mono G (fun _ hs => hs.trans h) ((mem_vertexModule G).mp hc))

def degreeModule (n : ℕ) : Submodule ℤ (Chain G) :=
  Finsupp.supported ℤ ℤ {s | degree G s = n}

lemma mem_degreeModule {n : ℕ} {c : Chain G} :
    c ∈ degreeModule G n ↔ Homogeneous G n c := Iff.rfl

lemma cone_mem_degreeModule {n : ℕ} (a : G) {c : Chain G}
    (hc : c ∈ degreeModule G n) : cone G a c ∈ degreeModule G (n+1) := by
  refine supported_cone G (Q := fun s => degree G s = n+1) a ?_ hc
  intro s hs
  rw [degree_cone, hs]

lemma vertex_mem_degreeModule (a : G) : vertex G a ∈ degreeModule G 0 :=
  supported_single G (P := fun s => degree G s = 0) rfl 1

lemma boundary_mem_degreeModule {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G (n+1)) : boundary G c ∈ degreeModule G n := by
  refine supported_linearMap G (Q := fun s => degree G s = n) (boundary G) ?_ hc
  intro s hs t ht
  have hl := boundary_lowers G s t ht
  exact Nat.add_right_cancel (hl.trans hs)

end OrderListChains

end

end OAI
