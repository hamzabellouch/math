import Mathlib
import OAI.GroupTheory.FiniteType.PresentationGeometryFiniteStage

namespace OAI

noncomputable section
namespace FreeTensor

variable (ι κ : Type*)
abbrev Chains := (ι × κ) →₀ ℤ

def pure : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ) →ₗ[ℤ] Chains ι κ :=
  Finsupp.linearCombination ℤ (fun i =>
    Finsupp.linearCombination ℤ (fun k => Finsupp.single (i,k) 1))

@[simp] lemma pure_single_single (i : ι) (k : κ) (r s : ℤ) :
    pure ι κ (Finsupp.single i r) (Finsupp.single k s) = Finsupp.single (i,k) (r*s) := by
  simp [pure]

lemma pure_single_one (i : ι) (k : κ) :
    pure ι κ (Finsupp.single i 1) (Finsupp.single k 1) = Finsupp.single (i,k) 1 := by
  simp

variable {ι κ}

lemma ext {M : Type*} [AddCommGroup M] [Module ℤ M]
    {f g : Chains ι κ →ₗ[ℤ] M}
    (h : ∀ x y, f (pure ι κ x y) = g (pure ι κ x y)) : f = g := by
  apply Finsupp.lhom_ext
  rintro ⟨i,k⟩ r
  have hr : Finsupp.single (i,k) r = r • pure ι κ (Finsupp.single i 1) (Finsupp.single k 1) := by
    simp
  rw [hr, LinearMap.map_smul, LinearMap.map_smul, h]

variable (ι κ)

def map {ι' κ' : Type*} (f : (ι →₀ ℤ) →ₗ[ℤ] (ι' →₀ ℤ))
    (g : (κ →₀ ℤ) →ₗ[ℤ] (κ' →₀ ℤ)) : Chains ι κ →ₗ[ℤ] Chains ι' κ' :=
  Finsupp.linearCombination ℤ (fun s => pure ι' κ' (f (Finsupp.single s.1 1))
    (g (Finsupp.single s.2 1)))

lemma map_pure {ι' κ' : Type*} (f : (ι →₀ ℤ) →ₗ[ℤ] (ι' →₀ ℤ))
    (g : (κ →₀ ℤ) →ₗ[ℤ] (κ' →₀ ℤ)) (x : ι →₀ ℤ) (y : κ →₀ ℤ) :
    map ι κ f g (pure ι κ x y) = pure ι' κ' (f x) (g y) := by
  have h : ((pure ι κ).compr₂ (map ι κ f g)) =
      ((pure ι' κ').comp f).compl₂ g := by
    apply Finsupp.lhom_ext
    intro i r
    apply Finsupp.lhom_ext
    intro k s
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      pure_single_single, map, Finsupp.linearCombination_single]
    have hi : Finsupp.single i r = r • Finsupp.single i 1 := by simp
    have hk : Finsupp.single k s = s • Finsupp.single k 1 := by simp
    rw [hi, hk, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul,
      LinearMap.smul_apply, LinearMap.map_smul, smul_smul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

def lift {M : Type*} [AddCommGroup M] (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ) →ₗ[ℤ] M) :
    Chains ι κ →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ (fun s => f (Finsupp.single s.1 1) (Finsupp.single s.2 1))

lemma lift_pure {M : Type*} [AddCommGroup M]
    (f : (ι →₀ ℤ) →ₗ[ℤ] (κ →₀ ℤ) →ₗ[ℤ] M) (x : ι →₀ ℤ) (y : κ →₀ ℤ) :
    lift ι κ f (pure ι κ x y) = f x y := by
  have h : (pure ι κ).compr₂ (lift ι κ f) = f := by
    apply Finsupp.lhom_ext
    intro i r
    apply Finsupp.lhom_ext
    intro k s
    simp only [LinearMap.compr₂_apply, pure_single_single, lift,
      Finsupp.linearCombination_single]
    have hi : Finsupp.single i r = r • Finsupp.single i 1 := by simp
    have hk : Finsupp.single k s = s • Finsupp.single k 1 := by simp
    simp only [hi, hk, LinearMap.map_smul, LinearMap.smul_apply, smul_smul]
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

end FreeTensor

namespace ListChains
section

variable (G H : Type*)

abbrev BiChain := FreeTensor.Chains (Simplex G) (Simplex H)

abbrev tensor : Chain G →ₗ[ℤ] Chain H →ₗ[ℤ] BiChain G H :=
  FreeTensor.pure (Simplex G) (Simplex H)

abbrev tensorMap {G' H' : Type*} (f : Chain G →ₗ[ℤ] Chain G')
    (g : Chain H →ₗ[ℤ] Chain H') : BiChain G H →ₗ[ℤ] BiChain G' H' :=
  FreeTensor.map (Simplex G) (Simplex H) f g

lemma tensorMap_tensor {G' H' : Type*} (f : Chain G →ₗ[ℤ] Chain G')
    (g : Chain H →ₗ[ℤ] Chain H') (x : Chain G) (y : Chain H) :
    tensorMap G H f g (tensor G H x y) = tensor G' H' (f x) (g y) :=
  FreeTensor.map_pure ..

def biBoundary : BiChain G H →ₗ[ℤ] BiChain G H :=
  tensorMap G H (boundary G) LinearMap.id + tensorMap G H (sign G) (boundary H)

lemma biBoundary_tensor (x : Chain G) (y : Chain H) :
    biBoundary G H (tensor G H x y) =
      tensor G H (boundary G x) y + tensor G H (sign G x) (boundary H y) := by
  simp only [biBoundary, LinearMap.add_apply, tensorMap_tensor, LinearMap.id_apply]

lemma biBoundary_squared (c : BiChain G H) : biBoundary G H (biBoundary G H c) = 0 := by
  have he : biBoundary G H ∘ₗ biBoundary G H = 0 := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, biBoundary_tensor,
      map_add, boundary_boundary, map_zero,
      LinearMap.zero_apply, boundary_sign, map_neg, LinearMap.neg_apply,
      add_neg_cancel, add_zero, zero_add]
  exact LinearMap.congr_fun he c

def biAugmentation : BiChain G H →ₗ[ℤ] ℤ :=
  FreeTensor.lift (Simplex G) (Simplex H)
    (((LinearMap.mul ℤ ℤ).comp (augmentation G)).compl₂ (augmentation H))

lemma biAugmentation_tensor (x : Chain G) (y : Chain H) :
    biAugmentation G H (tensor G H x y) = augmentation G x * augmentation H y := by
  rw [biAugmentation, FreeTensor.lift_pure]
  rfl

lemma biAugmentation_boundary (c : BiChain G H) : biAugmentation G H (biBoundary G H c) = 0 := by
  have he : biAugmentation G H ∘ₗ biBoundary G H = 0 := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, biBoundary_tensor, map_add,
      biAugmentation_tensor, augmentation_boundary, zero_mul, mul_zero, zero_add]
  exact LinearMap.congr_fun he c

def biCone (a : G) (b : H) : BiChain G H →ₗ[ℤ] BiChain G H :=
  tensorMap G H (cone G a) LinearMap.id + tensorMap G H (K G a) (cone H b)

lemma biCone_tensor (a : G) (b : H) (x : Chain G) (y : Chain H) :
    biCone G H a b (tensor G H x y) =
      tensor G H (cone G a x) y + tensor G H (K G a x) (cone H b y) := by
  simp only [biCone, LinearMap.add_apply, tensorMap_tensor, LinearMap.id_apply]

lemma biBoundary_biCone (a : G) (b : H) (c : BiChain G H) :
    biBoundary G H (biCone G H a b c) + biCone G H a b (biBoundary G H c) =
      c - biAugmentation G H c • tensor G H (vertex G a) (vertex H b) := by
  have he : biBoundary G H ∘ₗ biCone G H a b + biCone G H a b ∘ₗ biBoundary G H =
      LinearMap.id - (biAugmentation G H).smulRight (tensor G H (vertex G a) (vertex H b)) := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smulRight_apply, biCone_tensor, biBoundary_tensor,
      map_add, LinearMap.add_apply, boundary_cone, boundary_K, sign_cone, sign_K,
      K_boundary, K_sign, map_zero, LinearMap.zero_apply, map_sub, LinearMap.sub_apply,
      map_neg, LinearMap.neg_apply, biAugmentation_tensor]
    simp only [K_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_smul]
    abel
  exact LinearMap.congr_fun he c

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

end ListChains

end

end OAI
