import Mathlib
import OAI.GroupTheory.FiniteType.BasedComplex
import OAI.GroupTheory.FiniteType.FreeTensor

namespace OAI

noncomputable section
namespace FreeTensor

variable (ι κ : Type*)

lemma pure_mem (K : Submodule ℤ (Chains ι κ)) (x : ι →₀ ℤ) (y : κ →₀ ℤ)
    (h : ∀ i ∈ x.support, ∀ k ∈ y.support, Finsupp.single (i,k) 1 ∈ K) :
    pure ι κ x y ∈ K := by
  apply BasedComplex.map_mem_of_support ((pure ι κ).flip y) K x
  intro i hi
  change pure ι κ (Finsupp.single i 1) y ∈ K
  apply BasedComplex.map_mem_of_support (pure ι κ (Finsupp.single i 1)) K y
  intro k hk
  rw [pure_single_one]
  exact h i hi k hk

lemma single_mem_supported {α : Type*} (S : Set α) {s : α} (hs : s ∈ S) (r : ℤ) :
    Finsupp.single s r ∈ Finsupp.supported ℤ ℤ S := by
  classical
  intro t ht
  have he : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
  simpa only [he] using hs

end FreeTensor

namespace ListChains
section

variable (G H : Type*)

def based : BasedComplex.Data (Simplex G) where
  degree := degree G
  d := boundary G
  aug := augmentation G
  d_squared := boundary_boundary G
  lowers := boundary_lowers G
  aug_single s := by simp only [augmentation_single, degree, List.length_eq_zero_iff]
  aug_d := augmentation_boundary G

def contraction (a : G) : BasedComplex.Contraction (boundary G) (augmentation G) where
  point := vertex G a
  cone := cone G a
  d_point := boundary_vertex G a
  aug_point := augmentation_vertex G a
  aug_cone := augmentation_cone G a
  identity c := by rw [boundary_cone, K_apply]; abel

def biDegree (s : Simplex G × Simplex H) : ℕ := degree G s.1 + degree H s.2

def biDegreeModule (n : ℕ) : Submodule ℤ (BiChain G H) :=
  Finsupp.supported ℤ ℤ {s | biDegree G H s = n}

def biVertexModule (V : Set G) (W : Set H) : Submodule ℤ (BiChain G H) :=
  Finsupp.supported ℤ ℤ {s | vertices G s.1 ⊆ V ∧ vertices H s.2 ⊆ W}

lemma tensor_mem_degree {p q : ℕ} {x : Chain G} {y : Chain H}
    (hx : x ∈ degreeModule G p) (hy : y ∈ degreeModule H q) :
    tensor G H x y ∈ biDegreeModule G H (p+q) := by
  apply FreeTensor.pure_mem
  intro s hs t ht
  apply FreeTensor.single_mem_supported
  exact congrArg₂ (· + ·) (hx hs) (hy ht)

lemma tensor_mem_vertices {V : Set G} {W : Set H} {x : Chain G} {y : Chain H}
    (hx : x ∈ vertexModule G V) (hy : y ∈ vertexModule H W) :
    tensor G H x y ∈ biVertexModule G H V W := by
  apply FreeTensor.pure_mem
  intro s hs t ht
  apply FreeTensor.single_mem_supported
  exact ⟨hx hs, hy ht⟩

lemma biBoundary_lowers (s t : Simplex G × Simplex H)
    (ht : t ∈ (biBoundary G H (Finsupp.single s 1)).support) :
    biDegree G H t + 1 = biDegree G H s := by
  let K : Submodule ℤ (BiChain G H) :=
    Finsupp.supported ℤ ℤ {t | biDegree G H t + 1 = biDegree G H s}
  suffices hc : biBoundary G H (Finsupp.single s 1) ∈ K by exact hc ht
  rw [← FreeTensor.pure_single_one, biBoundary_tensor]
  apply K.add_mem
  · apply FreeTensor.pure_mem
    intro x hx y hy
    have he : y = s.2 := Finset.mem_singleton.mp (Finsupp.support_single_subset hy)
    subst y
    apply FreeTensor.single_mem_supported
    have hl := boundary_lowers G s.1 x hx
    change degree G x + degree H s.2 + 1 = degree G s.1 + degree H s.2
    omega
  · rw [sign_single]
    apply FreeTensor.pure_mem
    intro x hx y hy
    have he : x = s.1 := Finset.mem_singleton.mp
      (Finsupp.support_single_subset (Finsupp.support_smul hx))
    subst x
    apply FreeTensor.single_mem_supported
    have hl := boundary_lowers H s.2 y hy
    change degree G s.1 + degree H y + 1 = degree G s.1 + degree H s.2
    omega

lemma biBoundary_vertices (s t : Simplex G × Simplex H)
    (ht : t ∈ (biBoundary G H (Finsupp.single s 1)).support) :
    vertices G t.1 ⊆ vertices G s.1 ∧ vertices H t.2 ⊆ vertices H s.2 := by
  suffices hc : biBoundary G H (Finsupp.single s 1) ∈
      biVertexModule G H (vertices G s.1) (vertices H s.2) by exact hc ht
  rw [← FreeTensor.pure_single_one, biBoundary_tensor]
  apply Submodule.add_mem
  · apply tensor_mem_vertices
    · exact fun _ hx => boundary_vertices G s.1 _ hx
    · exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
  · apply tensor_mem_vertices
    · rw [sign_single]
      apply Submodule.smul_mem
      exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
    · exact fun _ hy => boundary_vertices H s.2 _ hy

lemma biAugmentation_single (s : Simplex G × Simplex H) (r : ℤ) :
    biAugmentation G H (Finsupp.single s r) = if biDegree G H s = 0 then r else 0 := by
  have hr : Finsupp.single s r = r • tensor G H
      (Finsupp.single s.1 1) (Finsupp.single s.2 1) := by
    rw [FreeTensor.pure_single_one, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hr, LinearMap.map_smul, biAugmentation_tensor, augmentation_single, augmentation_single]
  simp only [biDegree, degree, Nat.add_eq_zero_iff, List.length_eq_zero_iff]
  split_ifs <;> simp_all

lemma biAugmentation_biCone (a : G) (b : H) (c : BiChain G H) :
    biAugmentation G H (biCone G H a b c) = 0 := by
  have he : biAugmentation G H ∘ₗ biCone G H a b = 0 := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, biCone_tensor, map_add,
      biAugmentation_tensor, augmentation_cone, zero_mul, mul_zero, add_zero]
  exact LinearMap.congr_fun he c

def biBased : BasedComplex.Data (Simplex G × Simplex H) where
  degree := biDegree G H
  d := biBoundary G H
  aug := biAugmentation G H
  d_squared := biBoundary_squared G H
  lowers := biBoundary_lowers G H
  aug_single s := biAugmentation_single G H s 1
  aug_d := biAugmentation_boundary G H

def biContraction (a : G) (b : H) :
    BasedComplex.Contraction (biBoundary G H) (biAugmentation G H) where
  point := tensor G H (vertex G a) (vertex H b)
  cone := biCone G H a b
  d_point := by simp only [biBoundary_tensor, boundary_vertex, map_zero,
    LinearMap.zero_apply, add_zero]
  aug_point := by rw [biAugmentation_tensor, augmentation_vertex, augmentation_vertex, mul_one]
  aug_cone := biAugmentation_biCone G H a b
  identity := biBoundary_biCone G H a b

lemma biVertexModule_mono {V V' : Set G} {W W' : Set H} (hV : V ⊆ V') (hW : W ⊆ W') :
    biVertexModule G H V W ≤ biVertexModule G H V' W' := by
  intro c hc s hs
  exact ⟨(hc hs).1.trans hV, (hc hs).2.trans hW⟩

lemma K_mem_vertices {V : Set G} {a : G} (ha : a ∈ V) (c : Chain G) :
    K G a c ∈ vertexModule G V := by
  rw [K_apply]
  exact (vertexModule G V).smul_mem _ (vertex_mem_vertexModule G ha)

lemma biCone_mem_vertices {V : Set G} {W : Set H} {a : G} {b : H}
    (ha : a ∈ V) (hb : b ∈ W) {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) : biCone G H a b c ∈ biVertexModule G H V W := by
  apply BasedComplex.map_mem_of_support (biCone G H a b) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, biCone_tensor]
  apply Submodule.add_mem
  · apply tensor_mem_vertices
    · apply cone_mem_vertexModule G ha
      exact FreeTensor.single_mem_supported _ (hc hs).1 1
    · exact FreeTensor.single_mem_supported _ (hc hs).2 1
  · apply tensor_mem_vertices
    · exact K_mem_vertices G ha _
    · apply cone_mem_vertexModule H hb
      exact FreeTensor.single_mem_supported _ (hc hs).2 1

lemma biCone_mem_degree {n : ℕ} (a : G) (b : H) {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : biCone G H a b c ∈ biDegreeModule G H (n+1) := by
  apply BasedComplex.map_mem_of_support (biCone G H a b) _ c
  intro s hs
  have hn : degree G s.1 + degree H s.2 = n := hc hs
  rw [← FreeTensor.pure_single_one, biCone_tensor]
  apply Submodule.add_mem
  · have he : n+1 = (degree G s.1+1) + degree H s.2 := by omega
    rw [he]
    apply tensor_mem_degree
    · apply cone_mem_degreeModule
      apply FreeTensor.single_mem_supported
      rfl
    · apply FreeTensor.single_mem_supported
      rfl
  · rw [K_apply, augmentation_single]
    by_cases hz : s.1.2 = []
    · rw [ite_eq_left hz, one_smul]
      have hd : degree G s.1 = 0 := by simp only [degree, hz, List.length_nil]
      have he : n+1 = 0 + (degree H s.2+1) := by omega
      rw [he]
      apply tensor_mem_degree
      · exact vertex_mem_degreeModule G a
      · apply cone_mem_degreeModule
        apply FreeTensor.single_mem_supported
        rfl
    · rw [ite_eq_right hz, zero_smul, map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _

lemma vertices_map {G' : Type*} (f : G → G') (s : Simplex G) :
    vertices G' (f s.1, s.2.map f) = f '' vertices G s := by
  ext x
  simp only [mem_vertices, List.mem_map, Set.mem_image]
  constructor
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨s.1, Or.inl rfl, rfl⟩
    · exact ⟨a, Or.inr ha, rfl⟩
  · rintro ⟨a, rfl | ha, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a, ha, rfl⟩

lemma mapChain_mem_vertices {G' : Type*} (f : G → G') {V : Set G} {W : Set G'}
    (hf : Set.MapsTo f V W) {c : Chain G} (hc : c ∈ vertexModule G V) :
    mapChain G f c ∈ vertexModule G' W := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  rw [mapChain_single]
  apply FreeTensor.single_mem_supported
  change vertices G' (f s.1, s.2.map f) ⊆ W
  rw [vertices_map]
  rintro _ ⟨a, ha, rfl⟩
  exact hf (hc hs ha)

lemma mapChain_mem_degree {G' : Type*} (f : G → G') {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : mapChain G f c ∈ degreeModule G' n := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  rw [mapChain_single]
  apply FreeTensor.single_mem_supported
  change degree G' (f s.1, s.2.map f) = n
  simp only [degree, List.length_map]
  exact hc hs

def diagTensor : Chain G →ₗ[ℤ] BiChain G G :=
  BasedComplex.extend (based G) (biBoundary G G) (biAugmentation G G)
    (fun s => biContraction G G s.1 s.1)

lemma biBoundary_diagTensor (c : Chain G) :
    biBoundary G G (diagTensor G c) = diagTensor G (boundary G c) :=
  BasedComplex.d_extend ..

lemma biAugmentation_diagTensor (c : Chain G) :
    biAugmentation G G (diagTensor G c) = augmentation G c :=
  BasedComplex.aug_extend ..

lemma diagTensor_single_vertices (s : Simplex G) :
    diagTensor G (Finsupp.single s 1) ∈
      biVertexModule G G (vertices G s) (vertices G s) := by
  apply BasedComplex.extend_mem (K := fun s =>
    biVertexModule G G (vertices G s) (vertices G s))
  · intro s _
    apply tensor_mem_vertices
    · exact vertex_mem_vertexModule G (head_mem_vertices G s)
    · exact vertex_mem_vertexModule G (head_mem_vertices G s)
  · intro s c hc
    exact biCone_mem_vertices G G (head_mem_vertices G s) (head_mem_vertices G s) hc
  · intro s t ht
    exact biVertexModule_mono G G (boundary_vertices G s t ht) (boundary_vertices G s t ht)

lemma diagTensor_mem_degree {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    diagTensor G c ∈ biDegreeModule G G n := by
  apply BasedComplex.map_mem_of_support (diagTensor G) _ c
  intro s hs
  have hn : degree G s = n := hc hs
  rw [← hn]
  apply BasedComplex.extend_degree (D := biDegreeModule G G)
  · intro s _
    exact tensor_mem_degree G G (vertex_mem_degreeModule G s.1) (vertex_mem_degreeModule G s.1)
  · intro s n c hc
    exact biCone_mem_degree G G s.1 s.1 hc

def productComparison : BiChain G H →ₗ[ℤ] Chain (G × H) :=
  BasedComplex.extend (biBased G H) (boundary (G × H)) (augmentation (G × H))
    (fun s => contraction (G × H) (s.1.1, s.2.1))

lemma boundary_productComparison (c : BiChain G H) :
    boundary (G × H) (productComparison G H c) = productComparison G H (biBoundary G H c) :=
  BasedComplex.d_extend ..

lemma augmentation_productComparison (c : BiChain G H) :
    augmentation (G × H) (productComparison G H c) = biAugmentation G H c :=
  BasedComplex.aug_extend ..

lemma productComparison_single_vertices (s : Simplex G × Simplex H) :
    productComparison G H (Finsupp.single s 1) ∈
      vertexModule (G × H) (vertices G s.1 ×ˢ vertices H s.2) := by
  apply BasedComplex.extend_mem (K := fun s : Simplex G × Simplex H =>
    vertexModule (G × H) (vertices G s.1 ×ˢ vertices H s.2))
  · intro s _
    exact vertex_mem_vertexModule (G × H)
      (V := vertices G s.1 ×ˢ vertices H s.2)
      ⟨head_mem_vertices G s.1, head_mem_vertices H s.2⟩
  · intro s c hc
    exact cone_mem_vertexModule (G × H)
      (V := vertices G s.1 ×ˢ vertices H s.2)
      ⟨head_mem_vertices G s.1, head_mem_vertices H s.2⟩ hc
  · intro s t ht
    apply vertexModule_mono
    exact Set.prod_mono (biBoundary_vertices G H s t ht).1 (biBoundary_vertices G H s t ht).2

lemma productComparison_mem_vertices {V : Set G} {W : Set H} {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) :
    productComparison G H c ∈ vertexModule (G × H) (V ×ˢ W) := by
  apply BasedComplex.map_mem_of_support (productComparison G H) _ c
  intro s hs
  apply vertexModule_mono (G × H) (Set.prod_mono (hc hs).1 (hc hs).2)
  exact productComparison_single_vertices G H s

lemma productComparison_mem_degree {n : ℕ} {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : productComparison G H c ∈ degreeModule (G × H) n := by
  apply BasedComplex.map_mem_of_support (productComparison G H) _ c
  intro s hs
  have hn : biDegree G H s = n := hc hs
  rw [← hn]
  apply BasedComplex.extend_degree (D := degreeModule (G × H))
  · intro s _
    exact vertex_mem_degreeModule (G × H) (s.1.1,s.2.1)
  · intro s n c hc
    exact cone_mem_degreeModule (G × H) (s.1.1,s.2.1) hc

def diagonalHomotopy : Chain G →ₗ[ℤ] Chain (G × G) :=
  BasedComplex.homotopy (based G) (boundary (G × G)) (augmentation (G × G))
    (fun s => contraction (G × G) (s.1,s.1))
    (mapChain G (fun a => (a,a))) (productComparison G G ∘ₗ diagTensor G)

lemma boundary_diagonalHomotopy (c : Chain G) :
    boundary (G × G) (diagonalHomotopy G c) + diagonalHomotopy G (boundary G c) =
      mapChain G (fun a => (a,a)) c - productComparison G G (diagTensor G c) := by
  apply BasedComplex.d_homotopy
  · exact boundary_mapChain G _
  · intro c
    change boundary (G × G) (productComparison G G (diagTensor G c)) = _
    rw [boundary_productComparison, biBoundary_diagTensor]
    rfl
  · intro c
    simp only [LinearMap.comp_apply, augmentation_mapChain,
      augmentation_productComparison, biAugmentation_diagTensor]

lemma diagonalHomotopy_single_vertices (s : Simplex G) :
    diagonalHomotopy G (Finsupp.single s 1) ∈
      vertexModule (G × G) (vertices G s ×ˢ vertices G s) := by
  apply BasedComplex.homotopy_mem (K := fun s =>
    vertexModule (G × G) (vertices G s ×ˢ vertices G s))
  · intro s
    exact mapChain_mem_vertices G (fun a => (a,a))
      (V := vertices G s) (W := vertices G s ×ˢ vertices G s) (fun _ ha => ⟨ha,ha⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)
  · intro s
    exact productComparison_mem_vertices G G (diagTensor_single_vertices G s)
  · intro s c hc
    exact cone_mem_vertexModule (G × G) (V := vertices G s ×ˢ vertices G s)
      ⟨head_mem_vertices G s, head_mem_vertices G s⟩ hc
  · intro s t ht
    exact vertexModule_mono (G × G)
      (Set.prod_mono (boundary_vertices G s t ht) (boundary_vertices G s t ht))

lemma diagonalHomotopy_mem_degree {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : diagonalHomotopy G c ∈ degreeModule (G × G) (n+1) := by
  apply BasedComplex.map_mem_of_support (diagonalHomotopy G) _ c
  intro s hs
  have hn : degree G s = n := hc hs
  rw [← hn]
  apply BasedComplex.homotopy_degree (D := degreeModule (G × G))
  · intro s
    apply mapChain_mem_degree
    apply FreeTensor.single_mem_supported
    rfl
  · intro s
    apply productComparison_mem_degree G G
    apply diagTensor_mem_degree G
    apply FreeTensor.single_mem_supported
    rfl
  · intro s n c hc
    exact cone_mem_degreeModule (G × G) (s.1,s.1) hc

end

variable (G : Type*)

lemma sign_squared (c : Chain G) : sign G (sign G c) = c := by
  have he : sign G ∘ₗ sign G = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, LinearMap.id_apply, sign_single,
      LinearMap.map_smul, smul_smul, ← mul_pow, mul_neg_one, neg_neg, one_pow, one_smul]
  exact LinearMap.congr_fun he c

lemma sign_eq_smul_of_degree {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    sign G c = (-1 : ℤ)^n • c := by
  have he := BasedComplex.linear_eq_on_support (sign G)
    ((-1 : ℤ)^n • (LinearMap.id : Chain G →ₗ[ℤ] Chain G)) c (by
      intro s hs
      rw [sign_single]
      change _ = (-1 : ℤ)^n • Finsupp.single s 1
      rw [hc hs])
  exact he

lemma sign_map_of_degree (F : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G n) (c : Chain G) :
    sign G (F c) = F (sign G c) := by
  have he : sign G ∘ₗ F = F ∘ₗ sign G := by
    apply Finsupp.lhom_ext
    intro s r
    have hs : Finsupp.single s r ∈ degreeModule G (degree G s) := by
      apply FreeTensor.single_mem_supported
      rfl
    simp only [LinearMap.comp_apply, sign_eq_smul_of_degree G (hF _ _ hs),
      sign_single, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma sign_map_of_raising (J : Chain G →ₗ[ℤ] Chain G)
    (hJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1)) (c : Chain G) :
    sign G (J c) = -J (sign G c) := by
  have he : sign G ∘ₗ J = -(J ∘ₗ sign G) := by
    apply Finsupp.lhom_ext
    intro s r
    have hs : Finsupp.single s r ∈ degreeModule G (degree G s) := by
      apply FreeTensor.single_mem_supported
      rfl
    simp only [LinearMap.comp_apply, LinearMap.neg_apply,
      sign_eq_smul_of_degree G (hJ _ _ hs), sign_single, LinearMap.map_smul,
      pow_succ, mul_neg_one, neg_smul]
  exact LinearMap.congr_fun he c

def tensorHomotopy (F F' J : Chain G →ₗ[ℤ] Chain G) : BiChain G G →ₗ[ℤ] BiChain G G :=
  tensorMap G G J F + tensorMap G G (F' ∘ₗ sign G) J

lemma tensorHomotopy_tensor (F F' J : Chain G →ₗ[ℤ] Chain G) (x y : Chain G) :
    tensorHomotopy G F F' J (tensor G G x y) =
      tensor G G (J x) (F y) + tensor G G (F' (sign G x)) (J y) := by
  simp only [tensorHomotopy, LinearMap.add_apply, tensorMap_tensor, LinearMap.comp_apply]

theorem boundary_tensorHomotopy (F F' J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ c, boundary G (F c) = F (boundary G c))
    (hF' : ∀ c, boundary G (F' c) = F' (boundary G c))
    (hJ : ∀ c, boundary G (J c) + J (boundary G c) = F c - F' c)
    (hdegF' : ∀ n c, c ∈ degreeModule G n → F' c ∈ degreeModule G n)
    (hdegJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1))
    (c : BiChain G G) :
    biBoundary G G (tensorHomotopy G F F' J c) +
        tensorHomotopy G F F' J (biBoundary G G c) =
      tensorMap G G F F c - tensorMap G G F' F' c := by
  have hdJ (c : Chain G) : boundary G (J c) = F c - F' c - J (boundary G c) :=
    eq_sub_iff_add_eq.mpr (hJ c)
  have he : biBoundary G G ∘ₗ tensorHomotopy G F F' J +
      tensorHomotopy G F F' J ∘ₗ biBoundary G G =
        tensorMap G G F F - tensorMap G G F' F' := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      tensorHomotopy_tensor, biBoundary_tensor, tensorMap_tensor,
      map_add, LinearMap.add_apply, hF, hF', hdJ, boundary_sign,
      sign_map_of_degree G F' hdegF', sign_map_of_raising G J hdegJ, sign_squared,
      map_neg, map_sub, LinearMap.neg_apply, LinearMap.sub_apply]
    abel
  exact LinearMap.congr_fun he c

end ListChains

end

end OAI
