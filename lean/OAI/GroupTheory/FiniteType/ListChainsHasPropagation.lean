import Mathlib
import OAI.GroupTheory.FiniteType.ListChains

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*) [Group G] [Group H]

def hasPropagation (A : Set G) (s : Simplex G) : Prop :=
  ∀ x ∈ vertices G s, ∀ y ∈ vertices G s, x⁻¹ * y ∈ A

def controlledModule (A : Set G) : Submodule ℤ (Chain G) :=
  Finsupp.supported ℤ ℤ {s | hasPropagation G A s}

def biControlledModule (A : Set G) (B : Set H) : Submodule ℤ (BiChain G H) :=
  Finsupp.supported ℤ ℤ {s | hasPropagation G A s.1 ∧ hasPropagation H B s.2}

lemma controlledModule_mono {A B : Set G} (h : A ⊆ B) :
    controlledModule G A ≤ controlledModule G B := by
  intro c hc s hs x hx y hy
  exact h (hc hs x hx y hy)

lemma biControlledModule_mono {A A' : Set G} {B B' : Set H}
    (ha : A ⊆ A') (hb : B ⊆ B') :
    biControlledModule G H A B ≤ biControlledModule G H A' B' := by
  intro c hc s hs
  exact ⟨fun x hx y hy => ha ((hc hs).1 x hx y hy),
    fun x hx y hy => hb ((hc hs).2 x hx y hy)⟩

lemma vertexModule_le_controlledModule {V : Set G} {A : Set G}
    (h : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A) : vertexModule G V ≤ controlledModule G A := by
  intro c hc s hs x hx y hy
  exact h x (hc hs hx) y (hc hs hy)

lemma vertex_mem_controlledModule {A : Set G} (hA : 1 ∈ A) (a : G) :
    vertex G a ∈ controlledModule G A := by
  apply vertexModule_le_controlledModule G (V := {a}) _
    (vertex_mem_vertexModule G rfl)
  rintro x rfl y rfl
  simpa only [inv_mul_cancel] using hA

lemma boundary_mem_controlledModule {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : boundary G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (boundary G) _ c
  intro s hs
  apply vertexModule_le_controlledModule G (hc hs)
  exact boundary_mem_vertexModule G
    (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma sign_mem_controlledModule {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : sign G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (sign G) _ c
  intro s hs
  rw [sign_single]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs) 1

lemma tensor_mem_controlled {A : Set G} {B : Set H} {x : Chain G} {y : Chain H}
    (hx : x ∈ controlledModule G A) (hy : y ∈ controlledModule H B) :
    tensor G H x y ∈ biControlledModule G H A B := by
  apply FreeTensor.pure_mem
  intro s hs t ht
  apply FreeTensor.single_mem_supported
  exact ⟨hx hs,hy ht⟩

lemma biVertexModule_le_controlledModule {V : Set G} {W : Set H} {A : Set G} {B : Set H}
    (ha : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A)
    (hb : ∀ x ∈ W, ∀ y ∈ W, x⁻¹ * y ∈ B) :
    biVertexModule G H V W ≤ biControlledModule G H A B := by
  intro c hc s hs
  exact ⟨fun x hx y hy => ha x ((hc hs).1 hx) y ((hc hs).1 hy),
    fun x hx y hy => hb x ((hc hs).2 hx) y ((hc hs).2 hy)⟩

lemma vertexProduct_le_controlledModule {V : Set G} {W : Set H} {A : Set G} {B : Set H}
    (ha : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A)
    (hb : ∀ x ∈ W, ∀ y ∈ W, x⁻¹ * y ∈ B) :
    vertexModule (G × H) (V ×ˢ W) ≤ controlledModule (G × H) (A ×ˢ B) := by
  apply vertexModule_le_controlledModule
  intro x hx y hy
  exact ⟨ha x.1 hx.1 y.1 hy.1, hb x.2 hx.2 y.2 hy.2⟩

lemma diagTensor_mem_controlled {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : diagTensor G c ∈ biControlledModule G G A A := by
  apply BasedComplex.map_mem_of_support (diagTensor G) _ c
  intro s hs
  exact biVertexModule_le_controlledModule G G (hc hs) (hc hs)
    (diagTensor_single_vertices G s)

lemma productComparison_mem_controlled {A : Set G} {B : Set H} {c : BiChain G H}
    (hc : c ∈ biControlledModule G H A B) :
    productComparison G H c ∈ controlledModule (G × H) (A ×ˢ B) := by
  apply BasedComplex.map_mem_of_support (productComparison G H) _ c
  intro s hs
  exact vertexProduct_le_controlledModule G H (hc hs).1 (hc hs).2
    (productComparison_single_vertices G H s)

lemma projectLeft_mem_controlled {A : Set G} {B : Set H} {c : BiChain G H}
    (hc : c ∈ biControlledModule G H A B) : projectLeft G H c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (projectLeft G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectLeft_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).1 1

lemma projectRight_mem_controlled {A : Set G} {B : Set H} {c : BiChain G H}
    (hc : c ∈ biControlledModule G H A B) : projectRight G H c ∈ controlledModule H B := by
  apply BasedComplex.map_mem_of_support (projectRight G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectRight_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).2 1

lemma tensorMap_mem_controlled {G' H' : Type*} [Group G'] [Group H']
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    {A : Set G} {B : Set H} {A' : Set G'} {B' : Set H'}
    (hF : ∀ c, c ∈ controlledModule G A → F c ∈ controlledModule G' A')
    (hQ : ∀ c, c ∈ controlledModule H B → Q c ∈ controlledModule H' B')
    {c : BiChain G H} (hc : c ∈ biControlledModule G H A B) :
    tensorMap G H F Q c ∈ biControlledModule G' H' A' B' := by
  apply BasedComplex.map_mem_of_support (tensorMap G H F Q) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, tensorMap_tensor]
  apply tensor_mem_controlled
  · exact hF _ (FreeTensor.single_mem_supported _ (hc hs).1 1)
  · exact hQ _ (FreeTensor.single_mem_supported _ (hc hs).2 1)

lemma hom_image_propagation (f : G →* H) {V : Set G} {A : Set G}
    (h : ∀ x ∈ V, ∀ y ∈ V, x⁻¹ * y ∈ A) :
    ∀ x ∈ f '' V, ∀ y ∈ f '' V, x⁻¹ * y ∈ f '' A := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact ⟨x⁻¹*y, h x hx y hy, by simp only [map_mul, map_inv]⟩

lemma mapChain_mem_controlled (f : G →* H) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : mapChain G f c ∈ controlledModule H (f '' A) := by
  apply BasedComplex.map_mem_of_support (mapChain G f) _ c
  intro s hs
  apply vertexModule_le_controlledModule H (hom_image_propagation G H f (hc hs))
  exact mapChain_mem_vertices G f (fun _ hx => Set.mem_image_of_mem f hx)
    (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma projectionHomotopyLeft_mem_controlled {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : projectionHomotopyLeft G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (projectionHomotopyLeft G) _ c
  intro s hs
  exact vertexModule_le_controlledModule G (hc hs)
    (projectionHomotopyLeft_single_vertices G s)

lemma projectionHomotopyRight_mem_controlled {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : projectionHomotopyRight G c ∈ controlledModule G A := by
  apply BasedComplex.map_mem_of_support (projectionHomotopyRight G) _ c
  intro s hs
  exact vertexModule_le_controlledModule G (hc hs)
    (projectionHomotopyRight_single_vertices G s)

lemma endpointHomotopyLeft_mem_controlled (b : H) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    endpointHomotopyLeft G H b c ∈ controlledModule (G × H) (A ×ˢ {1}) := by
  apply BasedComplex.map_mem_of_support (endpointHomotopyLeft G H b) _ c
  intro s hs
  apply vertexProduct_le_controlledModule G H (hc hs) _
    (endpointHomotopyLeft_single_vertices G H b s)
  rintro x rfl y rfl
  simp only [Set.mem_singleton_iff, inv_mul_cancel]

lemma endpointHomotopyRight_mem_controlled (a : G) {A : Set H} {c : Chain H}
    (hc : c ∈ controlledModule H A) :
    endpointHomotopyRight G H a c ∈ controlledModule (G × H) ({1} ×ˢ A) := by
  apply BasedComplex.map_mem_of_support (endpointHomotopyRight G H a) _ c
  intro s hs
  apply vertexProduct_le_controlledModule G H _ (hc hs)
    (endpointHomotopyRight_single_vertices G H a s)
  rintro x rfl y rfl
  simp only [Set.mem_singleton_iff, inv_mul_cancel]

lemma mappedDiagonalHomotopy_mem_controlled (f : G →* H) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) : mappedDiagonalHomotopy G H f c ∈
      controlledModule (H × H) ((f '' A) ×ˢ (f '' A)) := by
  apply BasedComplex.map_mem_of_support (mappedDiagonalHomotopy G H f) _ c
  intro s hs
  exact vertexProduct_le_controlledModule H H (hom_image_propagation G H f (hc hs))
    (hom_image_propagation G H f (hc hs))
    (mappedDiagonalHomotopy_single_vertices G H f s)

end

section

variable (G : Type*) [Group G] (a : G)

theorem tensorMap_extreme_degrees_controlled {n : ℕ} (hn : 0 < n)
    (T : Chain G →ₗ[ℤ] Chain G)
    (A : Set G)
    (hT : ∀ m, m < n → ∀ c, c ∈ degreeModule G m →
      c ∈ controlledModule G A → T c = K G a c)
    {c : BiChain G G} (hc : c ∈ biDegreeModule G G n)
    (hca : c ∈ biControlledModule G G A A) :
    tensorMap G G T T c = includeRight G G a (T (projectRight G G c)) +
      includeLeft G G a (T (projectLeft G G c)) := by
  have he := BasedComplex.linear_eq_on_support (tensorMap G G T T)
    (includeRight G G a ∘ₗ T ∘ₗ projectRight G G +
      includeLeft G G a ∘ₗ T ∘ₗ projectLeft G G) c (by
      intro s hs
      have hdeg : degree G s.1 + degree G s.2 = n := hc hs
      have hx : Finsupp.single s.1 1 ∈ degreeModule G (degree G s.1) := by
        apply FreeTensor.single_mem_supported
        rfl
      have hy : Finsupp.single s.2 1 ∈ degreeModule G (degree G s.2) := by
        apply FreeTensor.single_mem_supported
        rfl
      have hxa : Finsupp.single s.1 1 ∈ controlledModule G A :=
        FreeTensor.single_mem_supported _ (hca hs).1 1
      have hya : Finsupp.single s.2 1 ∈ controlledModule G A :=
        FreeTensor.single_mem_supported _ (hca hs).2 1
      rw [← FreeTensor.pure_single_one]
      simp only [tensorMap_tensor, LinearMap.add_apply, LinearMap.comp_apply,
        projectRight_tensor, projectLeft_tensor, includeRight_apply, includeLeft_apply]
      by_cases hp : degree G s.1 = 0
      · have hq : degree G s.2 ≠ 0 := by omega
        have hax : augmentation G (Finsupp.single s.1 1) = 1 := by
          change (based G).aug (Finsupp.single s.1 1) = 1
          rw [(based G).aug_single]
          change (if degree G s.1 = 0 then (1 : ℤ) else 0) = 1
          rw [ite_eq_left hp]
        have hay : augmentation G (Finsupp.single s.2 1) = 0 :=
          augmentation_eq_zero_of_degree G hq hy
        rw [hT _ (by omega) _ hx hxa, K_apply, hax, hay, one_smul, zero_smul,
          map_zero, map_zero, LinearMap.zero_apply, add_zero]
        simp only [one_smul]
      · by_cases hq : degree G s.2 = 0
        · have hax : augmentation G (Finsupp.single s.1 1) = 0 :=
            augmentation_eq_zero_of_degree G hp hx
          have hay : augmentation G (Finsupp.single s.2 1) = 1 := by
            change (based G).aug (Finsupp.single s.2 1) = 1
            rw [(based G).aug_single]
            change (if degree G s.2 = 0 then (1 : ℤ) else 0) = 1
            rw [ite_eq_left hq]
          rw [hT _ (by omega) _ hy hya, K_apply, hax, hay, zero_smul, one_smul,
            map_zero, map_zero, zero_add]
          simp only [one_smul]
        · have hax : augmentation G (Finsupp.single s.1 1) = 0 :=
            augmentation_eq_zero_of_degree G hp hx
          have hay : augmentation G (Finsupp.single s.2 1) = 0 :=
            augmentation_eq_zero_of_degree G hq hy
          rw [hT _ (by omega) _ hx hxa, hT _ (by omega) _ hy hya, K_apply, K_apply, hax, hay]
          simp only [zero_smul, map_zero, LinearMap.zero_apply, add_zero])
  exact he

def perturbedMap (F J : Chain G →ₗ[ℤ] Chain G) : Chain G →ₗ[ℤ] Chain G :=
  F - boundary G ∘ₗ J - J ∘ₗ boundary G

omit [Group G] in
lemma perturbedMap_apply (F J : Chain G →ₗ[ℤ] Chain G) (c : Chain G) :
    perturbedMap G F J c = F c - boundary G (J c) - J (boundary G c) := rfl

omit [Group G] in
lemma boundary_perturbedMap (F J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ c, boundary G (F c) = F (boundary G c)) (c : Chain G) :
    boundary G (perturbedMap G F J c) = perturbedMap G F J (boundary G c) := by
  simp only [perturbedMap_apply, map_sub, boundary_boundary, map_zero, sub_zero, hF]

omit [Group G] in
lemma perturbation_homotopy (F J : Chain G →ₗ[ℤ] Chain G) (c : Chain G) :
    boundary G (J c) + J (boundary G c) = F c - perturbedMap G F J c := by
  rw [perturbedMap_apply]
  abel

omit [Group G] in
lemma boundary_eq_zero_of_degree_zero {c : Chain G} (hc : c ∈ degreeModule G 0) :
    boundary G c = 0 := by
  have he := BasedComplex.linear_eq_on_support (boundary G) (0 : Chain G →ₗ[ℤ] Chain G) c (by
    intro s hs
    exact BasedComplex.d_vertex (based G) (hc hs))
  exact he

omit [Group G] in
lemma perturbedMap_mem_degree (F J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G n)
    (hJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1))
    {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    perturbedMap G F J c ∈ degreeModule G n := by
  rw [perturbedMap_apply]
  apply Submodule.sub_mem
  · exact Submodule.sub_mem _ (hF _ _ hc) (boundary_mem_degreeModule G (hJ _ _ hc))
  · cases n with
    | zero =>
      rw [boundary_eq_zero_of_degree_zero G hc, map_zero]
      exact Submodule.zero_mem _
    | succ n => exact hJ _ _ (boundary_mem_degreeModule G hc)

omit [Group G] in
lemma perturbedMap_eq_on_cycle (F J : Chain G →ₗ[ℤ] Chain G) {c : Chain G}
    (hc : boundary G c = 0) (hj : J c = 0) : perturbedMap G F J c = F c := by
  simp only [perturbedMap_apply, hc, hj, map_zero, sub_zero]

omit [Group G] in
lemma perturbedMap_eq_on_lower (F J : Chain G →ₗ[ℤ] Chain G) {c : Chain G}
    (h : boundary G (J c) + J (boundary G c) = F c - K G a c) :
    perturbedMap G F J c = K G a c := by
  rw [perturbedMap_apply]
  calc F c - boundary G (J c) - J (boundary G c) =
      F c - (boundary G (J c) + J (boundary G c)) := by abel
    _ = K G a c := by rw [h, sub_sub_cancel]

lemma perturbedMap_mem_controlled (F J : Chain G →ₗ[ℤ] Chain G) {A B : Set G}
    (hF : ∀ c, c ∈ controlledModule G A → F c ∈ controlledModule G B)
    (hJ : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G B)
    {c : Chain G} (hc : c ∈ controlledModule G A) :
    perturbedMap G F J c ∈ controlledModule G B := by
  rw [perturbedMap_apply]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ (hF _ hc)
    (boundary_mem_controlledModule G (hJ _ hc))) (hJ _ (boundary_mem_controlledModule G hc))

omit [Group G] in
lemma sign_mem_degree {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    sign G c ∈ degreeModule G n := by
  rw [sign_eq_smul_of_degree G hc]
  exact Submodule.smul_mem _ _ hc

omit [Group G] in
lemma tensorHomotopy_mem_degree (F Q J : Chain G →ₗ[ℤ] Chain G)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G n)
    (hQ : ∀ n c, c ∈ degreeModule G n → Q c ∈ degreeModule G n)
    (hJ : ∀ n c, c ∈ degreeModule G n → J c ∈ degreeModule G (n+1))
    {n : ℕ} {c : BiChain G G} (hc : c ∈ biDegreeModule G G n) :
    tensorHomotopy G F Q J c ∈ biDegreeModule G G (n+1) := by
  apply BasedComplex.map_mem_of_support (tensorHomotopy G F Q J) _ c
  intro s hs
  have hn : degree G s.1 + degree G s.2 = n := hc hs
  have hx : Finsupp.single s.1 1 ∈ degreeModule G (degree G s.1) := by
    apply FreeTensor.single_mem_supported
    rfl
  have hy : Finsupp.single s.2 1 ∈ degreeModule G (degree G s.2) := by
    apply FreeTensor.single_mem_supported
    rfl
  rw [← FreeTensor.pure_single_one, tensorHomotopy_tensor]
  apply Submodule.add_mem
  · have he : n+1 = (degree G s.1+1) + degree G s.2 := by omega
    rw [he]
    exact tensor_mem_degree G G (hJ _ _ hx) (hF _ _ hy)
  · have he : n+1 = degree G s.1 + (degree G s.2+1) := by omega
    rw [he]
    exact tensor_mem_degree G G (hQ _ _ (sign_mem_degree G hx)) (hJ _ _ hy)

lemma tensorHomotopy_mem_controlled (F Q J : Chain G →ₗ[ℤ] Chain G) {A B : Set G}
    (hF : ∀ c, c ∈ controlledModule G A → F c ∈ controlledModule G B)
    (hQ : ∀ c, c ∈ controlledModule G A → Q c ∈ controlledModule G B)
    (hJ : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G B)
    {c : BiChain G G} (hc : c ∈ biControlledModule G G A A) :
    tensorHomotopy G F Q J c ∈ biControlledModule G G B B := by
  change tensorMap G G J F c + tensorMap G G (Q ∘ₗ sign G) J c ∈ _
  refine Submodule.add_mem _ ?_ ?_
  · exact tensorMap_mem_controlled G G J F hJ hF hc
  · have hQs (x : Chain G) (hx : x ∈ controlledModule G A) :
        (Q ∘ₗ sign G) x ∈ controlledModule G B := hQ _ (sign_mem_controlledModule G hx)
    exact tensorMap_mem_controlled G G (Q ∘ₗ sign G) J hQs hJ hc

end

variable (G : Type*) [Group G]

def additivityFilling (a : G) (f : G → G) (J : Chain G →ₗ[ℤ] Chain G) :
    Chain G →ₗ[ℤ] Chain (G × G) :=
  mappedDiagonalHomotopy G G f +
  productComparison G G ∘ₗ tensorHomotopy G (mapChain G f) (perturbedMap G (mapChain G f) J) J ∘ₗ diagTensor G +
  endpointHomotopyRight G G a ∘ₗ mapChain G f ∘ₗ projectRight G G ∘ₗ diagTensor G +
  endpointHomotopyLeft G G a ∘ₗ mapChain G f ∘ₗ projectLeft G G ∘ₗ diagTensor G +
  mapChain G (fun b => (a,b)) ∘ₗ mapChain G f ∘ₗ projectionHomotopyRight G +
  mapChain G (fun b => (b,a)) ∘ₗ mapChain G f ∘ₗ projectionHomotopyLeft G

theorem boundary_additivityFilling (a : G) (f : G → G)
    (J : Chain G →ₗ[ℤ] Chain G) {n : ℕ} (hn : 0 < n) (A : Set G)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
    (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
      boundary G (J c) + J (boundary G c) = mapChain G f c - K G a c)
    {z : Chain G} (hzd : z ∈ degreeModule G n) (hza : z ∈ controlledModule G A)
    (hz : boundary G z = 0) :
    boundary (G × G) (additivityFilling G a f J z) =
      mapChain G (fun b => (f b,f b)) z -
      mapChain G (fun b => (a,b)) (mapChain G f z) -
      mapChain G (fun b => (b,a)) (mapChain G f z) := by
  let F := mapChain G f
  let Q := perturbedMap G F J
  let d := diagTensor G z
  let r := projectRight G G d
  let l := projectLeft G G d
  have hFdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      F c ∈ degreeModule G m := mapChain_mem_degree G f hc
  have hQdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      Q c ∈ degreeModule G m := perturbedMap_mem_degree G F J hFdeg hJdeg hc
  have hFb (c : Chain G) : boundary G (F c) = F (boundary G c) := boundary_mapChain G f c
  have hd : biBoundary G G d = 0 := by
    dsimp only [d]
    rw [biBoundary_diagTensor, hz, map_zero]
  have hr : boundary G r = 0 := by
    dsimp only [r]
    rw [boundary_projectRight, hd, map_zero]
  have hl : boundary G l = 0 := by
    dsimp only [l]
    rw [boundary_projectLeft, hd, map_zero]
  have hrdeg : r ∈ degreeModule G n := projectRight_mem_degree G G (diagTensor_mem_degree G hzd)
  have hldeg : l ∈ degreeModule G n := projectLeft_mem_degree G G (diagTensor_mem_degree G hzd)
  have hQr : Q r = F r := perturbedMap_eq_on_cycle G F J hr (hJzero _ hrdeg)
  have hQl : Q l = F l := perturbedMap_eq_on_cycle G F J hl (hJzero _ hldeg)
  have hextreme : tensorMap G G Q Q d = includeRight G G a (F r) + includeLeft G G a (F l) := by
    rw [tensorMap_extreme_degrees_controlled G a hn Q A
      (fun m hm c hc ha => perturbedMap_eq_on_lower G a F J (hJlower m hm c hc ha))
      (diagTensor_mem_degree G hzd) (diagTensor_mem_controlled G hza), hQr, hQl]
  have h0 : boundary (G × G) (mappedDiagonalHomotopy G G f z) =
      mapChain G (fun b => (f b,f b)) z - productComparison G G (tensorMap G G F F d) := by
    have h := boundary_mappedDiagonalHomotopy G G f z
    simpa only [hz, map_zero, add_zero] using h
  have h1 : biBoundary G G (tensorHomotopy G F Q J d) =
      tensorMap G G F F d - (includeRight G G a (F r) + includeLeft G G a (F l)) := by
    have h := boundary_tensorHomotopy G F Q J (boundary_mapChain G f)
      (boundary_perturbedMap G F J (boundary_mapChain G f))
      (perturbation_homotopy G F J) hQdeg hJdeg d
    simpa only [hd, map_zero, add_zero, hextreme] using h
  have hFr : boundary G (F r) = 0 := by rw [boundary_mapChain, hr, map_zero]
  have hFl : boundary G (F l) = 0 := by rw [boundary_mapChain, hl, map_zero]
  have h2 : boundary (G × G) (endpointHomotopyRight G G a (F r)) =
      productComparison G G (includeRight G G a (F r)) - mapChain G (fun b => (a,b)) (F r) := by
    simpa only [hFr, map_zero, add_zero] using boundary_endpointHomotopyRight G G a (F r)
  have h3 : boundary (G × G) (endpointHomotopyLeft G G a (F l)) =
      productComparison G G (includeLeft G G a (F l)) - mapChain G (fun b => (b,a)) (F l) := by
    simpa only [hFl, map_zero, add_zero] using boundary_endpointHomotopyLeft G G a (F l)
  have h4 : boundary G (projectionHomotopyRight G z) = r - z := by
    simpa only [hz, map_zero, add_zero] using boundary_projectionHomotopyRight G z
  have h5 : boundary G (projectionHomotopyLeft G z) = l - z := by
    simpa only [hz, map_zero, add_zero] using boundary_projectionHomotopyLeft G z
  change boundary (G × G) (mappedDiagonalHomotopy G G f z +
    productComparison G G (tensorHomotopy G F Q J d) + endpointHomotopyRight G G a (F r) +
    endpointHomotopyLeft G G a (F l) +
    mapChain G (fun b => (a,b)) (F (projectionHomotopyRight G z)) +
    mapChain G (fun b => (b,a)) (F (projectionHomotopyLeft G z))) = _
  simp only [map_add, boundary_productComparison, boundary_mapChain, hFb, h0, h1, h2, h3, h4, h5,
    map_sub]
  dsimp only [F]
  abel

omit [Group G] in
lemma additivityFilling_mem_degree (a : G) (f : G → G) (J : Chain G →ₗ[ℤ] Chain G)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    {n : ℕ} {z : Chain G} (hzd : z ∈ degreeModule G n) :
    additivityFilling G a f J z ∈ degreeModule (G × G) (n+1) := by
  have hFdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      mapChain G f c ∈ degreeModule G m := mapChain_mem_degree G f hc
  have hQdeg (m : ℕ) (c : Chain G) (hc : c ∈ degreeModule G m) :
      perturbedMap G (mapChain G f) J c ∈ degreeModule G m :=
    perturbedMap_mem_degree G _ _ hFdeg hJdeg hc
  simp only [additivityFilling, LinearMap.add_apply, LinearMap.comp_apply]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact mappedDiagonalHomotopy_mem_degree G G f hzd
          · exact productComparison_mem_degree G G
              (tensorHomotopy_mem_degree G _ _ _ hFdeg hQdeg hJdeg (diagTensor_mem_degree G hzd))
        · exact endpointHomotopyRight_mem_degree G G a
            (hFdeg _ _ (projectRight_mem_degree G G (diagTensor_mem_degree G hzd)))
      · exact endpointHomotopyLeft_mem_degree G G a
          (hFdeg _ _ (projectLeft_mem_degree G G (diagTensor_mem_degree G hzd)))
    · exact mapChain_mem_degree G _ (hFdeg _ _ (projectionHomotopyRight_mem_degree G hzd))
  · exact mapChain_mem_degree G _ (hFdeg _ _ (projectionHomotopyLeft_mem_degree G hzd))

lemma fixedLeftMap_mem_controlled (a : G) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    mapChain G (fun b => (a,b)) c ∈ controlledModule (G × G) ({1} ×ˢ A) := by
  apply BasedComplex.map_mem_of_support (mapChain G (fun b => (a,b))) _ c
  intro s hs
  refine vertexProduct_le_controlledModule G G (V := {a}) (W := vertices G s) ?_ (hc hs) ?_
  · rintro x rfl y rfl
    simp only [Set.mem_singleton_iff, inv_mul_cancel]
  · exact mapChain_mem_vertices G (fun b => (a,b))
      (V := vertices G s) (W := {a} ×ˢ vertices G s) (fun _ hx => ⟨rfl,hx⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma fixedRightMap_mem_controlled (a : G) {A : Set G} {c : Chain G}
    (hc : c ∈ controlledModule G A) :
    mapChain G (fun b => (b,a)) c ∈ controlledModule (G × G) (A ×ˢ {1}) := by
  apply BasedComplex.map_mem_of_support (mapChain G (fun b => (b,a))) _ c
  intro s hs
  refine vertexProduct_le_controlledModule G G (V := vertices G s) (W := {a}) (hc hs) ?_ ?_
  · rintro x rfl y rfl
    simp only [Set.mem_singleton_iff, inv_mul_cancel]
  · exact mapChain_mem_vertices G (fun b => (b,a))
      (V := vertices G s) (W := vertices G s ×ˢ {a}) (fun _ hx => ⟨hx,rfl⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma additivityFilling_mem_controlled (a : G) (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
    {A B : Set G} (hB : 1 ∈ B) (hf : f '' A ⊆ B)
    (hJ : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G B)
    {z : Chain G} (hz : z ∈ controlledModule G A) :
    additivityFilling G a f J z ∈ controlledModule (G × G) (B ×ˢ B) := by
  have hF (c : Chain G) (hc : c ∈ controlledModule G A) :
      mapChain G f c ∈ controlledModule G B :=
    controlledModule_mono G hf (mapChain_mem_controlled G G f hc)
  have hQ (c : Chain G) (hc : c ∈ controlledModule G A) :
      perturbedMap G (mapChain G f) J c ∈ controlledModule G B :=
    perturbedMap_mem_controlled G _ _ hF hJ hc
  have hsingleton : ({1} : Set G) ⊆ B := Set.singleton_subset_iff.mpr hB
  have hr := hF _ (projectRight_mem_controlled G G (diagTensor_mem_controlled G hz))
  have hl := hF _ (projectLeft_mem_controlled G G (diagTensor_mem_controlled G hz))
  simp only [additivityFilling, LinearMap.add_apply, LinearMap.comp_apply]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · apply Submodule.add_mem
      · apply Submodule.add_mem
        · apply Submodule.add_mem
          · exact controlledModule_mono (G × G) (Set.prod_mono hf hf)
              (mappedDiagonalHomotopy_mem_controlled G G f hz)
          · exact productComparison_mem_controlled G G
              (tensorHomotopy_mem_controlled G _ _ _ hF hQ hJ (diagTensor_mem_controlled G hz))
        · exact controlledModule_mono (G × G) (Set.prod_mono hsingleton (Set.Subset.refl _))
            (endpointHomotopyRight_mem_controlled G G a hr)
      · exact controlledModule_mono (G × G) (Set.prod_mono (Set.Subset.refl _) hsingleton)
          (endpointHomotopyLeft_mem_controlled G G a hl)
    · exact controlledModule_mono (G × G) (Set.prod_mono hsingleton (Set.Subset.refl _))
        (fixedLeftMap_mem_controlled G a (hF _ (projectionHomotopyRight_mem_controlled G hz)))
  · exact controlledModule_mono (G × G) (Set.prod_mono (Set.Subset.refl _) hsingleton)
      (fixedRightMap_mem_controlled G a (hF _ (projectionHomotopyLeft_mem_controlled G hz)))

structure IsBound (A : Set G) : Prop where
  finite : A.Finite
  one_mem : 1 ∈ A
  inv_mem : ∀ a ∈ A, a⁻¹ ∈ A

lemma IsBound.union {A B : Set G} (ha : IsBound G A) (hb : IsBound G B) :
    IsBound G (A ∪ B) where
  finite := ha.finite.union hb.finite
  one_mem := Or.inl ha.one_mem
  inv_mem a h := h.elim (fun h => Or.inl (ha.inv_mem a h)) (fun h => Or.inr (hb.inv_mem a h))

lemma IsBound.image {H : Type*} [Group H] {A : Set G} (ha : IsBound G A) (f : G →* H) :
    IsBound H (f '' A) where
  finite := ha.finite.image f
  one_mem := ⟨1,ha.one_mem,f.map_one⟩
  inv_mem := by
    rintro _ ⟨a,ha',rfl⟩
    exact ⟨a⁻¹,ha.inv_mem a ha',f.map_inv a⟩

lemma IsBound.prod {H : Type*} [Group H] {A : Set G} {B : Set H}
    (ha : IsBound G A) (hb : IsBound H B) : IsBound (G × H) (A ×ˢ B) where
  finite := ha.finite.prod hb.finite
  one_mem := ⟨ha.one_mem,hb.one_mem⟩
  inv_mem a h := ⟨ha.inv_mem a.1 h.1,hb.inv_mem a.2 h.2⟩

theorem controlled_product_additivity (f : G →* G) (J : Chain G →ₗ[ℤ] Chain G)
    {n : ℕ} (hn : 0 < n) {A C : Set G} (hA : IsBound G A) (hC : IsBound G C)
    (hJdeg : ∀ m c, c ∈ degreeModule G m → J c ∈ degreeModule G (m+1))
    (hJzero : ∀ c, c ∈ degreeModule G n → J c = 0)
    (hJcontrol : ∀ c, c ∈ controlledModule G A → J c ∈ controlledModule G C)
    (hJlower : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → c ∈ controlledModule G A →
      boundary G (J c) + J (boundary G c) = mapChain G f c - K G 1 c) :
    ∃ B : Set (G × G), IsBound (G × G) B ∧
      ∀ z, z ∈ degreeModule G n → z ∈ controlledModule G A → boundary G z = 0 →
        ∃ w, w ∈ degreeModule (G × G) (n+1) ∧ w ∈ controlledModule (G × G) B ∧
          boundary (G × G) w = mapChain G (fun b => (f b,f b)) z -
            mapChain G (fun b => (1,b)) (mapChain G f z) -
            mapChain G (fun b => (b,1)) (mapChain G f z) := by
  let B := f '' A ∪ C
  have hB : IsBound G B := (hA.image G f).union G hC
  refine ⟨B ×ˢ B,hB.prod G hB,?_⟩
  intro z hzd hza hz
  refine ⟨additivityFilling G 1 f J z,additivityFilling_mem_degree G 1 f J hJdeg hzd,?_,?_⟩
  · exact additivityFilling_mem_controlled G 1 f J hB.one_mem Set.subset_union_left
      (fun c hc => controlledModule_mono G Set.subset_union_right (hJcontrol c hc)) hza
  · exact boundary_additivityFilling G 1 f J hn A hJdeg hJzero hJlower hzd hza hz

end ListChains

end

end OAI
