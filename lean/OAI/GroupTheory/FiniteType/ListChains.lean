import Mathlib
import OAI.GroupTheory.FiniteType.FreeTensorPureMem

namespace OAI

noncomputable section
namespace ListChains
section

variable (G H : Type*)

def projectLeft : BiChain G H →ₗ[ℤ] Chain G :=
  FreeTensor.lift (Simplex G) (Simplex H)
    (((augmentation H).smulRight (LinearMap.id : Chain G →ₗ[ℤ] Chain G)).flip)

def projectRight : BiChain G H →ₗ[ℤ] Chain H :=
  FreeTensor.lift (Simplex G) (Simplex H)
    ((augmentation G).smulRight (LinearMap.id : Chain H →ₗ[ℤ] Chain H))

lemma projectLeft_tensor (x : Chain G) (y : Chain H) :
    projectLeft G H (tensor G H x y) = augmentation H y • x := by
  rw [projectLeft, FreeTensor.lift_pure]
  rfl

lemma projectRight_tensor (x : Chain G) (y : Chain H) :
    projectRight G H (tensor G H x y) = augmentation G x • y := by
  rw [projectRight, FreeTensor.lift_pure]
  rfl

lemma boundary_projectLeft (c : BiChain G H) :
    boundary G (projectLeft G H c) = projectLeft G H (biBoundary G H c) := by
  have he : boundary G ∘ₗ projectLeft G H = projectLeft G H ∘ₗ biBoundary G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, biBoundary_tensor, map_add, projectLeft_tensor,
      augmentation_boundary, zero_smul, add_zero, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma boundary_projectRight (c : BiChain G H) :
    boundary H (projectRight G H c) = projectRight G H (biBoundary G H c) := by
  have he : boundary H ∘ₗ projectRight G H = projectRight G H ∘ₗ biBoundary G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, biBoundary_tensor, map_add, projectRight_tensor,
      augmentation_boundary, augmentation_sign, zero_smul, zero_add, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma augmentation_projectLeft (c : BiChain G H) :
    augmentation G (projectLeft G H c) = biAugmentation G H c := by
  have he : augmentation G ∘ₗ projectLeft G H = biAugmentation G H := by
    apply FreeTensor.ext
    intro x y
    rw [LinearMap.comp_apply, projectLeft_tensor, LinearMap.map_smul,
      biAugmentation_tensor, smul_eq_mul, mul_comm]
  exact LinearMap.congr_fun he c

lemma augmentation_projectRight (c : BiChain G H) :
    augmentation H (projectRight G H c) = biAugmentation G H c := by
  have he : augmentation H ∘ₗ projectRight G H = biAugmentation G H := by
    apply FreeTensor.ext
    intro x y
    rw [LinearMap.comp_apply, projectRight_tensor, LinearMap.map_smul,
      biAugmentation_tensor, smul_eq_mul]
  exact LinearMap.congr_fun he c

lemma projectLeft_mem_vertices {V : Set G} {W : Set H} {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) : projectLeft G H c ∈ vertexModule G V := by
  apply BasedComplex.map_mem_of_support (projectLeft G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectLeft_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).1 1

lemma projectRight_mem_vertices {V : Set G} {W : Set H} {c : BiChain G H}
    (hc : c ∈ biVertexModule G H V W) : projectRight G H c ∈ vertexModule H W := by
  apply BasedComplex.map_mem_of_support (projectRight G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectRight_tensor]
  apply Submodule.smul_mem
  exact FreeTensor.single_mem_supported _ (hc hs).2 1

lemma projectLeft_mem_degree {n : ℕ} {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : projectLeft G H c ∈ degreeModule G n := by
  apply BasedComplex.map_mem_of_support (projectLeft G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectLeft_tensor, augmentation_single]
  split_ifs with hz
  · rw [one_smul]
    apply FreeTensor.single_mem_supported
    have hn : degree G s.1 + degree H s.2 = n := hc hs
    change degree G s.1 = n
    simpa only [degree, hz, List.length_nil, add_zero] using hn
  · rw [zero_smul]
    exact Submodule.zero_mem _

lemma projectRight_mem_degree {n : ℕ} {c : BiChain G H}
    (hc : c ∈ biDegreeModule G H n) : projectRight G H c ∈ degreeModule H n := by
  apply BasedComplex.map_mem_of_support (projectRight G H) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, projectRight_tensor, augmentation_single]
  split_ifs with hz
  · rw [one_smul]
    apply FreeTensor.single_mem_supported
    have hn : degree G s.1 + degree H s.2 = n := hc hs
    change degree H s.2 = n
    simpa only [degree, hz, List.length_nil, zero_add] using hn
  · rw [zero_smul]
    exact Submodule.zero_mem _

lemma augmentation_eq_zero_of_degree {n : ℕ} (hn : n ≠ 0) {c : Chain G}
    (hc : c ∈ degreeModule G n) : augmentation G c = 0 := by
  have he := BasedComplex.linear_eq_on_support (augmentation G)
    (0 : Chain G →ₗ[ℤ] ℤ) c (by
      intro s hs
      have hd : degree G s ≠ 0 := by rw [hc hs]; exact hn
      change (based G).aug (Finsupp.single s 1) = 0
      rw [(based G).aug_single]
      change (if degree G s = 0 then (1 : ℤ) else 0) = 0
      rw [ite_eq_right hd])
  exact he

def includeLeft (b : H) : Chain G →ₗ[ℤ] BiChain G H := (tensor G H).flip (vertex H b)
def includeRight (a : G) : Chain H →ₗ[ℤ] BiChain G H := tensor G H (vertex G a)

@[simp] lemma includeLeft_apply (b : H) (x : Chain G) :
    includeLeft G H b x = tensor G H x (vertex H b) := rfl
@[simp] lemma includeRight_apply (a : G) (y : Chain H) :
    includeRight G H a y = tensor G H (vertex G a) y := rfl

lemma biBoundary_includeLeft (b : H) (c : Chain G) :
    biBoundary G H (includeLeft G H b c) = includeLeft G H b (boundary G c) := by
  simp only [includeLeft_apply, biBoundary_tensor, boundary_vertex, map_zero, add_zero]

lemma biBoundary_includeRight (a : G) (c : Chain H) :
    biBoundary G H (includeRight G H a c) = includeRight G H a (boundary H c) := by
  simp only [includeRight_apply, biBoundary_tensor, boundary_vertex, map_zero,
    LinearMap.zero_apply, sign_vertex, zero_add]

lemma biAugmentation_includeLeft (b : H) (c : Chain G) :
    biAugmentation G H (includeLeft G H b c) = augmentation G c := by
  rw [includeLeft_apply, biAugmentation_tensor, augmentation_vertex, mul_one]

lemma biAugmentation_includeRight (a : G) (c : Chain H) :
    biAugmentation G H (includeRight G H a c) = augmentation H c := by
  rw [includeRight_apply, biAugmentation_tensor, augmentation_vertex, one_mul]

variable (a : G)

theorem tensorMap_extreme_degrees {n : ℕ} (hn : 0 < n)
    (T : Chain G →ₗ[ℤ] Chain G)
    (hT : ∀ m, m < n → ∀ c, c ∈ degreeModule G m → T c = K G a c)
    {c : BiChain G G} (hc : c ∈ biDegreeModule G G n) :
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
        rw [hT _ (by omega) _ hx, K_apply, hax, hay, one_smul, zero_smul,
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
          rw [hT _ (by omega) _ hy, K_apply, hax, hay, zero_smul, one_smul,
            map_zero, map_zero, zero_add]
          simp only [one_smul]
        · have hax : augmentation G (Finsupp.single s.1 1) = 0 :=
            augmentation_eq_zero_of_degree G hp hx
          have hay : augmentation G (Finsupp.single s.2 1) = 0 :=
            augmentation_eq_zero_of_degree G hq hy
          rw [hT _ (by omega) _ hx, hT _ (by omega) _ hy, K_apply, K_apply, hax, hay]
          simp only [zero_smul, map_zero, LinearMap.zero_apply, add_zero])
  exact he

end

variable (G H : Type*)

def localHomotopy (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H) :
    Chain G →ₗ[ℤ] Chain H :=
  BasedComplex.homotopy (based G) (boundary H) (augmentation H)
    (fun s => contraction H (v s.1)) F Q

lemma boundary_localHomotopy (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H)
    (hF : ∀ c, boundary H (F c) = F (boundary G c))
    (hQ : ∀ c, boundary H (Q c) = Q (boundary G c))
    (ha : ∀ c, augmentation H (F c) = augmentation H (Q c)) (c : Chain G) :
    boundary H (localHomotopy G H v F Q c) +
      localHomotopy G H v F Q (boundary G c) = F c - Q c :=
  BasedComplex.d_homotopy (based G) (boundary H) (augmentation H)
    (fun s => contraction H (v s.1)) F Q hF hQ ha c

lemma localHomotopy_single_vertices (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H)
    (Φ : Set G → Set H) (hmono : Monotone Φ)
    (hv : ∀ V x, x ∈ V → v x ∈ Φ V)
    (hF : ∀ s, F (Finsupp.single s 1) ∈ vertexModule H (Φ (vertices G s)))
    (hQ : ∀ s, Q (Finsupp.single s 1) ∈ vertexModule H (Φ (vertices G s)))
    (s : Simplex G) : localHomotopy G H v F Q (Finsupp.single s 1) ∈
        vertexModule H (Φ (vertices G s)) := by
  apply BasedComplex.homotopy_mem (K := fun s => vertexModule H (Φ (vertices G s)))
  · exact hF
  · exact hQ
  · intro s c hc
    exact cone_mem_vertexModule H (hv _ _ (head_mem_vertices G s)) hc
  · intro s t ht
    exact vertexModule_mono H (hmono (boundary_vertices G s t ht))

lemma localHomotopy_mem_degree (v : G → H) (F Q : Chain G →ₗ[ℤ] Chain H)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule H n)
    (hQ : ∀ n c, c ∈ degreeModule G n → Q c ∈ degreeModule H n)
    {n : ℕ} {c : Chain G} (hc : c ∈ degreeModule G n) :
    localHomotopy G H v F Q c ∈ degreeModule H (n+1) := by
  apply BasedComplex.map_mem_of_support (localHomotopy G H v F Q) _ c
  intro s hs
  have hn : degree G s = n := hc hs
  rw [← hn]
  apply BasedComplex.homotopy_degree (D := degreeModule H)
  · intro s
    apply hF
    apply FreeTensor.single_mem_supported
    rfl
  · intro s
    apply hQ
    apply FreeTensor.single_mem_supported
    rfl
  · intro s n c hc
    exact cone_mem_degreeModule H (v s.1) hc

lemma diagTensor_mem_vertices {V : Set G} {c : Chain G} (hc : c ∈ vertexModule G V) :
    diagTensor G c ∈ biVertexModule G G V V := by
  apply BasedComplex.map_mem_of_support (diagTensor G) _ c
  intro s hs
  exact biVertexModule_mono G G (hc hs) (hc hs) (diagTensor_single_vertices G s)

def projectionHomotopyLeft : Chain G →ₗ[ℤ] Chain G :=
  localHomotopy G G id (projectLeft G G ∘ₗ diagTensor G) LinearMap.id

def projectionHomotopyRight : Chain G →ₗ[ℤ] Chain G :=
  localHomotopy G G id (projectRight G G ∘ₗ diagTensor G) LinearMap.id

lemma boundary_projectionHomotopyLeft (c : Chain G) :
    boundary G (projectionHomotopyLeft G c) + projectionHomotopyLeft G (boundary G c) =
      projectLeft G G (diagTensor G c) - c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_projectLeft, biBoundary_diagTensor]
  · intro c
    rfl
  · intro c
    simp only [LinearMap.comp_apply, augmentation_projectLeft, biAugmentation_diagTensor,
      LinearMap.id_apply]

lemma boundary_projectionHomotopyRight (c : Chain G) :
    boundary G (projectionHomotopyRight G c) + projectionHomotopyRight G (boundary G c) =
      projectRight G G (diagTensor G c) - c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_projectRight, biBoundary_diagTensor]
  · intro c
    rfl
  · intro c
    simp only [LinearMap.comp_apply, augmentation_projectRight, biAugmentation_diagTensor,
      LinearMap.id_apply]

lemma projectionHomotopyLeft_single_vertices (s : Simplex G) :
    projectionHomotopyLeft G (Finsupp.single s 1) ∈ vertexModule G (vertices G s) := by
  apply localHomotopy_single_vertices G G id _ _ id
  · exact monotone_id
  · intro _ _ h
    exact h
  · intro s
    exact projectLeft_mem_vertices G G (diagTensor_single_vertices G s)
  · intro s
    exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1

lemma projectionHomotopyRight_single_vertices (s : Simplex G) :
    projectionHomotopyRight G (Finsupp.single s 1) ∈ vertexModule G (vertices G s) := by
  apply localHomotopy_single_vertices G G id _ _ id
  · exact monotone_id
  · intro _ _ h
    exact h
  · intro s
    exact projectRight_mem_vertices G G (diagTensor_single_vertices G s)
  · intro s
    exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1

lemma projectionHomotopyLeft_mem_degree {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : projectionHomotopyLeft G c ∈ degreeModule G (n+1) := by
  apply localHomotopy_mem_degree G G _ _ _ _ _ hc
  · intro n c hc
    exact projectLeft_mem_degree G G (diagTensor_mem_degree G hc)
  · intro n c hc
    exact hc

lemma projectionHomotopyRight_mem_degree {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : projectionHomotopyRight G c ∈ degreeModule G (n+1) := by
  apply localHomotopy_mem_degree G G _ _ _ _ _ hc
  · intro n c hc
    exact projectRight_mem_degree G G (diagTensor_mem_degree G hc)
  · intro n c hc
    exact hc

def endpointHomotopyLeft (b : H) : Chain G →ₗ[ℤ] Chain (G × H) :=
  localHomotopy G (G × H) (fun a => (a,b))
    (productComparison G H ∘ₗ includeLeft G H b) (mapChain G (fun a => (a,b)))

def endpointHomotopyRight (a : G) : Chain H →ₗ[ℤ] Chain (G × H) :=
  localHomotopy H (G × H) (fun b => (a,b))
    (productComparison G H ∘ₗ includeRight G H a) (mapChain H (fun b => (a,b)))

lemma boundary_endpointHomotopyLeft (b : H) (c : Chain G) :
    boundary (G × H) (endpointHomotopyLeft G H b c) +
      endpointHomotopyLeft G H b (boundary G c) =
        productComparison G H (includeLeft G H b c) - mapChain G (fun a => (a,b)) c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_productComparison, biBoundary_includeLeft]
  · exact boundary_mapChain G _
  · intro c
    simp only [LinearMap.comp_apply, augmentation_productComparison,
      biAugmentation_includeLeft, augmentation_mapChain]

lemma boundary_endpointHomotopyRight (a : G) (c : Chain H) :
    boundary (G × H) (endpointHomotopyRight G H a c) +
      endpointHomotopyRight G H a (boundary H c) =
        productComparison G H (includeRight G H a c) - mapChain H (fun b => (a,b)) c := by
  apply boundary_localHomotopy
  · intro c
    simp only [LinearMap.comp_apply, boundary_productComparison, biBoundary_includeRight]
  · exact boundary_mapChain H _
  · intro c
    simp only [LinearMap.comp_apply, augmentation_productComparison,
      biAugmentation_includeRight, augmentation_mapChain]

lemma endpointHomotopyLeft_single_vertices (b : H) (s : Simplex G) :
    endpointHomotopyLeft G H b (Finsupp.single s 1) ∈
      vertexModule (G × H) (vertices G s ×ˢ {b}) := by
  apply localHomotopy_single_vertices G (G × H) (fun a => (a,b)) _ _ (fun V => V ×ˢ {b})
  · intro V W h
    exact Set.prod_mono h (Set.Subset.refl _)
  · intro V x hx
    exact ⟨hx,rfl⟩
  · intro s
    apply productComparison_mem_vertices G H
    apply tensor_mem_vertices
    · exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
    · exact vertex_mem_vertexModule H rfl
  · intro s
    exact mapChain_mem_vertices G (fun a => (a,b))
      (V := vertices G s) (W := vertices G s ×ˢ {b}) (fun _ ha => ⟨ha,rfl⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma endpointHomotopyRight_single_vertices (a : G) (s : Simplex H) :
    endpointHomotopyRight G H a (Finsupp.single s 1) ∈
      vertexModule (G × H) ({a} ×ˢ vertices H s) := by
  apply localHomotopy_single_vertices H (G × H) (fun b => (a,b)) _ _ (fun V => {a} ×ˢ V)
  · intro V W h
    exact Set.prod_mono (Set.Subset.refl _) h
  · intro V x hx
    exact ⟨rfl,hx⟩
  · intro s
    apply productComparison_mem_vertices G H
    apply tensor_mem_vertices
    · exact vertex_mem_vertexModule G rfl
    · exact FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1
  · intro s
    exact mapChain_mem_vertices H (fun b => (a,b))
      (V := vertices H s) (W := {a} ×ˢ vertices H s) (fun _ ha => ⟨rfl,ha⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)

lemma endpointHomotopyLeft_mem_degree (b : H) {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) : endpointHomotopyLeft G H b c ∈ degreeModule (G × H) (n+1) := by
  apply localHomotopy_mem_degree G (G × H) _ _ _ _ _ hc
  · intro n c hc
    apply productComparison_mem_degree G H
    simpa only [add_zero, includeLeft_apply] using tensor_mem_degree G H hc (vertex_mem_degreeModule H b)
  · intro n c hc
    exact mapChain_mem_degree G _ hc

lemma endpointHomotopyRight_mem_degree (a : G) {n : ℕ} {c : Chain H}
    (hc : c ∈ degreeModule H n) : endpointHomotopyRight G H a c ∈ degreeModule (G × H) (n+1) := by
  apply localHomotopy_mem_degree H (G × H) _ _ _ _ _ hc
  · intro n c hc
    apply productComparison_mem_degree G H
    simpa only [zero_add, includeRight_apply] using tensor_mem_degree G H (vertex_mem_degreeModule G a) hc
  · intro n c hc
    exact mapChain_mem_degree H _ hc

lemma tensorMap_mem_degree {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G' n)
    (hQ : ∀ n c, c ∈ degreeModule H n → Q c ∈ degreeModule H' n)
    {n : ℕ} {c : BiChain G H} (hc : c ∈ biDegreeModule G H n) :
    tensorMap G H F Q c ∈ biDegreeModule G' H' n := by
  apply BasedComplex.map_mem_of_support (tensorMap G H F Q) _ c
  intro s hs
  have hn : degree G s.1 + degree H s.2 = n := hc hs
  rw [← hn, ← FreeTensor.pure_single_one, tensorMap_tensor]
  apply tensor_mem_degree
  · apply hF
    apply FreeTensor.single_mem_supported
    rfl
  · apply hQ
    apply FreeTensor.single_mem_supported
    rfl

lemma tensorMap_mem_vertices {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    {V : Set G} {W : Set H} {V' : Set G'} {W' : Set H'}
    (hF : ∀ c, c ∈ vertexModule G V → F c ∈ vertexModule G' V')
    (hQ : ∀ c, c ∈ vertexModule H W → Q c ∈ vertexModule H' W')
    {c : BiChain G H} (hc : c ∈ biVertexModule G H V W) :
    tensorMap G H F Q c ∈ biVertexModule G' H' V' W' := by
  apply BasedComplex.map_mem_of_support (tensorMap G H F Q) _ c
  intro s hs
  rw [← FreeTensor.pure_single_one, tensorMap_tensor]
  apply tensor_mem_vertices
  · exact hF _ (FreeTensor.single_mem_supported _ (hc hs).1 1)
  · exact hQ _ (FreeTensor.single_mem_supported _ (hc hs).2 1)

lemma sign_map_of_degree_between (F : Chain G →ₗ[ℤ] Chain H)
    (hF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule H n) (c : Chain G) :
    sign H (F c) = F (sign G c) := by
  have he : sign H ∘ₗ F = F ∘ₗ sign G := by
    apply Finsupp.lhom_ext
    intro s r
    have hs : Finsupp.single s r ∈ degreeModule G (degree G s) := by
      apply FreeTensor.single_mem_supported
      rfl
    simp only [LinearMap.comp_apply, sign_eq_smul_of_degree H (hF _ _ hs),
      sign_single, LinearMap.map_smul]
  exact LinearMap.congr_fun he c

lemma boundary_tensorMap {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    (hF : ∀ c, boundary G' (F c) = F (boundary G c))
    (hQ : ∀ c, boundary H' (Q c) = Q (boundary H c))
    (hdF : ∀ n c, c ∈ degreeModule G n → F c ∈ degreeModule G' n)
    (c : BiChain G H) :
    biBoundary G' H' (tensorMap G H F Q c) = tensorMap G H F Q (biBoundary G H c) := by
  have he : biBoundary G' H' ∘ₗ tensorMap G H F Q =
      tensorMap G H F Q ∘ₗ biBoundary G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, tensorMap_tensor, biBoundary_tensor, map_add,
      hF, hQ, sign_map_of_degree_between G G' F hdF]
  exact LinearMap.congr_fun he c

lemma biAugmentation_tensorMap {G' H' : Type*}
    (F : Chain G →ₗ[ℤ] Chain G') (Q : Chain H →ₗ[ℤ] Chain H')
    (hF : ∀ c, augmentation G' (F c) = augmentation G c)
    (hQ : ∀ c, augmentation H' (Q c) = augmentation H c)
    (c : BiChain G H) : biAugmentation G' H' (tensorMap G H F Q c) = biAugmentation G H c := by
  have he : biAugmentation G' H' ∘ₗ tensorMap G H F Q = biAugmentation G H := by
    apply FreeTensor.ext
    intro x y
    simp only [LinearMap.comp_apply, tensorMap_tensor, biAugmentation_tensor, hF, hQ]
  exact LinearMap.congr_fun he c

def mappedDiagonalHomotopy (f : G → H) : Chain G →ₗ[ℤ] Chain (H × H) :=
  localHomotopy G (H × H) (fun a => (f a, f a))
    (mapChain G (fun a => (f a, f a)))
    (productComparison H H ∘ₗ tensorMap G G (mapChain G f) (mapChain G f) ∘ₗ diagTensor G)

lemma boundary_mappedDiagonalHomotopy (f : G → H) (c : Chain G) :
    boundary (H × H) (mappedDiagonalHomotopy G H f c) +
      mappedDiagonalHomotopy G H f (boundary G c) =
        mapChain G (fun a => (f a, f a)) c -
        productComparison H H (tensorMap G G (mapChain G f) (mapChain G f) (diagTensor G c)) := by
  apply boundary_localHomotopy
  · exact boundary_mapChain G _
  · intro c
    simp only [LinearMap.comp_apply, boundary_productComparison]
    rw [boundary_tensorMap G G _ _ (boundary_mapChain G f) (boundary_mapChain G f)
      (fun _ _ hc => mapChain_mem_degree G f hc), biBoundary_diagTensor]
  · intro c
    simp only [LinearMap.comp_apply, augmentation_mapChain, augmentation_productComparison]
    rw [biAugmentation_tensorMap G G _ _ (augmentation_mapChain G f)
      (augmentation_mapChain G f), biAugmentation_diagTensor]

lemma mappedDiagonalHomotopy_single_vertices (f : G → H) (s : Simplex G) :
    mappedDiagonalHomotopy G H f (Finsupp.single s 1) ∈
      vertexModule (H × H) ((f '' vertices G s) ×ˢ (f '' vertices G s)) := by
  apply localHomotopy_single_vertices G (H × H) (fun a => (f a, f a)) _ _
    (fun V => (f '' V) ×ˢ (f '' V))
  · intro V W h
    exact Set.prod_mono (Set.image_mono h) (Set.image_mono h)
  · intro V x hx
    exact ⟨Set.mem_image_of_mem f hx,Set.mem_image_of_mem f hx⟩
  · intro s
    exact mapChain_mem_vertices G (fun a => (f a, f a))
      (V := vertices G s) (W := (f '' vertices G s) ×ˢ (f '' vertices G s))
      (fun _ hx => ⟨Set.mem_image_of_mem f hx, Set.mem_image_of_mem f hx⟩)
      (FreeTensor.single_mem_supported _ (Set.Subset.refl _) 1)
  · intro s
    apply productComparison_mem_vertices H H
    apply tensorMap_mem_vertices G G _ _ _ _ (diagTensor_single_vertices G s)
    · intro c hc
      exact mapChain_mem_vertices G f (fun _ hx => Set.mem_image_of_mem f hx) hc
    · intro c hc
      exact mapChain_mem_vertices G f (fun _ hx => Set.mem_image_of_mem f hx) hc

lemma mappedDiagonalHomotopy_mem_degree (f : G → H) {n : ℕ} {c : Chain G}
    (hc : c ∈ degreeModule G n) :
    mappedDiagonalHomotopy G H f c ∈ degreeModule (H × H) (n+1) := by
  apply localHomotopy_mem_degree G (H × H) _ _ _ _ _ hc
  · intro n c hc
    exact mapChain_mem_degree G _ hc
  · intro n c hc
    apply productComparison_mem_degree H H
    exact tensorMap_mem_degree G G _ _ (fun _ _ hc => mapChain_mem_degree G f hc)
      (fun _ _ hc => mapChain_mem_degree G f hc) (diagTensor_mem_degree G hc)

end ListChains

end

end OAI
