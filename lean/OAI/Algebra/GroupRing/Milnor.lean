import Mathlib
import OAI.Algebra.GroupRing.PartialLift

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology

namespace GroupRingTopology.Milnor

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u}
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def boundedInclusion (N : ℕ) : C(Simplicial.Space (bounded G N),Space G) :=
  ⟨Simplicial.inclusion (bounded G N) (complex G) (fun _ h => bounded_le G N h),
    Simplicial.continuous_inclusion _ _ _⟩

def boundedContraction (N : ℕ) (g : G) :
    (boundedInclusion (G := G) N).Homotopy (ContinuousMap.const _ (vertex (N,g))) := by
  let H := Simplicial.straightHomotopy (bounded G N) (complex G) id (fun _ => (N,g))
    (bounded_id_face N) (bounded_const_face N g) (bounded_contiguous N g)
  exact H.cast (ContinuousMap.ext (fun x => bounded_map_id N x))
    (ContinuousMap.ext (fun x => map_const_vertex (bounded G N) (N,g) (bounded_const_face N g) x))

lemma compactMap_bounded {A : Type v} [TopologicalSpace A] [CompactSpace A] (f : C(A,Space G)) :
    ∃ N : ℕ, ∃ F : C(A,Simplicial.Space (bounded G N)), (boundedInclusion N).comp F = f := by
  obtain ⟨S,hS⟩ := Simplicial.compact_bounded_vertices (complex G) (isCompact_range f.continuous)
  let N := S.sup Prod.fst + 1
  have hN (a : A) (v : ℕ × G) (hv : v ∈ (f a).1.support) : v.1 < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := Prod.fst) (hS (f a) (mem_range_self a) hv))
  let F : A → Simplicial.Space (bounded G N) := fun a =>
    ⟨(f a).1,(f a).2.1,(f a).2.2.1,(f a).2.2.2,hN a⟩
  have hc : Continuous F :=
    (Simplicial.inclusion_closedEmbedding (bounded G N) (complex G)
      (fun _ h => bounded_le G N h)).isEmbedding.continuous_iff.mpr f.continuous
  exact ⟨N,⟨F,hc⟩,rfl⟩

lemma compactMap_nullhomotopic {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (g : G) (f : C(A,Space G)) : ∃ y, Nonempty (f.Homotopy (ContinuousMap.const _ y)) := by
  obtain ⟨N,F,hF⟩ := compactMap_bounded f
  exact ⟨vertex (N,g),⟨((boundedContraction N g).compContinuousMap F).cast hF rfl⟩⟩

lemma sphereFillable (g : G) : Cellular.SphereFillable (Space G) := by
  intro n f
  cases n with
  | zero =>
    refine ⟨ContinuousMap.const _ (vertex (0,g)),?_⟩
    intro x
    have hx : False := by
      have he := x.2
      simp only [Metric.mem_sphere,Subsingleton.elim x.1 0,dist_self] at he
      exact zero_ne_one he
    exact hx.elim
  | succ n =>
    let := SphereTopology.sphere_nonempty n
    obtain ⟨y,⟨H⟩⟩ := compactMap_nullhomotopic g f
    obtain ⟨F,hF⟩ := SphereTopology.extends_of_nullhomotopic H.symm
    exact ⟨F,fun x => ContinuousMap.congr_fun hF x⟩

lemma contractible [Nonempty G] : ContractibleSpace (Space G) := by
  let g : G := Classical.choice ‹Nonempty G›
  let : Nonempty (Space G) := ⟨vertex (0,g)⟩
  exact Cellular.contractible_of_sphereFillable (sphereFillable g)

end

section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
universe u v
variable {G : Type u} [Group G]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def translate (g : G) (s : Finset (ℕ × G)) : Finset (ℕ × G) := s.image (fun v => (v.1,g*v.2))

lemma translate_one (s : Finset (ℕ × G)) : translate 1 s = s := by
  simp only [translate,one_mul,Prod.mk.eta,Finset.image_id']
lemma translate_mul (g h : G) (s : Finset (ℕ × G)) : translate g (translate h s) = translate (g*h) s := by
  simp only [translate,Finset.image_image,Function.comp_def,mul_assoc]
lemma translate_mono (g : G) {s t : Finset (ℕ × G)} (h : s ⊆ t) : translate g s ⊆ translate g t :=
  Finset.image_subset_image h
lemma translate_valid (g : G) {s : Finset (ℕ × G)} (hs : s ∈ complex G) : translate g s ∈ complex G :=
  map_face (g * ·) id Function.injective_id ⟨s,hs⟩

def orbitSpan (S : Finset (Finset (ℕ × G))) : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {t | t ∈ complex G ∧ ∃ g : G, ∃ s ∈ S, t ⊆ translate g s}
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨ht.1.1,?_⟩
    intro u hut hu
    obtain ⟨g,s,hs,hts⟩ := ht.2
    exact ⟨(complex G).isRelLowerSet_faces.mem_of_le ht.1 hut hu,g,s,hs,hut.trans hts⟩

lemma orbitSpan_le (S : Finset (Finset (ℕ × G))) : orbitSpan S ≤ complex G := fun _ h => h.1
lemma orbitSpan_mono {S T : Finset (Finset (ℕ × G))} (h : S ⊆ T) : orbitSpan S ≤ orbitSpan T := by
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  exact ⟨ht.1,g,s,h hs,hts⟩
lemma orbitSpan_contains (S : Finset (Finset (ℕ × G))) {t : Finset (ℕ × G)}
    (ht : t ∈ complex G) (h : ∃ s ∈ S, t ⊆ s) : t ∈ orbitSpan S := by
  obtain ⟨s,hs,hts⟩ := h
  exact ⟨ht,1,s,hs,by rwa [translate_one]⟩
lemma orbitSpan_invariant (S : Finset (Finset (ℕ × G))) (g : G)
    {t : Finset (ℕ × G)} (ht : t ∈ orbitSpan S) : translate g t ∈ orbitSpan S := by
  obtain ⟨h,s,hs,hts⟩ := ht.2
  exact ⟨translate_valid g ht.1,g*h,s,hs,by rw [←translate_mul]; exact translate_mono g hts⟩

lemma orbitSpan_bounded (S : Finset (Finset (ℕ × G))) :
    orbitSpan S ≤ bounded G ((S.biUnion id).sup Prod.fst + 1) := by
  intro t ht
  refine ⟨ht.1,?_⟩
  intro v hv
  obtain ⟨g,s,hs,hts⟩ := ht.2
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (hts hv)
  have hh : w.1 ≤ (S.biUnion id).sup Prod.fst := Finset.le_sup (f := Prod.fst) (Finset.mem_biUnion.mpr ⟨s,hs,hw⟩)
  exact Nat.lt_succ_of_le hh

/-- Uniform finite orbit control, not compactness of the infinite free orbit. -/
def Controlled (K : PreAbstractSimplicialComplex (ℕ × G)) : Prop :=
  ∃ S : Finset (Finset (ℕ × G)), K ≤ orbitSpan S

lemma controlled_orbitSpan (S : Finset (Finset (ℕ × G))) : Controlled (orbitSpan S) := ⟨S,le_rfl⟩
lemma controlled_bounded {K : PreAbstractSimplicialComplex (ℕ × G)} (hK : Controlled K) :
    ∃ N, K ≤ bounded G N := by
  obtain ⟨S,hS⟩ := hK
  exact ⟨_,hS.trans (orbitSpan_bounded S)⟩

lemma orbitSpan_finite_representatives (S : Finset (Finset (ℕ × G))) :
    ∃ T : Finset (Finset (ℕ × G)), ∀ t ∈ orbitSpan S, ∃ s ∈ T, ∃ g : G, t = translate g s := by
  refine ⟨S.biUnion Finset.powerset,?_⟩
  intro t ht
  obtain ⟨g,s,hs,hts⟩ := ht.2
  have hh : translate g⁻¹ t ⊆ s := by
    have hh := translate_mono g⁻¹ hts
    simpa only [translate_mul,inv_mul_cancel,translate_one] using hh
  refine ⟨translate g⁻¹ t,Finset.mem_biUnion.mpr ⟨s,hs,Finset.mem_powerset.mpr hh⟩,g,?_⟩
  rw [translate_mul,mul_inv_cancel,translate_one]

end
section
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def vertexMap (φ : G →* H) (α : ℕ → ℕ) : ℕ × G → ℕ × H := fun v => (α v.1,φ v.2)
def faceImage (φ : G →* H) (α : ℕ → ℕ) (s : Finset (ℕ × G)) : Finset (ℕ × H) := s.image (vertexMap φ α)
def imageShapes (φ : G →* H) (α : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) : Finset (Finset (ℕ × H)) := S.image (faceImage φ α)

lemma faceImage_translate (φ : G →* H) (α : ℕ → ℕ) (a : G) (s : Finset (ℕ × G)) :
    faceImage φ α (translate a s) = translate (φ a) (faceImage φ α s) := by
  simp only [faceImage,translate,Finset.image_image,vertexMap,Function.comp_def,map_mul]

lemma faceImage_valid (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G) : faceImage φ α s ∈ complex H :=
  map_face φ α hα ⟨s,hs⟩

lemma faceImage_controlled (φ : G →* H) (α : ℕ → ℕ) (hα : Function.Injective α)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∈ orbitSpan (imageShapes φ α S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨faceImage_valid φ α hα s.2.1,φ a,faceImage φ α t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [← faceImage_translate]
  exact Finset.image_subset_image hst

lemma unionFace_valid (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    {s : Finset (ℕ × G)} (hs : s ∈ complex G)
    (hc : ∀ v ∈ s, ∀ w ∈ s, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s ∪ faceImage φ β s ∈ complex H := by
  refine ⟨(faceImage_valid φ α hα hs).1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact (faceImage_valid φ α hα hs).2 hx hy hxy
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : v = w := hs.2 hv hw (hc v hv w hw hxy)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    have hvw : w = v := hs.2 hw hv (hc w hw v hv hxy.symm)
    subst w
    apply Prod.ext
    · exact hxy
    · rfl
  · exact (faceImage_valid φ β hβ hs).2 hx hy hxy

def unionShapes (φ : G →* H) (α β : ℕ → ℕ) (S : Finset (Finset (ℕ × G))) :
    Finset (Finset (ℕ × H)) := S.image (fun s => faceImage φ α s ∪ faceImage φ β s)

lemma translate_union (a : H) (s t : Finset (ℕ × H)) : translate a (s ∪ t) = translate a s ∪ translate a t :=
  Finset.image_union _ _

lemma unionFace_controlled (φ : G →* H) (α β : ℕ → ℕ)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (S : Finset (Finset (ℕ × G))) (s : Face (orbitSpan S))
    (hc : ∀ v ∈ s.1, ∀ w ∈ s.1, α v.1 = β w.1 → v.1 = w.1) :
    faceImage φ α s.1 ∪ faceImage φ β s.1 ∈ orbitSpan (unionShapes φ α β S) := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  refine ⟨unionFace_valid φ α β hα hβ s.2.1 hc,φ a,faceImage φ α t ∪ faceImage φ β t,
    Finset.mem_image.mpr ⟨t,ht,rfl⟩,?_⟩
  rw [translate_union,←faceImage_translate,←faceImage_translate]
  exact Finset.union_subset_union (Finset.image_subset_image hst) (Finset.image_subset_image hst)

/-- A fresh relayer fixes layer zero, so the ensuing straight homotopies are
based. Positive layers move above every old layer under consideration. -/
def fresh (N : ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else N+i
lemma fresh_zero (N : ℕ) : fresh N 0 = 0 := by simp [fresh]
lemma fresh_injective (N : ℕ) : Function.Injective (fresh N) := by
  intro i j h
  unfold fresh at h
  split_ifs at h with hi hj hj
  · exact hi.trans hj.symm
  · exfalso; omega
  · exfalso; omega
  · omega

lemma fresh_cross (N : ℕ) (α : ℕ → ℕ) (hα : Function.Injective α) (hzero : α 0 = 0)
    {i j : ℕ} (hi : α i < N) (h : α i = fresh N j) : i = j := by
  by_cases hj : j = 0
  · subst j
    apply hα
    simpa only [fresh_zero,hzero] using h
  · have hh : N ≤ fresh N j := by simp only [fresh,ite_eq_right hj]; exact Nat.le_add_right _ _
    omega
end
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def shapeBound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ) : ℕ :=
  (S.biUnion id).sup (fun v => α v.1) + 1
lemma orbit_below_bound (S : Finset (Finset (ℕ × G))) (α : ℕ → ℕ)
    (s : Face (orbitSpan S)) {v : ℕ × G} (hv : v ∈ s.1) : α v.1 < shapeBound S α := by
  obtain ⟨a,t,ht,hst⟩ := s.2.2
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp (hst hv)
  have hh : α w.1 ≤ (S.biUnion id).sup (fun v => α v.1) :=
    Finset.le_sup (f := fun v : ℕ × G => α v.1) (Finset.mem_biUnion.mpr ⟨t,ht,hw⟩)
  exact Nat.lt_succ_of_le hh

def relayerFresh (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) : ℕ → ℕ :=
  fresh (max (shapeBound S α) (shapeBound S β))
def relayerTarget (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ) :=
  unionShapes φ α (relayerFresh S α β) S ∪ unionShapes φ β (relayerFresh S α β) S

lemma relayerLeftValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hα : Function.Injective α) (hα0 : α 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ α s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_left
  apply unionFace_controlled φ α (relayerFresh S α β) hα (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ α hα hα0 ((orbit_below_bound S α s hv).trans_le (le_max_left _ _)) h

lemma relayerRightValid (φ : G →* H) (S : Finset (Finset (ℕ × G)))
    (α β : ℕ → ℕ) (hβ : Function.Injective β) (hβ0 : β 0 = 0) (s : Face (orbitSpan S)) :
    faceImage φ β s.1 ∪ faceImage φ (relayerFresh S α β) s.1 ∈ orbitSpan (relayerTarget φ S α β) := by
  apply orbitSpan_mono Finset.subset_union_right
  apply unionFace_controlled φ β (relayerFresh S α β) hβ (fresh_injective _) S s
  intro v hv w _ h
  exact fresh_cross _ β hβ hβ0 ((orbit_below_bound S β s hv).trans_le (le_max_right _ _)) h

variable (φ : G →* H) (S : Finset (Finset (ℕ × G))) (α β : ℕ → ℕ)
variable (hα : Function.Injective α) (hβ : Function.Injective β) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
include hα hα0 in
lemma relayerLeftMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ α) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_left (s.2.1.1.image _)
include hβ hβ0 in
lemma relayerRightMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ β) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerRightValid φ S α β hβ hβ0 s)
    Finset.subset_union_left (s.2.1.1.image _)
include hα hα0 in
lemma relayerFreshMapValid (s : Face (orbitSpan S)) :
    s.1.image (vertexMap φ (relayerFresh S α β)) ∈ orbitSpan (relayerTarget φ S α β) :=
  (orbitSpan _).isRelLowerSet_faces.mem_of_le (relayerLeftValid φ S α β hα hα0 s)
    Finset.subset_union_right (s.2.1.1.image _)

def relayerLeftMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ α) (relayerLeftMapValid φ S α β hα hα0)
def relayerRightMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ β) (relayerRightMapValid φ S α β hβ hβ0)
def relayerFreshMap := mapC (orbitSpan S) (orbitSpan (relayerTarget φ S α β))
  (vertexMap φ (relayerFresh S α β)) (relayerFreshMapValid φ S α β hα hα0)

def relayerLeftHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0)
def relayerRightHomotopy : (relayerRightMap φ S α β hβ hβ0).Homotopy (relayerFreshMap φ S α β hα hα0) :=
  straightHomotopy _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0)

def relayerHomotopy : (relayerLeftMap φ S α β hα hα0).Homotopy (relayerRightMap φ S α β hβ hβ0) :=
  (relayerLeftHomotopy φ S α β hα hα0).trans (relayerRightHomotopy φ S α β hα hβ hα0 hβ0).symm

lemma relayerLeftPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerLeftMap φ S α β hα hα0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ α) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hα0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl
lemma relayerRightPure (x : Simplicial.Space (orbitSpan S)) (g : G) (hx : x.1 = Finsupp.single (0,g) 1) :
    relayerRightMap φ S α β hβ hβ0 x = relayerFreshMap φ S α β hα hα0 x := by
  apply Subtype.ext
  change x.1.mapDomain (vertexMap φ β) = x.1.mapDomain (vertexMap φ (relayerFresh S α β))
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
  congr 1
  exact Prod.ext (hβ0.trans (fresh_zero (max (shapeBound S α) (shapeBound S β))).symm) rfl

lemma relayerLeftHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerLeftHomotopy φ S α β hα hα0 (t,x) = relayerLeftMap φ S α β hα hα0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerLeftValid φ S α β hα hα0) x
    (relayerLeftPure φ S α β hα hα0 x g hx) t
lemma relayerRightHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerRightHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerRightMap φ S α β hβ hβ0 x :=
  straightHomotopy_fixed _ _ _ _ _ _ (relayerRightValid φ S α β hβ hβ0) x
    (relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx) t

/-- The controlled relayer comparison is stationary on all layer-zero points. -/
theorem relayerHomotopy_fixed (x : Simplicial.Space (orbitSpan S)) (g : G)
    (hx : x.1 = Finsupp.single (0,g) 1) (t : I) :
    relayerHomotopy φ S α β hα hβ hα0 hβ0 (t,x) = relayerLeftMap φ S α β hα hα0 x := by
  rw [relayerHomotopy,ContinuousMap.Homotopy.trans_apply]
  split
  · exact relayerLeftHomotopy_fixed φ S α β hα hα0 x g hx _
  · rw [ContinuousMap.Homotopy.symm_apply]
    exact (relayerRightHomotopy_fixed φ S α β hα hβ hα0 hβ0 x g hx _).trans
      ((relayerRightPure φ S α β hα hβ hα0 hβ0 x g hx).trans
        (relayerLeftPure φ S α β hα hα0 x g hx).symm)
end GroupRingTopology.Milnor

/-! Functoriality and product additivity on actual higher homotopy groups.
This is geometric support for the literal finite idempotent diagrams. -/
namespace GroupRingTopology.HomotopyFunctor
open scoped Topology Topology.Homotopy
universe u v w
variable {N : Type u} {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y}

def loopMap (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.1,fun t ht => by change f (p t) = y; rw [GenLoop.boundary p t ht,hf]⟩

lemma loopMap_homotopic (f : C(X,Y)) (hf : f x = y) {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) : GenLoop.Homotopic (loopMap f hf p) (loopMap f hf q) :=
  h.comp_continuousMap f

def map (f : C(X,Y)) (hf : f x = y) : HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (loopMap f hf) (fun _ _ h => loopMap_homotopic f hf h)

@[simp] lemma map_mk (f : C(X,Y)) (hf : f x = y) (p : GenLoop N X x) :
    map f hf (Quotient.mk' p) = Quotient.mk' (loopMap f hf p) := rfl

lemma loopMap_const (f : C(X,Y)) (hf : f x = y) :
    loopMap (N := N) f hf GenLoop.const = GenLoop.const := by
  ext t
  exact hf

lemma loopMap_transAt [DecidableEq N] (i : N) (f : C(X,Y)) (hf : f x = y)
    (p q : GenLoop N X x) :
    loopMap f hf (GenLoop.transAt i p q) = GenLoop.transAt i (loopMap f hf p) (loopMap f hf q) := by
  ext t
  change f (if (t i : ℝ) ≤ 1/2 then p _ else q _) =
    if (t i : ℝ) ≤ 1/2 then f (p _) else f (q _)
  split <;> rfl

def mapHom [DecidableEq N] [Nonempty N] (f : C(X,Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := map f hf
  map_one' := by
    change Quotient.mk' (loopMap f hf GenLoop.const) = Quotient.mk' GenLoop.const
    exact congrArg Quotient.mk' (loopMap_const f hf)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    have h₁ := HomotopyGroup.mul_spec (i := Classical.arbitrary N) (p := p) (q := q)
    have h₂ := HomotopyGroup.mul_spec (i := Classical.arbitrary N)
      (p := loopMap f hf p) (q := loopMap f hf q)
    exact (congrArg (map f hf) h₁).trans
      ((congrArg Quotient.mk' (loopMap_transAt (Classical.arbitrary N) f hf q p)).trans h₂.symm)

lemma map_id (a : HomotopyGroup N X x) : map (y := x) (ContinuousMap.id X) rfl a = a := by
  induction a using Quotient.inductionOn with | h p =>
  exact congrArg Quotient.mk' (by ext t; rfl)

lemma map_comp {Z : Type*} [TopologicalSpace Z] {z : Z}
    (f : C(X,Y)) (hf : f x = y) (g : C(Y,Z)) (hg : g y = z)
    (a : HomotopyGroup N X x) :
    map g hg (map f hf a) = map (g.comp f) (by change g (f x) = z; rw [hf,hg]) a := by
  induction a using Quotient.inductionOn with | h p =>
  rfl

lemma map_const [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (ContinuousMap.const X y) rfl a = 1 := by
  induction a using Quotient.inductionOn with | h p =>
  rfl

variable {Z : Type*} [TopologicalSpace Z] {z : Z}

def loopPair (p : GenLoop N X x) (q : GenLoop N Y y) : GenLoop N (X × Y) (x,y) :=
  ⟨p.1.prodMk q.1,fun t ht => Prod.ext (GenLoop.boundary p t ht) (GenLoop.boundary q t ht)⟩

lemma pair_homotopic {p p' : GenLoop N X x} {q q' : GenLoop N Y y}
    (h : GenLoop.Homotopic p p') (k : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (loopPair p q) (loopPair p' q') := by
  rcases h with ⟨h⟩
  rcases k with ⟨k⟩
  refine ⟨{ toHomotopy := h.toHomotopy.prodMk k.toHomotopy,prop' := ?_ }⟩
  intro t a ha
  exact Prod.ext (h.eq_fst t ha) (k.eq_fst t ha)

lemma product_ext (a b : HomotopyGroup N (X × Y) (x,y))
    (h₁ : map ((ContinuousMap.fst : C(X × Y,X))) rfl a = map ((ContinuousMap.fst : C(X × Y,X))) rfl b)
    (h₂ : map ((ContinuousMap.snd : C(X × Y,Y))) rfl a = map ((ContinuousMap.snd : C(X × Y,Y))) rfl b) : a = b := by
  induction a using Quotient.inductionOn with | h p =>
  induction b using Quotient.inductionOn with | h q =>
  apply Quotient.sound
  have hh := pair_homotopic (Quotient.exact h₁) (Quotient.exact h₂)
  exact hh

/-- The diagonal class in a product is the product of its two coordinate
classes. This is a statement about genuine based homotopy groups. -/
lemma diagonal_split [DecidableEq N] [Nonempty N] (a : HomotopyGroup N X x) :
    map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl a =
      (map (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)) rfl a) *
      (map (y := (x,x)) ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)) rfl a) := by
  apply product_ext
  · change mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.fst : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) _ _ (map (y := (x,x)) _ _ a) =
      map (y := x) _ _ (map (y := (x,x)) _ _ a) * map (y := x) _ _ (map (y := (x,x)) _ _ a)
    erw [map_comp, map_comp, map_comp]
    change map (y := x) (ContinuousMap.id X) rfl a = map (y := x) (ContinuousMap.id X) rfl a * map (y := x) (ContinuousMap.const X x) rfl a
    erw [map_id,map_const,mul_one]
  · change mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _ = mapHom ((ContinuousMap.snd : C(X × X,X))) rfl _
    rw [map_mul]
    change map (y := x) _ _ (map (y := (x,x)) _ _ a) =
      map (y := x) _ _ (map (y := (x,x)) _ _ a) * map (y := x) _ _ (map (y := (x,x)) _ _ a)
    erw [map_comp, map_comp, map_comp]
    change map (y := x) (ContinuousMap.id X) rfl a = map (y := x) (ContinuousMap.const X x) rfl a * map (y := x) (ContinuousMap.id X) rfl a
    erw [map_id,map_const,one_mul]

/-- Product additivity requires no homological comparison or Hurewicz theorem. -/
theorem product_additivity [DecidableEq N] [Nonempty N] (F : C(X × X,Y))
    (hF : F (x,x) = y) (a : HomotopyGroup N X x) :
    map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.id X))) hF a =
      map (F.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X x))) hF a *
      map (F.comp ((ContinuousMap.const X x).prodMk (ContinuousMap.id X))) hF a := by
  have h := map_comp (y := (x,x)) ((ContinuousMap.id X).prodMk (ContinuousMap.id X)) rfl F hF a
  rw [← h,diagonal_split]
  change mapHom (N := N) F hF (_ * _) = _
  rw [map_mul]
  exact congrArg₂ (· * ·) (map_comp _ _ _ _ a) (map_comp _ _ _ _ a)
end GroupRingTopology.HomotopyFunctor

end

end OAI
