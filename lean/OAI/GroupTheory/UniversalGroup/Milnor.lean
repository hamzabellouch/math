import OAI.GroupTheory.UniversalGroup.Simplicial

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
local instance (priority := 2000) (α : Type*) : DecidableEq α := Classical.decEq α
variable (G : Type u)

def complex : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {s | s.Nonempty ∧ Set.InjOn Prod.fst (s : Set (ℕ × G))}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1,fun t hts ht => ⟨ht,hs.2.mono hts⟩⟩

abbrev Space := Simplicial.Space (complex G)

lemma mem_complex (s : Finset (ℕ × G)) : s ∈ complex G ↔
    s.Nonempty ∧ Set.InjOn Prod.fst (s : Set (ℕ × G)) := Iff.rfl

def bounded (N : ℕ) : PreAbstractSimplicialComplex (ℕ × G) where
  faces := {s | s ∈ complex G ∧ ∀ v ∈ s, v.1 < N}
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1.1,fun t hts ht => ⟨(complex G).isRelLowerSet_faces.mem_of_le hs.1 hts ht,
      fun v hv => hs.2 v (hts hv)⟩⟩

lemma bounded_le (N : ℕ) : bounded G N ≤ complex G := fun _ hs => hs.1
lemma bounded_mono {N M : ℕ} (h : N ≤ M) : bounded G N ≤ bounded G M :=
  fun _ hs => ⟨hs.1,fun v hv => lt_of_lt_of_le (hs.2 v hv) h⟩

variable {G} {H : Type v}
lemma map_face (φ : G → H) (ρ : ℕ → ℕ) (hρ : Function.Injective ρ)
    (s : Face (complex G)) : s.1.image (fun v => (ρ v.1,φ v.2)) ∈ complex H := by
  refine ⟨s.2.1.image _,?_⟩
  rintro a ha b hb hab
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
  exact congrArg (fun v : ℕ × G => (ρ v.1,φ v.2)) (s.2.2 hx hy (hρ hab))

def map (φ : G → H) (ρ : ℕ → ℕ) (hρ : Function.Injective ρ) : C(Space G,Space H) :=
  Simplicial.mapC (complex G) (complex H) (fun v => (ρ v.1,φ v.2)) (map_face φ ρ hρ)

lemma map_comp {J : Type*} (φ : G → H) (ψ : H → J)
    (ρ τ : ℕ → ℕ) (hρ : Function.Injective ρ) (hτ : Function.Injective τ) (x : Space G) :
    map ψ τ hτ (map φ ρ hρ x) = map (ψ ∘ φ) (τ ∘ ρ) (hτ.comp hρ) x :=
by
  apply Subtype.ext
  exact Finsupp.mapDomain_comp.symm

lemma map_id (x : Space G) : map id id Function.injective_id x = x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

def vertex (v : ℕ × G) : Space G :=
  ⟨Finsupp.single v 1,by intro w; simp only [Finsupp.single_apply]; split_ifs <;> norm_num,
    by simp,by
      simp only [Finsupp.support_single _ one_ne_zero]
      exact ⟨Finset.singleton_nonempty v,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst v⟩⟩

lemma bounded_union_apex (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1 ∪ {(N,g)} ∈ complex G := by
  refine ⟨s.2.1.1.mono Finset.subset_union_left,?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact s.2.1.2 hx hy hxy
  · have hyy := Finset.mem_singleton.mp hy
    subst y
    exact False.elim ((Nat.ne_of_lt (s.2.2 x hx)) hxy)
  · have hxx := Finset.mem_singleton.mp hx
    subst x
    exact False.elim ((Nat.ne_of_lt (s.2.2 y hy)) hxy.symm)
  · exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm

lemma bounded_id_face (N : ℕ) (s : Face (bounded G N)) : s.1.image id ∈ complex G := by
  simpa only [Finset.image_id] using s.2.1
lemma bounded_const_face (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1.image (fun _ => (N,g)) ∈ complex G := by
  rw [Finset.image_const s.2.1.1]
  exact ⟨Finset.singleton_nonempty _,by simpa only [Finset.coe_singleton] using Set.injOn_singleton Prod.fst (N,g)⟩
lemma bounded_contiguous (N : ℕ) (g : G) (s : Face (bounded G N)) :
    s.1.image id ∪ s.1.image (fun _ => (N,g)) ∈ complex G := by
  rw [Finset.image_id,Finset.image_const s.2.1.1]
  exact bounded_union_apex N g s

lemma bounded_map_id (N : ℕ) (x : Simplicial.Space (bounded G N)) :
    Simplicial.map (bounded G N) (complex G) id (bounded_id_face N) x =
      Simplicial.inclusion (bounded G N) (complex G) (fun _ h => bounded_le G N h) x := by
  apply Subtype.ext
  exact Finsupp.mapDomain_id

lemma map_const_vertex (K : PreAbstractSimplicialComplex (ℕ × G)) (v : ℕ × G)
    (hf : ∀ s : Face K, s.1.image (fun _ => v) ∈ complex G) (x : Simplicial.Space K) :
    Simplicial.map K (complex G) (fun _ => v) hf x = vertex v := by
  apply Subtype.ext
  change x.1.mapDomain (fun _ => v) = Finsupp.single v 1
  rw [Finsupp.mapDomain,← Finsupp.single_sum]
  exact congrArg (Finsupp.single v) x.2.2.1

end UniversalFInfinity.Milnor

namespace UniversalFInfinity.Simplicial
open Set Metric Topology BigOperators
universe u
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

abbrev Cell (n : ℕ) := {s : Face K // s.1.card = n+1}

def cellOfFace (s : Face K) : Cell K (s.1.card-1) :=
  ⟨s,by have := Finset.card_pos.mpr (face_nonempty K s); omega⟩

def cellEquiv {n : ℕ} (s : Cell K n) : s.1.1 ≃ Fin (n+1) :=
  Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using s.2)

def faceDisk {n : ℕ} (s : Cell K n) : SimplexDisk.Simplex s.1.1 ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (SimplexDisk.reindex (cellEquiv K s)).trans (SimplexDisk.simplexDisk n)

lemma faceDisk_open {n : ℕ} (s : Cell K n) (x : SimplexDisk.Simplex s.1.1) :
    (faceDisk K s x).1 ∈ ball 0 1 ↔ (faceMap K s.1 x).1.support = s.1.1 := by
  rw [support_eq_iff]
  exact (SimplexDisk.simplexDisk_open n _).trans (SimplexDisk.reindex_positive _ _)

def diskMap {n : ℕ} (s : Cell K n) : C(closedBall (0 : Fin n → ℝ) 1, Space K) :=
  ⟨(faceMap K s.1) ∘ (faceDisk K s).symm,(continuous_faceMap K s.1).comp (faceDisk K s).symm.continuous⟩

lemma diskMap_injective {n : ℕ} (s : Cell K n) : Function.Injective (diskMap K s) :=
  (faceMap_injective K s.1).comp (faceDisk K s).symm.injective

lemma diskMap_range {n : ℕ} (s : Cell K n) : Set.range (diskMap K s) = Set.range (faceMap K s.1) :=
  (faceDisk K s).symm.surjective.range_comp (faceMap K s.1)

def characteristic {n : ℕ} (s : Cell K n) (x : Fin n → ℝ) : Space K := by
  classical
  exact if hx : x ∈ closedBall 0 1 then diskMap K s ⟨x,hx⟩ else diskMap K s ⟨0,by simp⟩

lemma characteristic_disk {n : ℕ} (s : Cell K n) (x : closedBall (0 : Fin n → ℝ) 1) :
    characteristic K s x.1 = diskMap K s x := by simp only [characteristic,dite_eq_left x.2]

lemma characteristic_bijOn {n : ℕ} (s : Cell K n) :
    Set.BijOn (characteristic K s) (ball 0 1) {x | x.1.support = s.1.1} := by
  constructor
  · intro x hx
    let d : closedBall (0 : Fin n → ℝ) 1 := ⟨x,ball_subset_closedBall hx⟩
    rw [show characteristic K s x = diskMap K s d from characteristic_disk K s d]
    exact (faceDisk_open K s ((faceDisk K s).symm d)).mp (by simpa using hx)
  constructor
  · intro x hx y hy hxy
    have hxy' : diskMap K s ⟨x,ball_subset_closedBall hx⟩ = diskMap K s ⟨y,ball_subset_closedBall hy⟩ := by
      simpa only [← characteristic_disk] using hxy
    exact congrArg Subtype.val (diskMap_injective K s hxy')
  · intro x hx
    let z := coordinates K s.1.1 x (by rw [hx])
    let d := faceDisk K s z
    have hd : d.1 ∈ ball 0 1 := (faceDisk_open K s z).mpr (by rwa [faceMap_coordinates])
    exact ⟨d.1,hd,(characteristic_disk K s d).trans (by
      change faceMap K s.1 ((faceDisk K s).symm (faceDisk K s z)) = x
      rw [Homeomorph.symm_apply_apply]
      exact faceMap_coordinates K s.1 x _)⟩

def characteristicPE {n : ℕ} (s : Cell K n) : PartialEquiv (Fin n → ℝ) (Space K) :=
  (characteristic_bijOn K s).toPartialEquiv _ _ _

lemma characteristicPE_open {n : ℕ} (s : Cell K n) :
    characteristicPE K s '' ball 0 1 = {x | x.1.support = s.1.1} :=
  (characteristic_bijOn K s).image_eq

lemma characteristicPE_closed {n : ℕ} (s : Cell K n) :
    characteristicPE K s '' closedBall 0 1 = Set.range (faceMap K s.1) := by
  rw [← diskMap_range]
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,(characteristic_disk K s ⟨z,hz⟩).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨z.1,z.2,characteristic_disk K s z⟩

lemma characteristicPE_continuous {n : ℕ} (s : Cell K n) :
    ContinuousOn (characteristicPE K s) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (closedBall (0:Fin n→ℝ) 1).domRestrict (characteristicPE K s) = diskMap K s := by
    funext x
    exact characteristic_disk K s x
  rw [he]
  exact (diskMap K s).continuous

lemma characteristicPE_continuous_symm {n : ℕ} (s : Cell K n) :
    ContinuousOn (characteristicPE K s).symm (characteristicPE K s).target := by
  let e := characteristicPE K s
  have he : IsEmbedding (e.source.domRestrict e) := by
    let inc : ball (0:Fin n→ℝ) 1 → closedBall (0:Fin n→ℝ) 1 := fun x => ⟨x.1,ball_subset_closedBall x.2⟩
    have hi : IsEmbedding inc := IsEmbedding.subtypeVal.codRestrict _ (fun x => ball_subset_closedBall x.2)
    have heq : e.source.domRestrict e = (diskMap K s) ∘ inc := by
      funext x
      exact characteristic_disk K s (inc x)
    rw [heq]
    exact ((diskMap K s).continuous.isClosedEmbedding (diskMap_injective K s)).isEmbedding.comp hi
  let H : e.source ≃ₜ e.target := e.toEquiv.toHomeomorphOfIsInducing
    (he.isInducing.codRestrict (fun x => e.map_source x.2))
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp H.symm.continuous

lemma support_lt_of_sphere {n : ℕ} (s : Cell K n) (x : Fin n → ℝ) (hx : x ∈ sphere 0 1) :
    (characteristicPE K s x).1.support.card < s.1.1.card := by
  have hd := characteristic_disk K s ⟨x,sphere_subset_closedBall hx⟩
  have hs : (characteristicPE K s x).1.support ⊆ s.1.1 := by
    rw [show characteristicPE K s x = diskMap K s ⟨x,sphere_subset_closedBall hx⟩ from hd]
    exact weight_support_subset _ _
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hs,?_⟩
  intro he
  have ho : x ∈ ball (0:Fin n→ℝ) 1 := by
    have hh := (faceDisk_open K s ((faceDisk K s).symm ⟨x,sphere_subset_closedBall hx⟩)).mpr (by
      change (characteristic K s x).1.support = s.1.1 at he
      rwa [hd] at he)
    simpa only [Homeomorph.apply_symm_apply] using hh
  exact sphere_disjoint_ball.notMem_of_mem_left hx ho

lemma subcells_finite (s : Face K) (n : ℕ) : Set.Finite {c : Cell K n | c.1.1 ⊆ s.1} := by
  classical
  have hinj : Function.Injective (fun c : Cell K n => c.1.1) := Subtype.val_injective.comp Subtype.val_injective
  have hfin := (s.1.powerset.finite_toSet).preimage hinj.injOn
  convert hfin using 1
  ext c
  simp only [mem_ofPred_eq,mem_preimage,Finset.mem_coe,Finset.mem_powerset]

noncomputable def subcells (s : Face K) (n : ℕ) : Finset (Cell K n) := (subcells_finite K s n).toFinset

lemma characteristic_boundary {n : ℕ} (s : Cell K n) :
    MapsTo (characteristicPE K s) (sphere 0 1)
      (⋃ (m < n) (j ∈ subcells K s.1 m), characteristicPE K j '' closedBall 0 1) := by
  intro x hx
  let y := characteristicPE K s x
  let t : Face K := ⟨y.1.support,y.2.2.2⟩
  let m := y.1.support.card-1
  let c : Cell K m := cellOfFace K t
  have hpos : 0 < y.1.support.card := Finset.card_pos.mpr (support_nonempty y.2.2.1)
  have hlt : y.1.support.card < s.1.1.card := support_lt_of_sphere K s x hx
  have hmn : m < n := by dsimp [m]; rw [s.2] at hlt; omega
  have hcs : c ∈ subcells K s.1 m := by
    rw [subcells,Set.Finite.mem_toFinset]
    change y.1.support ⊆ s.1.1
    rw [show y = diskMap K s ⟨x,sphere_subset_closedBall hx⟩ from characteristic_disk K s ⟨x,sphere_subset_closedBall hx⟩]
    exact weight_support_subset _ _
  refine mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hmn,mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hcs,?_⟩⟩⟩⟩
  rw [characteristicPE_closed,range_faceMap]
  exact Finset.Subset.refl _

instance cwComplex : Topology.CWComplex (Set.univ : Set (Space K)) where
  cell := Cell K
  map _ := characteristicPE K
  source_eq _ _ := rfl
  continuousOn _ := characteristicPE_continuous K
  continuousOn_symm _ := characteristicPE_continuous_symm K
  pairwiseDisjoint' := by
    intro a _ b _ hab
    change Disjoint (characteristicPE K a.2 '' ball 0 1) (characteristicPE K b.2 '' ball 0 1)
    rw [characteristicPE_open,characteristicPE_open]
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he : a.2.1.1 = b.2.1.1 := hx.symm.trans hy
    have hn : a.1 = b.1 := by have hc := congrArg Finset.card he; rw [a.2.2,b.2.2] at hc; omega
    apply hab
    rcases a with ⟨n,a⟩
    rcases b with ⟨m,b⟩
    dsimp at hn
    subst m
    exact congrArg (Sigma.mk n) (Subtype.ext (Subtype.ext he))
  mapsTo' _ s := ⟨subcells K s.1,characteristic_boundary K s⟩
  closed' A _ hA := by
    rw [isClosed_iff]
    intro s
    have hc := hA _ (cellOfFace K s)
    rw [characteristicPE_closed] at hc
    have hp := hc.preimage (continuous_faceMap K s)
    have he : (faceMap K s) ⁻¹' (A ∩ Set.range (faceMap K (cellOfFace K s).1)) = (faceMap K s) ⁻¹' A := by
      ext z; simp only [mem_preimage,mem_inter_iff]; exact and_iff_left (mem_range_self z)
    rwa [he] at hp
  union' := by
    apply Set.Subset.antisymm (subset_univ _)
    intro x _
    let s : Face K := ⟨x.1.support,x.2.2.2⟩
    refine mem_iUnion.mpr ⟨s.1.card-1,mem_iUnion.mpr ⟨cellOfFace K s,?_⟩⟩
    rw [characteristicPE_closed,range_faceMap]
    exact Finset.Subset.refl _
end UniversalFInfinity.Simplicial

end

end OAI
