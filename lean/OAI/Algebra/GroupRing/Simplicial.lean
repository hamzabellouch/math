import Mathlib
import OAI.Algebra.GroupRing.SimplexTopology

namespace OAI

noncomputable section

open Set Metric Topology BigOperators

namespace GroupRingTopology.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical unitInterval
universe u v
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)

def mass : (V →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.lsum ℝ fun _ => LinearMap.id
lemma mass_apply (w : V →₀ ℝ) : mass w = w.sum (fun _ r => r) := rfl

lemma blend_support (x y : V →₀ ℝ) (t : I) :
    ((1-(t:ℝ)) • x + (t:ℝ) • y).support ⊆ x.support ∪ y.support :=
  Finsupp.support_add.trans (Finset.union_subset_union Finsupp.support_smul Finsupp.support_smul)

def blend (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) (t : I) : Space K := by
  let w := (1-(t:ℝ)) • x.1 + (t:ℝ) • y.1
  have hw : w.sum (fun _ r => r) = 1 := by
    rw [← mass_apply]
    simp only [w,map_add,map_smul,mass_apply,x.2.2.1,y.2.2.1,smul_eq_mul,mul_one]
    ring
  refine ⟨w,?_,hw,?_⟩
  · intro v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) (x.2.1 v)) (mul_nonneg t.2.1 (y.2.1 v))
  · exact K.isRelLowerSet_faces.mem_of_le s.2
      ((blend_support x.1 y.1 t).trans (Finset.union_subset hx hy)) (support_nonempty hw)

lemma blend_zero (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 0 = x := by
  apply Subtype.ext
  simp [blend]
lemma blend_one (s : Face K) (x y : Space K) (hx : x.1.support ⊆ s.1) (hy : y.1.support ⊆ s.1) :
    blend K s x y hx hy 1 = y := by
  apply Subtype.ext
  simp [blend]
lemma blend_self (s : Face K) (x : Space K) (hx : x.1.support ⊆ s.1) (t : I) :
    blend K s x x hx hx t = x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • x.1 + (t:ℝ) • x.1 = x.1
  rw [← add_smul,sub_add_cancel,one_smul]

variable (f g : V → W) (hf : ∀ s : Face K, s.1.image f ∈ L) (hg : ∀ s : Face K, s.1.image g ∈ L)
variable (hfg : ∀ s : Face K, s.1.image f ∪ s.1.image g ∈ L)

def straight (t : I) (x : Space K) : Space L :=
  blend L ⟨x.1.support.image f ∪ x.1.support.image g,hfg ⟨x.1.support,x.2.2.2⟩⟩
    (map K L f hf x) (map K L g hg x)
    ((map_support K L f hf x).trans Finset.subset_union_left)
    ((map_support K L g hg x).trans Finset.subset_union_right) t

lemma continuous_straight : Continuous (fun p : I × Space K => straight K L f g hf hg hfg p.1 p.2) := by
  rw [continuous_prod_iff]
  intro s
  apply continuous_of_support_subset L _ ⟨s.1.image f ∪ s.1.image g,hfg s⟩
  · intro p
    exact (blend_support _ _ p.1).trans (Finset.union_subset_union
      ((map_support K L f hf _).trans (Finset.image_subset_image (weight_support_subset _ _)))
      ((map_support K L g hg _).trans (Finset.image_subset_image (weight_support_subset _ _))))
  · intro b
    change Continuous (fun p : I × simplexSet ℝ s.1 =>
      (1-(p.1:ℝ)) * (map K L f hf (faceMap K s p.2)).1 b +
        (p.1:ℝ) * (map K L g hg (faceMap K s p.2)).1 b)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_eval L b).comp ((continuous_map K L f hf).comp ((continuous_faceMap K s).comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_eval L b).comp ((continuous_map K L g hg).comp ((continuous_faceMap K s).comp continuous_snd))))

def straightHomotopy : (mapC K L f hf).Homotopy (mapC K L g hg) where
  toFun p := straight K L f g hf hg hfg p.1 p.2
  continuous_toFun := continuous_straight K L f g hf hg hfg
  map_zero_left _ := blend_zero L _ _ _ _ _
  map_one_left _ := blend_one L _ _ _ _ _

lemma straightHomotopy_fixed (x : Space K) (h : map K L f hf x = map K L g hg x) (t : I) :
    straightHomotopy K L f g hf hg hfg (t,x) = map K L f hf x := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (map K L f hf x).1 + (t:ℝ) • (map K L g hg x).1 = (map K L f hf x).1
  rw [←h,←add_smul,sub_add_cancel,one_smul]
end
open Set Metric Topology BigOperators
open scoped Classical
universe u
variable {V : Type u} (K L : PreAbstractSimplicialComplex V) (hKL : ∀ s ∈ K, s ∈ L)

def inclusion (x : Space K) : Space L := ⟨x.1,x.2.1,x.2.2.1,hKL _ x.2.2.2⟩

lemma inclusion_injective : Function.Injective (inclusion K L hKL) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : Space L => z.1) h)

lemma inclusion_faceMap (s : Face K) (x : simplexSet ℝ s.1) :
    inclusion K L hKL (faceMap K s x) = faceMap L ⟨s.1,hKL _ s.2⟩ x := rfl

lemma continuous_inclusion : Continuous (inclusion K L hKL) := by
  rw [continuous_iff]
  intro s
  exact continuous_faceMap L ⟨s.1,hKL _ s.2⟩

lemma inclusion_isClosedMap : IsClosedMap (inclusion K L hKL) := by
  intro A hA
  rw [isClosed_iff]
  intro s
  let T : Set (Face K) := {t | t.1 ⊆ s.1}
  have hT : T.Finite := by
    have hf := s.1.powerset.finite_toSet.preimage (Subtype.val_injective : Function.Injective (Subtype.val : Face K → Finset V)).injOn
    convert hf using 1
    ext t
    simp only [T,mem_ofPred_eq,mem_preimage,Finset.mem_coe,Finset.mem_powerset]
  have hc : IsClosed (⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t))) := by
    apply hT.isClosed_biUnion
    intro t _
    exact (((isCompact_range (continuous_faceMap K t)).inter_left hA).image
      (continuous_inclusion K L hKL)).isClosed
  have he : inclusion K L hKL '' A ∩ Set.range (faceMap L s) =
      ⋃ t ∈ T, inclusion K L hKL '' (A ∩ Set.range (faceMap K t)) := by
    ext x
    simp only [mem_inter_iff,mem_image,mem_iUnion]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hs⟩
      rw [range_faceMap] at hs
      let t : Face K := ⟨y.1.support,y.2.2.2⟩
      refine ⟨t,hs,y,⟨hy,?_⟩,rfl⟩
      rw [range_faceMap]
      exact Finset.Subset.refl _
    · rintro ⟨t,ht,y,⟨hy,hyt⟩,rfl⟩
      refine ⟨⟨y,hy,rfl⟩,?_⟩
      rw [range_faceMap] at hyt ⊢
      exact hyt.trans (show t.1 ⊆ s.1 from ht)
  rw [←he] at hc
  have hp := hc.preimage (continuous_faceMap L s)
  simpa only [preimage_inter,preimage_range,inter_univ] using hp

lemma inclusion_closedEmbedding : IsClosedEmbedding (inclusion K L hKL) :=
  .of_continuous_injective_isClosedMap (continuous_inclusion K L hKL)
    (inclusion_injective K L hKL) (inclusion_isClosedMap K L hKL)
end GroupRingTopology.Simplicial
namespace GroupRingTopology.Milnor
open Set Metric Topology BigOperators GroupRingTopology.Simplicial
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

end GroupRingTopology.Milnor

namespace GroupRingTopology.Simplicial
open Set Metric Topology BigOperators
universe u
variable {V : Type u} (K : PreAbstractSimplicialComplex V)

abbrev Cell (n : ℕ) := {s : Face K // s.1.card = n+1}

def cellOfFace (s : Face K) : Cell K (s.1.card-1) :=
  ⟨s,by have := Finset.card_pos.mpr (face_nonempty K s); omega⟩

def cellEquiv {n : ℕ} (s : Cell K n) : s.1.1 ≃ Fin (n+1) :=
  Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using s.2)

def faceDisk {n : ℕ} (s : Cell K n) : simplexSet ℝ s.1.1 ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  (SimplexDisk.reindex (cellEquiv K s)).trans (SimplexDisk.simplexDisk n)

lemma faceDisk_open {n : ℕ} (s : Cell K n) (x : simplexSet ℝ s.1.1) :
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
end GroupRingTopology.Simplicial
open Set Metric Topology

end

end OAI
