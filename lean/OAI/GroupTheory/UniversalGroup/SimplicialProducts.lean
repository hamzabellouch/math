import OAI.GroupTheory.UniversalGroup.MilnorProducts

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical
universe u v w
variable {G : Type u} {H : Type v} {J : Type w}
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def pairVertex (β : G → H → J) (v : (ℕ × G) × (ℕ × H)) : ℕ × J :=
  (Nat.pair v.1.1 v.2.1,β v.1.2 v.2.2)

def pairFace (β : G → H → J) (s : Finset (ℕ × G)) (t : Finset (ℕ × H)) : Finset (ℕ × J) :=
  (s ×ˢ t).image (pairVertex β)

lemma pairFace_valid (β : G → H → J) {s : Finset (ℕ × G)} {t : Finset (ℕ × H)}
    (hs : s ∈ complex G) (ht : t ∈ complex H) : pairFace β s t ∈ complex J := by
  refine ⟨(hs.1.product ht.1).image _,?_⟩
  intro a ha b hb hab
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨⟨x',y'⟩,hxy',rfl⟩ := Finset.mem_image.mp hb
  have hh := Nat.pair_eq_pair.mp hab
  have hx : x = x' := hs.2 (Finset.mem_product.mp hxy).1 (Finset.mem_product.mp hxy').1 hh.1
  have hy : y = y' := ht.2 (Finset.mem_product.mp hxy).2 (Finset.mem_product.mp hxy').2 hh.2
  subst x'; subst y'; rfl

lemma pairFace_mono (β : G → H → J) {s s' : Finset (ℕ × G)} {t t' : Finset (ℕ × H)}
    (hs : s ⊆ s') (ht : t ⊆ t') : pairFace β s t ⊆ pairFace β s' t' :=
  Finset.image_subset_image (Finset.product_subset_product hs ht)

variable [Group G] [Group H] [Group J]
variable (φ : G →* J) (ψ : H →* J) (hc : ∀ g h, Commute (φ g) (ψ h))

include hc in
lemma pair_translate_vertex (a g : G) (b h : H) :
    φ (a*g)*ψ (b*h) = (φ a*ψ b)*(φ g*ψ h) := by
  rw [φ.map_mul,ψ.map_mul]
  calc
    (φ a*φ g)*(ψ b*ψ h) = φ a*(φ g*ψ b)*ψ h := by simp only [mul_assoc]
    _ = φ a*(ψ b*φ g)*ψ h := by
      have hh := hc g b
      change φ g * ψ b = ψ b * φ g at hh
      rw [hh]
    _ = (φ a*ψ b)*(φ g*ψ h) := by simp only [mul_assoc]

include hc in
lemma pairFace_translate (a : G) (b : H) (s : Finset (ℕ × G)) (t : Finset (ℕ × H)) :
    pairFace (fun g h => φ g*ψ h) (translate a s) (translate b t) =
      translate (φ a*ψ b) (pairFace (fun g h => φ g*ψ h) s t) := by
  ext z
  simp only [pairFace,translate,Finset.mem_image,Finset.mem_product]
  constructor
  · rintro ⟨⟨x,y⟩,⟨⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩,rfl⟩
    refine ⟨pairVertex (fun g h => φ g*ψ h) (v,w),⟨⟨v,w⟩,⟨hv,hw⟩,rfl⟩,?_⟩
    apply Prod.ext
    · rfl
    · exact (pair_translate_vertex φ ψ hc a v.2 b w.2).symm
  · rintro ⟨z,⟨⟨v,w⟩,⟨hv,hw⟩,rfl⟩,rfl⟩
    refine ⟨⟨(v.1,a*v.2),(w.1,b*w.2)⟩,⟨⟨v,hv,rfl⟩,⟨w,hw,rfl⟩⟩,?_⟩
    apply Prod.ext
    · rfl
    · exact pair_translate_vertex φ ψ hc a v.2 b w.2

def productShapes (S : Finset (Finset (ℕ × G))) (T : Finset (Finset (ℕ × H))) :
    Finset (Finset (ℕ × J)) := (S ×ˢ T).image (fun p => pairFace (fun g h => φ g*ψ h) p.1 p.2)

include hc in
lemma pairFace_controlled (S : Finset (Finset (ℕ × G))) (T : Finset (Finset (ℕ × H)))
    (s : Face (orbitSpan S)) (t : Face (orbitSpan T)) :
    pairFace (fun g h => φ g*ψ h) s.1 t.1 ∈ orbitSpan (productShapes φ ψ S T) := by
  obtain ⟨a,s',hs',hss⟩ := s.2.2
  obtain ⟨b,t',ht',htt⟩ := t.2.2
  refine ⟨pairFace_valid _ s.2.1 t.2.1,φ a*ψ b,pairFace (fun g h => φ g*ψ h) s' t',?_,?_⟩
  · exact Finset.mem_image.mpr ⟨(s',t'),Finset.mem_product.mpr ⟨hs',ht'⟩,rfl⟩
  · rw [←pairFace_translate φ ψ hc]
    exact pairFace_mono _ hss htt

end UniversalFInfinity.Milnor

namespace UniversalFInfinity.HomotopyFunctor
open scoped Topology.Homotopy
lemma map_congr_maps {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f g : C(X,Y)) (hf : f x = y) (hg : g x = y) (h : f = g) (a : HomotopyGroup N X x) :
    map f hf a = map g hg a := by
  subst g
  rfl
end UniversalFInfinity.HomotopyFunctor

namespace UniversalFInfinity.Simplicial

section
open Set Metric Topology BigOperators
open scoped Classical Topology.Homotopy
universe u v w
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)
variable (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1)

include hx in
lemma anchorFace : ({v} : Finset V) ∈ K := by
  have hh := x.2.2.2
  rwa [hx,Finsupp.support_single _ one_ne_zero] at hh

include hx hp in
lemma leftAxisFace (s : Face K) : s.1.image (fun a => p (a,v)) ∈ L := by
  have hh := hp s ⟨{v},anchorFace K x v hx⟩
  simpa only [Finset.product_singleton,Finset.map_eq_image,Finset.image_image,
    Function.comp_def,Function.Embedding.sectL_apply] using hh
include hx hp in
lemma rightAxisFace (s : Face K) : s.1.image (fun a => p (v,a)) ∈ L := by
  have hh := hp ⟨{v},anchorFace K x v hx⟩ s
  simpa only [Finset.singleton_product,Finset.map_eq_image,Finset.image_image,
    Function.comp_def,Function.Embedding.sectR_apply] using hh

def leftAxis : C(Space K,Space L) := mapC K L (fun a => p (a,v)) (leftAxisFace K L p hp x v hx)
def rightAxis : C(Space K,Space L) := mapC K L (fun a => p (v,a)) (rightAxisFace K L p hp x v hx)

lemma leftAxis_point : leftAxis K L p hp x v hx x = vertexDiagonal K L p hp x := by
  apply Subtype.ext
  change x.1.mapDomain _ = x.1.mapDomain _
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]
lemma rightAxis_point : rightAxis K L p hp x v hx x = vertexDiagonal K L p hp x := by
  apply Subtype.ext
  change x.1.mapDomain _ = x.1.mapDomain _
  rw [hx,Finsupp.mapDomain_single,Finsupp.mapDomain_single]

variable [Finite (Face K)]
lemma pairLeft_eq : (pairMapC K K L p hp).comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ x)) =
    leftAxis K L p hp x v hx := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change (tensor z.1 x.1).mapDomain p = z.1.mapDomain _
  rw [hx,tensor_single_right_push]
lemma pairRight_eq : (pairMapC K K L p hp).comp ((ContinuousMap.const _ x).prodMk (ContinuousMap.id _)) =
    rightAxis K L p hp x v hx := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change (tensor x.1 z.1).mapDomain p = z.1.mapDomain _
  rw [hx,tensor_single_left_push]

include hx in
lemma productDiagonal_point : productDiagonal K L p hp x = vertexDiagonal K L p hp x := by
  apply Subtype.ext
  rw [show (productDiagonal K L p hp x).1 = Finsupp.single (p (v,v)) 1 from pairMap_pure K L p hp x x v v hx hx]
  change Finsupp.single _ 1 = x.1.mapDomain _
  rw [hx,Finsupp.mapDomain_single]

variable {N : Type w} [DecidableEq N] [Nonempty N]
lemma finite_pair_additivity (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) rfl a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) (leftAxis_point K L p hp x v hx) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) (rightAxis_point K L p hp x v hx) a := by
  have hh := HomotopyFunctor.product_additivity (pairMapC K K L p hp)
    (productDiagonal_point K L p hp x v hx) a
  have hD := HomotopyFunctor.map_eq_of_homotopy (productDiagonal K L p hp) (vertexDiagonal K L p hp)
    (productDiagonal_point K L p hp x v hx) rfl (diagonalHomotopy K L p hp)
    (diagonalHomotopy_fixed K L p hp x v hx) a
  simp only [ContinuousMap.id_apply] at hh
  have hL := HomotopyFunctor.map_congr_maps ((pairMapC K K L p hp).comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ x))) _ (productDiagonal_point K L p hp x v hx) (leftAxis_point K L p hp x v hx)
    (pairLeft_eq K L p hp x v hx) a
  have hR := HomotopyFunctor.map_congr_maps ((pairMapC K K L p hp).comp ((ContinuousMap.const _ x).prodMk (ContinuousMap.id _))) _ (productDiagonal_point K L p hp x v hx) (rightAxis_point K L p hp x v hx)
    (pairRight_eq K L p hp x v hx) a
  exact hD.symm.trans (hh.trans (congrArg₂ (· * ·) hL hR))
end

section
open Set Metric Topology BigOperators
open scoped Classical Topology.Homotopy
universe u v w
variable {V : Type u} {W : Type v}
variable (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
variable (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)
variable (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1)
variable {N : Type w} [DecidableEq N] [Nonempty N]
lemma finite_pair_additivity_to [Finite (Face K)] (z : Space L)
    (hz : vertexDiagonal K L p hp x = z) (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) hz a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) ((leftAxis_point K L p hp x v hx).trans hz) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) ((rightAxis_point K L p hp x v hx).trans hz) a := by
  subst z
  exact finite_pair_additivity K L p hp x v hx a

lemma pair_additivity (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) rfl a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) (leftAxis_point K L p hp x v hx) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) (rightAxis_point K L p hp x v hx) a := by
  induction a using Quotient.inductionOn with | h q =>
  obtain ⟨R,y,hy,r,hr⟩ := loop_finite_restriction K q
  have hyr : y.1 = Finsupp.single v 1 := (congrArg (fun z : Space K => z.1) hy).trans hx
  let hpR : ∀ s t : Face (restrict K R), (s.1 ×ˢ t.1).image p ∈ L :=
    fun s t => hp ⟨s.1,s.2.1⟩ ⟨t.1,t.2.1⟩
  have hz : vertexDiagonal (restrict K R) L p hpR y = vertexDiagonal K L p hp x := by
    apply Subtype.ext
    exact congrArg (Finsupp.mapDomain (fun v => p (v,v))) (congrArg (fun z : Space K => z.1) hy)
  have hh := finite_pair_additivity_to (restrict K R) L p hpR y v hyr _ hz (Quotient.mk' r)
  subst q
  exact hh
end

open scoped Classical Topology.Homotopy
universe u v w
variable {V : Type u} {W : Type v}
lemma pair_additivity_to (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (p : V × V → W) (hp : ∀ s t : Face K, (s.1 ×ˢ t.1).image p ∈ L)
    (x : Space K) (v : V) (hx : x.1 = Finsupp.single v 1) {N : Type w} [DecidableEq N] [Nonempty N]
    (z : Space L) (hz : vertexDiagonal K L p hp x = z) (a : HomotopyGroup N (Space K) x) :
    HomotopyFunctor.map (vertexDiagonal K L p hp) hz a =
      HomotopyFunctor.map (leftAxis K L p hp x v hx) ((leftAxis_point K L p hp x v hx).trans hz) a *
      HomotopyFunctor.map (rightAxis K L p hp x v hx) ((rightAxis_point K L p hp x v hx).trans hz) a := by
  subst z
  exact pair_additivity K L p hp x v hx a
end UniversalFInfinity.Simplicial

namespace UniversalFInfinity.Milnor
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical Topology.Homotopy
universe u v w
variable {G : Type u} {H : Type v} [Group G] [Group H]
variable (N : Type w) [DecidableEq N] [Nontrivial N]
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

variable (φ ψ : G →* H) (hc : ∀ g h, Commute (φ g) (ψ h)) (S : Shapes G)
def commutingProduct : G →* H where
  toFun g := φ g*ψ g
  map_one' := by rw [φ.map_one,ψ.map_one,one_mul]
  map_mul' a b := pair_translate_vertex φ ψ hc a b a b

def addTarget : Shapes H := productShapes φ ψ (basedShapes G S) (basedShapes G S)
def addVertex := pairVertex (fun g h => φ g*ψ h)
include hc in
lemma addValid (s t : Face (stage G S)) : (s.1 ×ˢ t.1).image (addVertex φ ψ) ∈ stage H (addTarget φ ψ S) :=
  orbitSpan_mono (Finset.subset_insert _ _) (pairFace_controlled φ ψ hc _ _ s t)

def diagLayer (i : ℕ) := Nat.pair i i
def leftLayer (i : ℕ) := Nat.pair i 0
def rightLayer (i : ℕ) := Nat.pair 0 i
lemma diagLayer_injective : Function.Injective diagLayer := fun _ _ h => (Nat.pair_eq_pair.mp h).1
lemma leftLayer_injective : Function.Injective leftLayer := fun _ _ h => (Nat.pair_eq_pair.mp h).1
lemma rightLayer_injective : Function.Injective rightLayer := fun _ _ h => (Nat.pair_eq_pair.mp h).2

lemma addDiagValid (s : Face (stage G S)) :
    faceImage (commutingProduct φ ψ hc) diagLayer s.1 ∈ stage H (addTarget φ ψ S) :=
  diagonal_face _ _ (addVertex φ ψ) (addValid φ ψ hc S) s
include hc in
lemma addLeftValid (s : Face (stage G S)) :
    faceImage φ leftLayer s.1 ∈ stage H (addTarget φ ψ S) := by
  have hh := leftAxisFace _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl s
  change (s.1.image (fun a => (Nat.pair a.1 0,φ a.2))) ∈ stage H (addTarget φ ψ S)
  simpa only [addVertex,pairVertex,map_one,mul_one] using hh
include hc in
lemma addRightValid (s : Face (stage G S)) :
    faceImage ψ rightLayer s.1 ∈ stage H (addTarget φ ψ S) := by
  have hh := rightAxisFace _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl s
  change (s.1.image (fun a => (Nat.pair 0 a.1,ψ a.2))) ∈ stage H (addTarget φ ψ S)
  simpa only [addVertex,pairVertex,map_one,one_mul] using hh

lemma addLeftMap : leftAxis _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl =
    stageMap φ leftLayer S _ (addLeftValid φ ψ hc S) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change z.1.mapDomain _ = z.1.mapDomain _
  congr 1
  funext v
  exact Prod.ext rfl (by exact (congrArg (φ v.2 * ·) ψ.map_one).trans (mul_one _))
lemma addRightMap : rightAxis _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl =
    stageMap ψ rightLayer S _ (addRightValid φ ψ hc S) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  change z.1.mapDomain _ = z.1.mapDomain _
  congr 1
  funext v
  exact Prod.ext rfl (by exact (congrArg (· * ψ v.2) φ.map_one).trans (one_mul _))

lemma addHom : stageMapHom N (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl =
    stageMapHom N φ leftLayer S _ (addLeftValid φ ψ hc S) rfl *
      stageMapHom N ψ rightLayer S _ (addRightValid φ ψ hc S) rfl := by
  ext a
  have hh := pair_additivity_to (stage G S) (stage H (addTarget φ ψ S)) (addVertex φ ψ) (addValid φ ψ hc S)
    (stagePoint G S) (0,1) rfl (stagePoint H (addTarget φ ψ S))
    (stageMap_point (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl) a
  have hL := HomotopyFunctor.map_congr_maps _ _
    ((leftAxis_point _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl).trans (stageMap_point (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl))
    (stageMap_point φ leftLayer S _ (addLeftValid φ ψ hc S) rfl) (addLeftMap φ ψ hc S) a
  have hR := HomotopyFunctor.map_congr_maps _ _
    ((rightAxis_point _ _ (addVertex φ ψ) (addValid φ ψ hc S) (stagePoint G S) (0,1) rfl).trans (stageMap_point (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl))
    (stageMap_point ψ rightLayer S _ (addRightValid φ ψ hc S) rfl) (addRightMap φ ψ hc S) a
  exact hh.trans (congrArg₂ (· * ·) hL hR)

theorem mapValue_product :
    mapValue N (commutingProduct φ ψ hc) id S rfl Function.injective_id =
      mapValue N φ id S rfl Function.injective_id * mapValue N ψ id S rfl Function.injective_id := by
  rw [mapValue_relayer N (commutingProduct φ ψ hc) S id diagLayer Function.injective_id diagLayer_injective rfl rfl,
    mapValue_relayer N φ S id leftLayer Function.injective_id leftLayer_injective rfl rfl,
    mapValue_relayer N ψ S id rightLayer Function.injective_id rightLayer_injective rfl rfl,
    mapValue_eq N (commutingProduct φ ψ hc) diagLayer S _ (addDiagValid φ ψ hc S) rfl diagLayer_injective,
    mapValue_eq N φ leftLayer S _ (addLeftValid φ ψ hc S) rfl leftLayer_injective,
    mapValue_eq N ψ rightLayer S _ (addRightValid φ ψ hc S) rfl rightLayer_injective]
  change value H N _ _ _ = value H N _ _ _ * value H N _ _ _
  rw [←value_mul,addHom N φ ψ hc S]
end UniversalFInfinity.Milnor

end

end OAI
