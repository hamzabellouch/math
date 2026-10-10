import OAI.GroupTheory.UniversalGroup.ControlledCells

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

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor AscendingTorus Cellular
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

abbrev idx (n : ℕ) (c : Coset f) := (next f)^[n] c
lemma idx_next (n : ℕ) (c : Coset f) : idx f n (next f c) = next f (idx f n c) :=
  (Function.iterate_succ_apply _ _ _).symm.trans (Function.iterate_succ_apply' _ _ _)

lemma left_full_eq (S : Shapes U) (x : Milnor.Stage U S) :
    Milnor.stageFull U (vertexShapes f S) (left f S x) = Milnor.stageFull U S x := rfl

variable (S T : Shapes U) (n : ℕ)
variable (q : C(Milnor.Stage U (vertexShapes f S),Milnor.Stage U T)) (z : Milnor.Stage U T)
variable (H : q.Homotopy (.const _ z))
variable (hq : ∀ x,Milnor.stageFull U T (q x) =
  Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x))

def firstH (c : Coset f) : C(I × Milnor.Stage U (vertexShapes f S),Milnor.Stage U T) :=
  (stageSmul U T (forwardOffset f n c)).comp H.toContinuousMap
include hq in
lemma firstH_zero (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    Milnor.stageFull U T (firstH f S T n q z H c (0,x)) =
      GraphBundle.forward (next f) (transition f) n c (Milnor.stageFull U _ x) := by
  change Milnor.stageFull U T (forwardOffset f n c • H (0,x)) = _
  rw [H.apply_zero,Milnor.stageFull_smul,hq,forward_eq]
lemma firstH_one (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    firstH f S T n q z H c (1,x) = forwardOffset f n c • z := by
  change forwardOffset f n c • H (1,x) = _
  rw [H.apply_one]; rfl

def squareLeft (c : Coset f) : C(I × Milnor.Stage U S,Milnor.Stage U (vertexShapes f T)) :=
  (right f T (idx f n c)).comp ((firstH f S T n q z H c).comp
    (.prodMap (.id I) (left f S)))
def squareRight (c : Coset f) : C(I × Milnor.Stage U S,Milnor.Stage U (vertexShapes f T)) :=
  (left f T).comp ((firstH f S T n q z H (next f c)).comp
    (.prodMap (.id I) (right f S c)))
include hq in
lemma square_start (c : Coset f) (x : Milnor.Stage U S) :
    squareLeft f S T n q z H c (0,x) = squareRight f S T n q z H c (0,x) := by
  apply (Milnor.stageFull_embedding U _).injective
  change Milnor.stageFull U _ (right f T (idx f n c) (firstH f S T n q z H c (0,left f S x))) =
    Milnor.stageFull U _ (left f T (firstH f S T n q z H (next f c) (0,right f S c x)))
  rw [right_full,left_full_eq,firstH_zero _ _ _ _ _ _ _ hq,firstH_zero _ _ _ _ _ _ _ hq,left_full_eq,right_full]
  exact (GraphBundle.forward_natural _ _ n c _).symm
lemma squareLeft_one (c : Coset f) (x : Milnor.Stage U S) :
    squareLeft f S T n q z H c (1,x) = right f T (idx f n c) (forwardOffset f n c • z) := by
  exact congrArg (right f T (idx f n c)) (firstH_one f S T n q z H c (left f S x))
lemma squareRight_one (c : Coset f) (x : Milnor.Stage U S) :
    squareRight f S T n q z H c (1,x) = left f T (forwardOffset f n (next f c) • z) := by
  exact congrArg (left f T) (firstH_one f S T n q z H (next f c) (right f S c x))

variable (Z : Shapes U) (e : ℕ)
variable (r : C(Milnor.Stage U (vertexShapes f T),Milnor.Stage U Z)) (w : Milnor.Stage U Z)
variable (J : r.Homotopy (.const _ w))
variable (hr : ∀ x,Milnor.stageFull U Z (r x) =
  Milnor.map (iterateHom f e) id Function.injective_id (Milnor.stageFull U _ x))

def secondH (c : Coset f) : C(I × Milnor.Stage U (vertexShapes f S),Milnor.Stage U Z) :=
  (stageSmul U Z (forwardOffset f e (idx f n c))).comp
    (r.comp ((left f T).comp (firstH f S T n q z H c)))
include hr in
lemma secondH_full (c : Coset f) (t : I) (x : Milnor.Stage U (vertexShapes f S)) :
    Milnor.stageFull U Z (secondH f S T n q z H Z e r c (t,x)) =
      GraphBundle.forward (next f) (transition f) e (idx f n c)
        (Milnor.stageFull U T (firstH f S T n q z H c (t,x))) := by
  change Milnor.stageFull U Z (forwardOffset f e (idx f n c) • r (left f T (firstH f S T n q z H c (t,x)))) = _
  rw [Milnor.stageFull_smul,hr,left_full_eq,forward_eq]
lemma secondH_one (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    secondH f S T n q z H Z e r c (1,x) =
      forwardOffset f e (idx f n c) • r (left f T (forwardOffset f n c • z)) := by
  change forwardOffset f e (idx f n c) • r (left f T (firstH f S T n q z H c (1,x))) = _
  rw [firstH_one]
include hq hr in
lemma secondH_start_natural (c : Coset f) (x : Milnor.Stage U S) :
    right f Z (idx f e (idx f n c)) (secondH f S T n q z H Z e r c (0,left f S x)) =
      left f Z (secondH f S T n q z H Z e r (next f c) (0,right f S c x)) := by
  apply (Milnor.stageFull_embedding U _).injective
  rw [right_full,left_full_eq,secondH_full _ _ _ _ _ _ _ _ _ _ hr,secondH_full _ _ _ _ _ _ _ _ _ _ hr,
    firstH_zero _ _ _ _ _ _ _ hq,firstH_zero _ _ _ _ _ _ _ hq,left_full_eq,right_full]
  rw [idx_next,GraphBundle.forward_natural,GraphBundle.forward_natural]

include hq J in
lemma twoGhost_square (c : Coset f) :
    ∃ (P : Path (right f T (idx f n c) (forwardOffset f n c • z))
        (left f T (forwardOffset f n (next f c) • z)))
      (Q : C(Milnor.Stage U S,C(I,C(I,Milnor.Stage U Z)))),
      (∀ x t,Q x 0 t = r (squareLeft f S T n q z H c (0,x))) ∧
      (∀ x t,Q x 1 t = r (P t)) ∧
      (∀ x s,Q x s 0 = r (squareLeft f S T n q z H c (s,x))) ∧
      (∀ x s,Q x s 1 = r (squareRight f S T n q z H c (s,x))) := by
  exact connector_after_nullhomotopy (squareLeft f S T n q z H c) (squareRight f S T n q z H c)
    _ _ (square_start f S T n q z H hq c) (squareLeft_one f S T n q z H c)
    (squareRight_one f S T n q z H c) (Milnor.stagePoint U S) r w J

def finalIndex (n e : ℕ) (c : Coset f) := idx f e (idx f n c)
lemma finalIndex_next (n e : ℕ) (c : Coset f) : finalIndex f n e (next f c) = next f (finalIndex f n e c) := by
  simp only [finalIndex,idx_next]

def finalLower (c : Coset f) : C(Milnor.Stage U Z,Stage f Z) :=
  (GraphBundle.vertexMap (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c)).comp (left f Z)
def finalUpper (c : Coset f) : C(Milnor.Stage U Z,Stage f Z) :=
  (GraphBundle.vertexMap (next f) (fun _ => left f Z) (right f Z) (next f (finalIndex f n e c))).comp
    (right f Z (finalIndex f n e c))
def finalHigh (c : Coset f) : C(Milnor.Stage U Z,Stage f Z) :=
  (GraphBundle.vertexMap (next f) (fun _ => left f Z) (right f Z) (next f (finalIndex f n e c))).comp (left f Z)

include hr in
lemma final_natural (c : Coset f) (x : Milnor.Stage U T) :
    left f Z (forwardOffset f e (idx f n (next f c)) • r (right f T (idx f n c) x)) =
      right f Z (finalIndex f n e c) (forwardOffset f e (idx f n c) • r (left f T x)) := by
  apply (Milnor.stageFull_embedding U _).injective
  rw [left_full_eq,right_full,Milnor.stageFull_smul,Milnor.stageFull_smul,hr,hr,right_full,left_full_eq]
  rw [←forward_eq,←forward_eq,idx_next]
  exact GraphBundle.forward_natural _ _ e (idx f n c) _

def finalPoint (c : Coset f) : Milnor.Stage U Z :=
  forwardOffset f e (idx f n c) • r (left f T (forwardOffset f n c • z))

def shifted_stage (hq : ∀ x,Milnor.stageFull U T (q x) =
    Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x))
    (hr : ∀ x,Milnor.stageFull U Z (r x) =
    Milnor.map (iterateHom f e) id Function.injective_id (Milnor.stageFull U _ x)) : C(Stage f S,Stage f Z) :=
  GraphBundle.lift (next f) (fun _ => left f S) (right f S)
    (fun c => (finalLower f n Z e c).comp ((secondH f S T n q z H Z e r c).comp
      ⟨fun x => (0,x),continuous_const.prodMk continuous_id⟩))
    (fun c => (GraphBundle.edgeMap (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c)).comp
      ⟨fun p => (p.1,secondH f S T n q z H Z e r c (0,left f S p.2)),
        continuous_fst.prodMk ((secondH f S T n q z H Z e r c).continuous.comp
          (continuous_const.prodMk ((left f S).continuous.comp continuous_snd)))⟩)
    (fun c x => GraphBundle.edge_zero _ _ _ _ _)
    (fun c x => by
      change GraphBundle.edge (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c) 1
        (secondH f S T n q z H Z e r c (0,left f S x)) = _
      rw [GraphBundle.edge_one]
      change GraphBundle.vertex _ _ _ (next f (finalIndex f n e c))
        (right f Z (finalIndex f n e c) (secondH f S T n q z H Z e r c (0,left f S x))) =
        GraphBundle.vertex _ _ _ (finalIndex f n e (next f c))
        (left f Z (secondH f S T n q z H Z e r (next f c) (0,right f S c x)))
      rw [finalIndex_next]
      exact congrArg (GraphBundle.vertex _ _ _ _) (secondH_start_natural f S T n q z H hq Z e r hr c x))
lemma shifted_stage_vertex (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    shifted_stage f S T n q z H Z e r hq hr (GraphBundle.vertex _ _ _ c x) =
      finalLower f n Z e c (secondH f S T n q z H Z e r c (0,x)) := rfl
lemma shifted_stage_edge (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    shifted_stage f S T n q z H Z e r hq hr (GraphBundle.edge _ _ _ c t x) =
      GraphBundle.edge (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c) t
        (secondH f S T n q z H Z e r c (0,left f S x)) :=
  GraphBundle.lift_edge _ _ _ _ _ _ _ c (t,x)

include hq hr J in

theorem shifted_stage_nullhomotopic :
    (shifted_stage f S T n q z H Z e r hq hr).Nullhomotopic := by
  choose P Q hQ0 hQ1 hQL hQR using twoGhost_square f S T n q z H hq Z r w J
  let a := shifted_stage f S T n q z H Z e r hq hr
  let y (c : Coset f) := finalLower f n Z e c (finalPoint f T n z Z e r c)
  let V (c : Coset f) : (a.comp (GraphBundle.vertexMap (next f) (fun _ => left f S) (right f S) c)).Homotopy (.const _ (y c)) :=
    { toFun tx := finalLower f n Z e c (secondH f S T n q z H Z e r c tx)
      continuous_toFun := (finalLower f n Z e c).continuous.comp (secondH f S T n q z H Z e r c).continuous
      map_zero_left x := rfl
      map_one_left x := congrArg (finalLower f n Z e c) (secondH_one f S T n q z H Z e r c x) }
  let E (c : Coset f) (x : Milnor.Stage U Z) : Path (finalLower f n Z e c x) (finalUpper f n Z e c x) :=
    GraphBundle.edgePath (next f) (fun _ => left f Z) (right f Z) (finalIndex f n e c) x
  let K (c : Coset f) : C(I × Milnor.Stage U S,Milnor.Stage U Z) :=
    (secondH f S T n q z H Z e r c).comp (.prodMap (.id I) (left f S))
  let D (c : Coset f) : C(Milnor.Stage U S,C(I,C(I,Stage f Z))) :=
    ContinuousMap.curry (ContinuousMap.curry ((finalHigh f n Z e c).comp
      ((stageSmul U Z (forwardOffset f e (idx f n (next f c)))).comp ((Q c).uncurry.uncurry))))
  have he (c : Coset f) : Continuous (fun p : Milnor.Stage U Z × I => E c p.1 p.2) :=
    (GraphBundle.edgeMap (next f) (fun _ => left f Z) (right f Z) _).continuous.comp continuous_swap
  have hdleft (c : Coset f) (x : Milnor.Stage U S) (s : I) :
      D c x s 0 = finalUpper f n Z e c (K c (s,x)) := by
    change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x s 0) = _
    rw [hQL]
    exact congrArg (GraphBundle.vertex (next f) (fun _ => left f Z) (right f Z) (next f (finalIndex f n e c)))
      (final_natural f T n Z e r hr c (firstH f S T n q z H c (s,left f S x)))
  have hdright (c : Coset f) (x : Milnor.Stage U S) (s : I) :
      D c x s 1 = V (next f c) (s,right f S c x) := by
    change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x s 1) = _
    rw [hQR]
    change GraphBundle.vertex _ _ _ (next f (finalIndex f n e c)) _ =
      GraphBundle.vertex _ _ _ (finalIndex f n e (next f c)) _
    rw [finalIndex_next]
    rfl
  let p (c : Coset f) : Path (y c) (y (next f c)) :=
    (GraphBundle.gluedPath (next f) (fun _ => left f S) (right f S) a y V
      (finalLower f n Z e) (finalUpper f n Z e) E K D hdleft hdright c (1,Milnor.stagePoint U S)).cast
      (congrArg (finalLower f n Z e c) (secondH_one f S T n q z H Z e r c (left f S (Milnor.stagePoint U S))).symm)
      ((V (next f c)).apply_one (right f S c (Milnor.stagePoint U S))).symm
  apply GraphBundle.nullhomotopic_of_coherent_contraction (next f) (fun _ => left f S) (right f S)
    a y V (finalLower f n Z e) (finalUpper f n Z e) E he K D (fun _ _ _ => rfl) hdleft hdright
    (fun c x s => ?_) (fun c x s => ?_) p (fun c x s => ?_)
    (cosetHeight f) (height_next f) (common_descendant f) (QuotientGroup.mk (1 : Torus f))
  · exact (shifted_stage_edge f S T n q z H hq Z e r hr c s x).symm
  · change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x 0 s) = _
    rw [hQ0,square_start f S T n q z H hq c x]
    change GraphBundle.vertex _ _ _ (next f (finalIndex f n e c)) _ =
      GraphBundle.vertex _ _ _ (finalIndex f n e (next f c)) _
    rw [finalIndex_next]
    rfl
  · change ((E c (K c (1,x))).trans _ ) s =
      ((E c (K c (1,Milnor.stagePoint U S))).trans _) s
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs
    · change GraphBundle.edge _ _ _ _ _ (secondH f S T n q z H Z e r c (1,left f S x)) =
        GraphBundle.edge _ _ _ _ _ (secondH f S T n q z H Z e r c (1,left f S (Milnor.stagePoint U S)))
      rw [secondH_one,secondH_one]
    · change finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c x 1 _) =
        finalHigh f n Z e c (forwardOffset f e (idx f n (next f c)) • Q c (Milnor.stagePoint U S) 1 _)
      rw [hQ1,hQ1]
end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
variable (S T : Shapes U) (n : ℕ)
variable (q : C(Milnor.Stage U (vertexShapes f S),Milnor.Stage U T)) (z : Milnor.Stage U T)
variable (H : q.Homotopy (.const _ z))
variable (hq : ∀ x,Milnor.stageFull U T (q x) =
  Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x))
variable (Z : Shapes U) (e : ℕ)
variable (r : C(Milnor.Stage U (vertexShapes f T),Milnor.Stage U Z))
variable (hr : ∀ x,Milnor.stageFull U Z (r x) =
  Milnor.map (iterateHom f e) id Function.injective_id (Milnor.stageFull U _ x))
lemma shifted_stage_full :
    (stageFull f Z).comp (shifted_stage f S T n q z H Z e r hq hr) =
      (GraphBundle.shiftIterate (next f) (transition f) e).comp
        ((GraphBundle.shiftIterate (next f) (transition f) n).comp (stageFull f S)) := by
  apply GraphBundle.hom_ext
  · intro c x
    change stageFull f Z (shifted_stage f S T n q z H Z e r hq hr (GraphBundle.vertex _ _ _ c x)) = _
    rw [shifted_stage_vertex]
    change stageFull f Z (GraphBundle.vertex _ _ _ (finalIndex f n e c)
      (left f Z (secondH f S T n q z H Z e r c (0,x)))) = _
    rw [stageFull_vertex,left_full_eq,secondH_full _ _ _ _ _ _ _ _ _ _ hr,
      firstH_zero _ _ _ _ _ _ _ hq]
    change GraphBundle.vertex _ _ _ (finalIndex f n e c) _ =
      GraphBundle.shiftIterate (next f) (transition f) e
        (GraphBundle.shiftIterate (next f) (transition f) n
          (stageFull f S (GraphBundle.vertex _ _ _ c x)))
    rw [stageFull_vertex,vertex,GraphBundle.shiftIterate_vertex,GraphBundle.shiftIterate_vertex]
    rfl
  · intro c tx
    change stageFull f Z (shifted_stage f S T n q z H Z e r hq hr (GraphBundle.edge _ _ _ c tx.1 tx.2)) = _
    rw [shifted_stage_edge,stageFull_edge,secondH_full _ _ _ _ _ _ _ _ _ _ hr,
      firstH_zero _ _ _ _ _ _ _ hq,left_full_eq]
    change GraphBundle.edge _ _ _ (finalIndex f n e c) tx.1 _ =
      GraphBundle.shiftIterate (next f) (transition f) e
        (GraphBundle.shiftIterate (next f) (transition f) n
          (stageFull f S (GraphBundle.edge _ _ _ c tx.1 tx.2)))
    rw [stageFull_edge,GraphBundle.shiftIterate_edge,GraphBundle.shiftIterate_edge]
    rfl
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.PathFamilies
open Set Topology
open scoped unitInterval
variable {Y : Type*} [TopologicalSpace Y] {x y z : Y}
lemma diagonalSquare_mem (p : Path x y) (q : Path y z) (s t : I) {K : Set Y}
    (hp : Set.range p ⊆ K) (hq : Set.range q ⊆ K) : diagonalSquare p q (s,t) ∈ K := by
  apply (Set.union_subset hp hq)
  rw [←Path.trans_range,←Path.extend_range]
  exact Set.mem_range_self (((s:ℝ)+(t:ℝ))/2)
end UniversalFInfinity.PathFamilies

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

lemma vertexShapes_mono {S T : Shapes U} (h : S ⊆ T) : vertexShapes f S ⊆ vertexShapes f T := by
  apply Finset.union_subset_union h
  exact Finset.image_subset_image (Finset.insert_subset_insert _ h)
lemma stage_range_mono {S T : Shapes U} (h : S ⊆ T) :
    Set.range (stageFull f S) ⊆ Set.range (stageFull f T) := by
  rintro _ ⟨x,rfl⟩
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at x
  cases x with
  | inl x =>
    exact ⟨GraphBundle.vertex _ _ _ x.1 (stageIncl U _ _ (vertexShapes_mono f h) x.2),rfl⟩
  | inr x =>
    exact ⟨GraphBundle.interior _ _ _ x.1 x.2.1 (stageIncl U _ _ h x.2.2),rfl⟩

def stageInclusion (S T : Shapes U) (h : S ⊆ T) : C(Stage f S,Stage f T) :=
  factorStage f (stageFull f S) T (stage_range_mono f h)
lemma stageInclusion_full (S T : Shapes U) (h : S ⊆ T) (x : Stage f S) :
    stageFull f T (stageInclusion f S T h x) = stageFull f S x := factorStage_spec f _ _ _ x

lemma edge_mem_stage (S : Shapes U) (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) c t (Milnor.stageFull U S x) ∈
      Set.range (stageFull f S) := ⟨GraphBundle.edge _ _ _ c t x,stageFull_edge f S c t x⟩

lemma shiftHomotopy_controlled (S : Shapes U) (t : I) (x : Stage f S) :
    GraphBundle.shiftHomotopy (next f) (transition f) (t,stageFull f S x) ∈
      Set.range (stageFull f (vertexShapes f S)) := by
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at x
  cases x with
  | inl x => exact edge_mem_stage f _ x.1 t x.2
  | inr x =>
    change PathFamilies.diagonalSquare (GraphBundle.edgePath (next f) (fun _ => ContinuousMap.id _) (transition f) x.1 (Milnor.stageFull U S x.2.2))
      (GraphBundle.edgePath (next f) (fun _ => ContinuousMap.id _) (transition f) (next f x.1)
        (transition f x.1 (Milnor.stageFull U S x.2.2)))
      (t,⟨x.2.1.1,x.2.1.2.1.le,x.2.1.2.2.le⟩) ∈ _
    apply PathFamilies.diagonalSquare_mem
    · rintro y ⟨s,rfl⟩
      exact stage_range_mono f (vertexShapes_left f S) (edge_mem_stage f S x.1 s x.2.2)
    · rintro y ⟨s,rfl⟩
      exact edge_mem_stage f _ (next f x.1) s (right f S x.1 x.2.2)

lemma shiftIterateHomotopy_controlled (S : Shapes U) (n : ℕ) :
    ∃ T : Shapes U, ∀ (t : I) (x : Stage f S),
      GraphBundle.shiftIterateHomotopy (next f) (transition f) n (t,stageFull f S x) ∈
        Set.range (stageFull f T) := by
  induction n with
  | zero => exact ⟨S,fun _ x => ⟨x,rfl⟩⟩
  | succ n ih =>
    obtain ⟨T,hT⟩ := ih
    refine ⟨vertexShapes f T,?_⟩
    intro t x
    change ((GraphBundle.shiftIterateHomotopy (next f) (transition f) n).trans
      ((GraphBundle.shiftHomotopy (next f) (transition f)).compContinuousMap
        (GraphBundle.shiftIterate (next f) (transition f) n))) (t,stageFull f S x) ∈ _
    refine (congrArg (· ∈ Set.range (stageFull f (vertexShapes f T)))
      (ContinuousMap.Homotopy.trans_apply
        (GraphBundle.shiftIterateHomotopy (next f) (transition f) n)
        ((GraphBundle.shiftHomotopy (next f) (transition f)).compContinuousMap
          (GraphBundle.shiftIterate (next f) (transition f) n))
        (t,stageFull f S x))).mpr ?_
    split_ifs
    · exact stage_range_mono f (vertexShapes_left f T) (hT _ x)
    · have hx := hT 1 x
      rw [ContinuousMap.Homotopy.apply_one] at hx
      obtain ⟨y,hy⟩ := hx
      change GraphBundle.shiftHomotopy (next f) (transition f) (_,GraphBundle.shiftIterate (next f) (transition f) n (stageFull f S x)) ∈ _
      rw [←hy]
      exact shiftHomotopy_controlled f T _ y

variable {X : Type v} [TopologicalSpace X]
def homotopyFactor (S : Shapes U) (a b : C(X,Stage f S))
    (H : ((stageFull f S).comp a).Homotopy ((stageFull f S).comp b))
    (h : ∀ t x,H (t,x) ∈ Set.range (stageFull f S)) : a.Homotopy b where
  toContinuousMap := factorStage f H.toContinuousMap S (Set.range_subset_iff.mpr (fun x => h x.1 x.2))
  map_zero_left x := by
    apply (stageFull_closedEmbedding f S).injective
    exact (factorStage_spec f H.toContinuousMap S _ (0,x)).trans (H.apply_zero x)
  map_one_left x := by
    apply (stageFull_closedEmbedding f S).injective
    exact (factorStage_spec f H.toContinuousMap S _ (1,x)).trans (H.apply_one x)
end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

lemma doubleShiftHomotopy_controlled (S : Shapes U) (n e : ℕ) :
    ∃ R : Shapes U, ∀ (t : I) (x : Stage f S),
      ((GraphBundle.shiftIterateHomotopy (next f) (transition f) n).trans
        ((GraphBundle.shiftIterateHomotopy (next f) (transition f) e).compContinuousMap
          (GraphBundle.shiftIterate (next f) (transition f) n))) (t,stageFull f S x) ∈
        Set.range (stageFull f R) := by
  obtain ⟨A,hA⟩ := shiftIterateHomotopy_controlled f S n
  obtain ⟨B,hB⟩ := shiftIterateHomotopy_controlled f A e
  refine ⟨A ∪ B,?_⟩
  intro t x
  refine (congrArg (· ∈ Set.range (stageFull f (A ∪ B)))
    (ContinuousMap.Homotopy.trans_apply
      (GraphBundle.shiftIterateHomotopy (next f) (transition f) n)
      ((GraphBundle.shiftIterateHomotopy (next f) (transition f) e).compContinuousMap
        (GraphBundle.shiftIterate (next f) (transition f) n))
      (t,stageFull f S x))).mpr ?_
  split_ifs
  · exact stage_range_mono f Finset.subset_union_left (hA _ x)
  · have hx := hA 1 x
    rw [ContinuousMap.Homotopy.apply_one] at hx
    obtain ⟨y,hy⟩ := hx
    change GraphBundle.shiftIterateHomotopy (next f) (transition f) e
      (_,GraphBundle.shiftIterate (next f) (transition f) n (stageFull f S x)) ∈ _
    rw [←hy]
    exact stage_range_mono f Finset.subset_union_right (hB _ y)

theorem uniform_stage_nullhomotopy
    (hghost : ∀ S : Shapes U, ∃ (n : ℕ) (T : Shapes U)
      (q : C(Milnor.Stage U S,Milnor.Stage U T)) (z : Milnor.Stage U T),
      (∀ x,Milnor.stageFull U T (q x) =
        Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U S x)) ∧
      Nonempty (q.Homotopy (.const _ z))) (S : Shapes U) :
    ∃ (R : Shapes U) (hSR : S ⊆ R), (stageInclusion f S R hSR).Nullhomotopic := by
  obtain ⟨n,T,q,z,hq,⟨H⟩⟩ := hghost (vertexShapes f S)
  obtain ⟨e,Z,r,w,hr,⟨J⟩⟩ := hghost (vertexShapes f T)
  obtain ⟨B,hB⟩ := doubleShiftHomotopy_controlled f S n e
  let R := S ∪ Z ∪ B
  have hSR : S ⊆ R := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hZR : Z ⊆ R := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hBR : B ⊆ R := Finset.subset_union_right
  let a := stageInclusion f S R hSR
  let b := (stageInclusion f Z R hZR).comp (shifted_stage f S T n q z H Z e r hq hr)
  let K := ((GraphBundle.shiftIterateHomotopy (next f) (transition f) n).trans
    ((GraphBundle.shiftIterateHomotopy (next f) (transition f) e).compContinuousMap
      (GraphBundle.shiftIterate (next f) (transition f) n))).compContinuousMap (stageFull f S)
  have ha : (stageFull f S) = (stageFull f R).comp a := by
    apply ContinuousMap.ext; intro x
    exact (stageInclusion_full f S R hSR x).symm
  have hb : (GraphBundle.shiftIterate (next f) (transition f) e).comp
      ((GraphBundle.shiftIterate (next f) (transition f) n).comp (stageFull f S)) =
      (stageFull f R).comp b := by
    rw [←shifted_stage_full f S T n q z H hq Z e r hr]
    apply ContinuousMap.ext; intro x
    exact (stageInclusion_full f Z R hZR _).symm
  let K' : ((stageFull f R).comp a).Homotopy ((stageFull f R).comp b) := K.cast ha hb
  have hc (t : I) (x : Stage f S) : K' (t,x) ∈ Set.range (stageFull f R) :=
    stage_range_mono f hBR (hB t x)
  let L := homotopyFactor f R a b K' hc
  have hn := shifted_stage_nullhomotopic f S T n q z H hq Z e r w J hr
  obtain ⟨v,⟨M⟩⟩ := hn
  refine ⟨R,hSR,stageInclusion f Z R hZR v,⟨?_⟩⟩
  exact L.trans ((ContinuousMap.Homotopy.refl (stageInclusion f Z R hZR)).comp M)
end UniversalFInfinity.TorusGeometry

end

end OAI
