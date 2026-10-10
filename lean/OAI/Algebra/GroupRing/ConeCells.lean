import Mathlib
import OAI.Algebra.GroupRing.GeneralPosition

namespace OAI



section
namespace TorsionFreeZeroDivisors.GraphConeCW
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open GroupRingTopology.Cellular hiding Disk Sphere boundary
open scoped unitInterval Classical
noncomputable section
lemma cons_tail_time {n : ℕ} (d : Disk (n+1)) : diskCons (diskTail d) (diskTime d)=d := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [diskCons,diskTime,Fin.cons_zero]
    ring
  · rfl
lemma cylinder_side {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (a : C(Sphere n,C(I,Y))) (b : C(Disk n,Y×Y))
    (h : ∀x,pathEndpoint (a x)=b (boundary n x)) (x : Sphere n) (t : I) :
    cylinderBoundaryMap a b h ⟨_,cons_mem_sphere_of_boundary x t⟩=a x t := by
  let z : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
  have hz : z∈cylinderFace n none := by
    change (diskTail (diskCons (boundary n x) t)).1∈sphere 0 1
    rw [diskTail_cons]
    exact x.2
  rw [cylinderBoundaryMap_face a b h none ⟨z,hz⟩]
  change a (faceSphere ⟨z,hz⟩) (diskTime (diskCons (boundary n x) t))=a x t
  rw [diskTime_cons]
  congr 1
lemma cylinder_bottom {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (a : C(Sphere n,C(I,Y))) (b : C(Disk n,Y×Y))
    (h : ∀x,pathEndpoint (a x)=b (boundary n x)) (d : Disk n) :
    cylinderBoundaryMap a b h ⟨_,cons_zero_mem_sphere d⟩=(b d).1 := by
  let z : Sphere (n+1) := ⟨_,cons_zero_mem_sphere d⟩
  have hz : z∈cylinderFace n (some false) := by norm_num [z,cylinderFace,diskCons]
  rw [cylinderBoundaryMap_face a b h (some false) ⟨z,hz⟩]
  change (b (diskTail (diskCons d 0))).1=_
  rw [diskTail_cons]
lemma cylinder_top {Y : Type*} [TopologicalSpace Y] {n : ℕ}
    (a : C(Sphere n,C(I,Y))) (b : C(Disk n,Y×Y))
    (h : ∀x,pathEndpoint (a x)=b (boundary n x)) (d : Disk n) :
    cylinderBoundaryMap a b h ⟨_,cons_one_mem_sphere d⟩=(b d).2 := by
  let z : Sphere (n+1) := ⟨_,cons_one_mem_sphere d⟩
  have hz : z∈cylinderFace n (some true) := by norm_num [z,cylinderFace,diskCons]
  rw [cylinderBoundaryMap_face a b h (some true) ⟨z,hz⟩]
  change (b (diskTail (diskCons d 1))).2=_
  rw [diskTail_cons]
variable {V E : Type*} (src dst : E→V)
local instance : TopologicalSpace (Option V) := ⊥
local instance : DiscreteTopology (Option V) := ⟨rfl⟩
def endpoint : V⊕E → Bool → Option V
  | .inl v,false => some v
  | .inl _,true => none
  | .inr e,false => some (src e)
  | .inr e,true => some (dst e)
def oneBoundary (i : V⊕E) : C(Sphere 1,Option V) :=
  ⟨fun x=>endpoint src dst i (if x=Cayley.minus then false else true),continuous_of_discreteTopology⟩
abbrev One := Space (oneBoundary src dst)
def vertex (v : Option V) : One src dst := base _ v
lemma minus_ne_plus : Cayley.minus≠Cayley.plus := by
  intro he
  have := congrArg (fun x : Sphere 1=>x.1 0) he
  norm_num [Cayley.minus,Cayley.plus] at this
@[simp] lemma oneBoundary_minus (i : V⊕E) : oneBoundary src dst i Cayley.minus=endpoint src dst i false := by
  simp [oneBoundary]
@[simp] lemma oneBoundary_plus (i : V⊕E) : oneBoundary src dst i Cayley.plus=endpoint src dst i true := by
  simp [oneBoundary,Ne.symm minus_ne_plus]
def radial (v : V) : C(I,One src dst) := (cell _ (.inl v)).comp ⟨Cayley.edgeParam,Cayley.continuous_edgeParam⟩
def outer (e : E) : C(Disk 1,One src dst) := cell _ (.inr e)
@[simp] lemma radial_zero (v : V) : radial src dst v 0=vertex src dst (some v) := by
  change cell _ _ (Cayley.edgeParam 0)=_
  rw [Cayley.edgeParam_zero,cell_boundary,oneBoundary_minus]
  rfl
@[simp] lemma radial_one (v : V) : radial src dst v 1=vertex src dst none := by
  change cell _ _ (Cayley.edgeParam 1)=_
  rw [Cayley.edgeParam_one,cell_boundary,oneBoundary_plus]
  rfl
@[simp] lemma outer_minus (e : E) : outer src dst e (boundary 1 Cayley.minus)=vertex src dst (some (src e)) := by
  change cell _ _ (boundary 1 Cayley.minus)=_
  rw [cell_boundary,oneBoundary_minus]
  rfl
@[simp] lemma outer_plus (e : E) : outer src dst e (boundary 1 Cayley.plus)=vertex src dst (some (dst e)) := by
  change cell _ _ (boundary 1 Cayley.plus)=_
  rw [cell_boundary,oneBoundary_plus]
  rfl
def sides (e : E) : C(Sphere 1,C(I,One src dst)) :=
  ⟨fun x=>radial src dst (if x=Cayley.minus then src e else dst e),continuous_of_discreteTopology⟩
def ends (e : E) : C(Disk 1,One src dst × One src dst) :=
  ⟨fun d=>(outer src dst e d,vertex src dst none),(outer src dst e).continuous.prodMk continuous_const⟩
lemma compatible (e : E) (x : Sphere 1) : pathEndpoint (sides src dst e x)=ends src dst e (boundary 1 x) := by
  rcases Cayley.sphere_one_eq x with rfl|rfl <;>
    simp [pathEndpoint,sides,ends,Ne.symm minus_ne_plus]
def twoBoundary (e : E) : C(Sphere 2,One src dst) := cylinderBoundaryMap (sides src dst e) (ends src dst e) (compatible src dst e)
abbrev Cone := Space (twoBoundary src dst)
def inclusion : C(One src dst,Cone src dst) := ⟨base _,continuous_base _⟩
def apex : Cone src dst := inclusion src dst (vertex src dst none)
def square (e : E) : C(Disk 2,Cone src dst) := cell _ e
lemma square_side (e : E) (x : Sphere 1) (t : I) :
    square src dst e (diskCons (boundary 1 x) t)=inclusion src dst (sides src dst e x t) := by
  change cell _ e (boundary 2 ⟨_,cons_mem_sphere_of_boundary x t⟩)=_
  rw [cell_boundary]
  exact congrArg (inclusion src dst) (cylinder_side _ _ _ x t)
lemma square_bottom (e : E) (d : Disk 1) :
    square src dst e (diskCons d 0)=inclusion src dst (outer src dst e d) := by
  change cell _ e (boundary 2 ⟨_,cons_zero_mem_sphere d⟩)=_
  rw [cell_boundary]
  exact congrArg (inclusion src dst) (cylinder_bottom _ _ _ d)
lemma square_top (e : E) (d : Disk 1) : square src dst e (diskCons d 1)=apex src dst := by
  change cell _ e (boundary 2 ⟨_,cons_one_mem_sphere d⟩)=_
  rw [cell_boundary]
  exact congrArg (inclusion src dst) (cylinder_top _ _ _ d)
def joinTime (r t : I) : I := ⟨r.1+(1-r.1)*t.1,by
  constructor
  · nlinarith [r.2.1,r.2.2,t.2.1,t.2.2]
  · nlinarith [r.2.1,r.2.2,t.2.1,t.2.2]⟩
lemma continuous_joinTime : Continuous (fun p : I×I=>joinTime p.1 p.2) := by
  unfold joinTime
  fun_prop
@[simp] lemma joinTime_zero (r : I) : joinTime r 0=r := by ext; simp [joinTime]
@[simp] lemma joinTime_one (r : I) : joinTime r 1=1 := by ext; simp [joinTime]
@[simp] lemma zero_joinTime (t : I) : joinTime 0 t=t := by ext; simp [joinTime]
@[simp] lemma one_joinTime (t : I) : joinTime 1 t=1 := by ext; simp [joinTime]
def vertexPaths : C(Option V,C(I,Cone src dst)) :=
  ⟨fun v=>match v with
    | none => .const _ (apex src dst)
    | some v => (inclusion src dst).comp (radial src dst v),continuous_of_discreteTopology⟩
def radialPaths (v : V) : C(Disk 1,C(I,Cone src dst)) :=
  (⟨fun p : Disk 1×I=>inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime p.1) p.2)),
    (inclusion src dst).continuous.comp ((radial src dst v).continuous.comp
      (continuous_joinTime.comp ((Cayley.continuous_edgeTime.comp continuous_fst).prodMk continuous_snd)))⟩ :
    C(Disk 1×I,Cone src dst)).curry
def outerPaths (e : E) : C(Disk 1,C(I,Cone src dst)) :=
  ((square src dst e).comp ⟨fun p : Disk 1×I=>diskCons p.1 p.2,continuous_diskCons⟩).curry
def edgePaths : V⊕E → C(Disk 1,C(I,Cone src dst)) := Sum.elim (radialPaths src dst) (outerPaths src dst)
lemma edgePaths_boundary (i : V⊕E) (x : Sphere 1) :
    edgePaths src dst i (boundary 1 x)=vertexPaths src dst (oneBoundary src dst i x) := by
  ext t
  cases i with
  | inl v =>
    rcases Cayley.sphere_one_eq x with rfl|rfl
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime (boundary 1 Cayley.minus)) t))=_
      simp [Cayley.edgeTime_minus,vertexPaths,endpoint]
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime (boundary 1 Cayley.plus)) t))=_
      simp [Cayley.edgeTime_plus,vertexPaths,endpoint,apex]
  | inr e =>
    change square src dst e (diskCons (boundary 1 x) t)=_
    rw [square_side]
    rcases Cayley.sphere_one_eq x with rfl|rfl <;>
      simp [sides,vertexPaths,endpoint,Ne.symm minus_ne_plus]
def onePaths : C(One src dst,C(I,Cone src dst)) :=
  lift _ (vertexPaths src dst) (edgePaths src dst) (edgePaths_boundary src dst)
@[simp] lemma onePaths_vertex (v : Option V) : onePaths src dst (vertex src dst v)=vertexPaths src dst v := rfl
@[simp] lemma onePaths_outer (e : E) (d : Disk 1) (t : I) :
    onePaths src dst (outer src dst e d) t=square src dst e (diskCons d t) := by
  change onePaths src dst (cell (oneBoundary src dst) (.inr e) d) t=_
  simp only [onePaths,lift_cell]
  rfl
@[simp] lemma onePaths_radial (v : V) (r t : I) :
    onePaths src dst (radial src dst v r) t=inclusion src dst (radial src dst v (joinTime r t)) := by
  change onePaths src dst (cell (oneBoundary src dst) (.inl v) (Cayley.edgeParam r)) t=_
  simp only [onePaths,lift_cell]
  change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime (Cayley.edgeParam r)) t))=_
  rw [Cayley.edgeTime_param]
def squarePaths (e : E) : C(Disk 2,C(I,Cone src dst)) :=
  (⟨fun p : Disk 2×I=>square src dst e (diskCons (diskTail p.1) (joinTime (diskTime p.1) p.2)),
    (square src dst e).continuous.comp (continuous_diskCons.comp
      ((continuous_diskTail.comp continuous_fst).prodMk (continuous_joinTime.comp
      ((continuous_diskTime.comp continuous_fst).prodMk continuous_snd))))⟩ : C(Disk 2×I,Cone src dst)).curry
lemma squarePaths_boundary (e : E) (x : Sphere 2) :
    squarePaths src dst e (boundary 2 x)=onePaths src dst (twoBoundary src dst e x) := by
  ext t
  change square src dst e (diskCons (diskTail (boundary 2 x)) (joinTime (diskTime (boundary 2 x)) t))=_
  rcases sphere_split x with hz|ho|hs
  · have ht : diskTime (boundary 2 x)=0 := faceTime_eq_zero x hz
    rw [ht,zero_joinTime]
    have hx : twoBoundary src dst e x=outer src dst e (diskTail (boundary 2 x)) := by
      exact cylinderBoundaryMap_face _ _ _ (some false) ⟨x,hz⟩
    rw [hx,onePaths_outer]
  · have ht : diskTime (boundary 2 x)=1 := faceTime_eq_one x ho
    rw [ht,one_joinTime,square_top]
    have hx : twoBoundary src dst e x=vertex src dst none := by
      exact cylinderBoundaryMap_face _ _ _ (some true) ⟨x,ho⟩
    rw [hx,onePaths_vertex]
    rfl
  · let z : Sphere 1 := ⟨(diskTail (boundary 2 x)).1,hs⟩
    have hx : twoBoundary src dst e x=sides src dst e z (diskTime (boundary 2 x)) :=
      cylinderBoundaryMap_face _ _ _ none ⟨x,hs⟩
    rw [hx]
    change square src dst e (diskCons (boundary 1 z) (joinTime (diskTime (boundary 2 x)) t))=_
    rw [square_side]
    change inclusion src dst (radial src dst (if z=Cayley.minus then src e else dst e) _)=
      onePaths src dst (radial src dst (if z=Cayley.minus then src e else dst e) _) _
    rw [onePaths_radial]
def contractionPaths : C(Cone src dst,C(I,Cone src dst)) :=
  lift _ (onePaths src dst) (squarePaths src dst) (squarePaths_boundary src dst)
lemma onePaths_zero (z : One src dst) : onePaths src dst z 0=inclusion src dst z := by
  obtain ⟨q,rfl⟩ := quotient_surjective (oneBoundary src dst) z
  cases q with
  | inl v =>
    change vertexPaths src dst v 0=inclusion src dst (vertex src dst v)
    cases v <;> simp [vertexPaths,apex]
  | inr p =>
    change onePaths src dst (cell (oneBoundary src dst) p.1 p.2) 0=_
    simp only [onePaths,lift_cell]
    rcases p with ⟨v|e,d⟩
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime d) 0))=_
      rw [joinTime_zero]
      change inclusion src dst (cell _ (.inl v) (Cayley.edgeParam (Cayley.edgeTime d)))=_
      rw [Cayley.edgeParam_time]
      rfl
    · exact square_bottom src dst e d
lemma onePaths_one (z : One src dst) : onePaths src dst z 1=apex src dst := by
  obtain ⟨q,rfl⟩ := quotient_surjective (oneBoundary src dst) z
  cases q with
  | inl v =>
    change vertexPaths src dst v 1=apex src dst
    cases v <;> simp [vertexPaths,apex]
  | inr p =>
    change onePaths src dst (cell (oneBoundary src dst) p.1 p.2) 1=_
    simp only [onePaths,lift_cell]
    rcases p with ⟨v|e,d⟩
    · change inclusion src dst (radial src dst v (joinTime (Cayley.edgeTime d) 1))=_
      rw [joinTime_one,radial_one]
      rfl
    · exact square_top src dst e d
def contraction : (ContinuousMap.id (Cone src dst)).Homotopy (.const _ (apex src dst)) where
  toFun p := contractionPaths src dst p.2 p.1
  continuous_toFun := (contractionPaths src dst).uncurry.continuous.comp continuous_swap
  map_zero_left z := by
    obtain ⟨q,rfl⟩ := quotient_surjective (twoBoundary src dst) z
    cases q with
    | inl v => exact onePaths_zero src dst v
    | inr p =>
      change contractionPaths src dst (cell (twoBoundary src dst) p.1 p.2) 0=_
      simp only [contractionPaths,lift_cell]
      change square src dst p.1 (diskCons (diskTail p.2) (joinTime (diskTime p.2) 0))=_
      rw [joinTime_zero,cons_tail_time]
      rfl
  map_one_left z := by
    obtain ⟨q,rfl⟩ := quotient_surjective (twoBoundary src dst) z
    cases q with
    | inl v => exact onePaths_one src dst v
    | inr p =>
      change contractionPaths src dst (cell (twoBoundary src dst) p.1 p.2) 1=_
      simp only [contractionPaths,lift_cell]
      change square src dst p.1 (diskCons (diskTail p.2) (joinTime (diskTime p.2) 1))=_
      rw [joinTime_one,square_top]
      rfl
instance contractible : ContractibleSpace (Cone src dst) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨apex src dst,⟨contraction src dst⟩⟩
end
end TorsionFreeZeroDivisors.GraphConeCW


end

end OAI
