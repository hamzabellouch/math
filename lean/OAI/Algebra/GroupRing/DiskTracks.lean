import Mathlib
import OAI.Algebra.GroupRing.ConeCells

namespace OAI



section
namespace TorsionFreeZeroDivisors.DiskTracks
open Set Metric Topology GroupRingTopology GroupRingTopology.Attachment
open GroupRingTopology.Cellular hiding Disk Sphere boundary
open scoped unitInterval
noncomputable section
variable {Y : Type} [TopologicalSpace Y] {y : Y} {p : Path y y}
def square (c : Path p (Path.refl y)) : C(Disk 2,Y) :=
  ⟨fun d=>c (diskTime d) (Cayley.edgeTime (diskTail d)),
   (Path.continuous_uncurry_iff.mpr c.continuous).comp
     (continuous_diskTime.prodMk (Cayley.continuous_edgeTime.comp continuous_diskTail))⟩
lemma square_boundary (c : Path p (Path.refl y)) (z : Sphere 2) :
    square c (boundary 2 z)=LoopSphere.map p z := by
  have hz : z∈⋃i,cylinderFace 1 i := by rw [cylinderFace_cover];trivial
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  change _=cylinderBoundaryMap _ _ _ z
  rw [cylinderBoundaryMap_face _ _ _ i ⟨z,hi⟩]
  cases i with
  | none =>
    have he : diskTail (boundary 2 z)=boundary 1 (faceSphere ⟨z,hi⟩) := rfl
    change c (diskTime (boundary 2 z)) (Cayley.edgeTime (diskTail (boundary 2 z)))=y
    rw [he]
    obtain hh|hh := Cayley.sphere_one_eq (faceSphere ⟨z,hi⟩)
    · rw [hh,Cayley.edgeTime_minus,Path.source]
    · rw [hh,Cayley.edgeTime_plus,Path.target]
  | some b =>
    cases b
    · have ht : diskTime (boundary 2 z)=0 := by
        apply Subtype.ext
        change (z.1 0+1)/2=0
        change z.1 0= -1 at hi
        rw [hi];norm_num
      change c (diskTime (boundary 2 z)) (Cayley.edgeTime (diskTail (boundary 2 z)))=p _
      rw [ht,c.source];rfl
    · have ht : diskTime (boundary 2 z)=1 := by
        apply Subtype.ext
        change (z.1 0+1)/2=1
        change z.1 0=1 at hi
        rw [hi];norm_num
      change c (diskTime (boundary 2 z)) (Cayley.edgeTime (diskTail (boundary 2 z)))=y
      rw [ht,c.target];rfl
variable (F : C(Disk 2,Y)) (hF : ∀z,F (boundary 2 z)=LoopSphere.map p z)
def physical : Path p (Path.refl y) where
  toFun t := {
    toFun s := F (diskCons (Cayley.edgeParam s) t)
    continuous_toFun := F.continuous.comp (continuous_diskCons.comp
      (Cayley.continuous_edgeParam.prodMk continuous_const))
    source' := by
      rw [Cayley.edgeParam_zero]
      erw [hF ⟨_,cons_mem_sphere_of_boundary Cayley.minus t⟩]
      exact GraphConeCW.cylinder_side _ _ _ _ _
    target' := by
      rw [Cayley.edgeParam_one]
      erw [hF ⟨_,cons_mem_sphere_of_boundary Cayley.plus t⟩]
      exact GraphConeCW.cylinder_side _ _ _ _ _ }
  continuous_toFun := Path.continuous_uncurry_iff.mp (F.continuous.comp
    (continuous_diskCons.comp ((Cayley.continuous_edgeParam.comp continuous_snd).prodMk continuous_fst)))
  source' := by
    ext s
    change F (diskCons (Cayley.edgeParam s) 0)=p s
    erw [hF ⟨_,cons_zero_mem_sphere (Cayley.edgeParam s)⟩]
    unfold LoopSphere.map
    erw [GraphConeCW.cylinder_bottom]
    change p (Cayley.edgeTime (Cayley.edgeParam s))=p s
    rw [Cayley.edgeTime_param]
  target' := by
    ext s
    change F (diskCons (Cayley.edgeParam s) 1)=y
    erw [hF ⟨_,cons_one_mem_sphere (Cayley.edgeParam s)⟩]
    exact GraphConeCW.cylinder_top _ _ _ _
lemma square_physical : square (physical F hF)=F := by
  ext d
  change F (diskCons (Cayley.edgeParam (Cayley.edgeTime (diskTail d))) (diskTime d))=F d
  rw [Cayley.edgeParam_time,GraphConeCW.cons_tail_time]

def shift (t s : unitInterval) : unitInterval :=
  ⟨t+(1-t)*s,by constructor <;> nlinarith [t.2.1,t.2.2,s.2.1,s.2.2]⟩
lemma continuous_shift : Continuous (fun q : unitInterval×unitInterval=>shift q.1 q.2) := by
  apply Continuous.subtype_mk
  fun_prop
@[simp] lemma shift_zero (s : unitInterval) : shift 0 s=s := by ext;simp [shift]
@[simp] lemma shift_one (s : unitInterval) : shift 1 s=1 := by ext;simp [shift]
@[simp] lemma shift_zero_right (t : unitInterval) : shift t 0=t := by ext;simp [shift]
@[simp] lemma shift_one_right (t : unitInterval) : shift t 1=1 := by ext;simp [shift]
def tail (c : Path p (Path.refl y)) (t : unitInterval) : Path (c t) (Path.refl y) where
  toFun s:=c (shift t s)
  continuous_toFun:=c.continuous.comp (continuous_shift.comp (continuous_const.prodMk continuous_id))
  source':=by rw [shift_zero_right]
  target':=by rw [shift_one_right,c.target]
def contract (c : Path p (Path.refl y)) : (square c).Homotopy (.const _ y) where
  toFun z:=square (tail c z.1) z.2
  continuous_toFun := (Path.continuous_uncurry_iff.mpr c.continuous).comp
    ((continuous_shift.comp (continuous_fst.prodMk (continuous_diskTime.comp continuous_snd))).prodMk
      (Cayley.continuous_edgeTime.comp (continuous_diskTail.comp continuous_snd)))
  map_zero_left d := by change c (shift 0 (diskTime d)) _=c _ _;rw [shift_zero]
  map_one_left d := by change c (shift 1 (diskTime d)) _=y;rw [shift_one,c.target];rfl
lemma contract_boundary (c : Path p (Path.refl y)) (t : unitInterval) (z : Sphere 2) :
    contract c (t,boundary 2 z)=LoopSphere.map (c t) z := square_boundary (tail c t) z
end
end TorsionFreeZeroDivisors.DiskTracks

end



end OAI
