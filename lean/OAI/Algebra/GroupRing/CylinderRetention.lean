import Mathlib
import OAI.Algebra.GroupRing.LoopSphere

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology

namespace TorsionFreeZeroDivisors.CylinderRetention
open Set Metric Topology GroupRingTopology GroupRingTopology.Cellular
noncomputable section
variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}

/-- Converse to the cylinder filling construction: an extension of the family
of paths, with its specified ends, extends the entire cylinder boundary. -/
theorem extends_of_path_family (a : C(Sphere n,C(unitInterval,Y)))
    (b : C(Disk n,Y × Y)) (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
    (e : C(Disk n,C(unitInterval,Y))) (he : ∀ x, e (boundary n x) = a x)
    (hend : ∀ x, pathEndpoint (e x) = b x) :
    SphereTopology.Extends (cylinderBoundaryMap a b h) := by
  let F : C(Disk (n+1),Y) :=
    ⟨fun x => e (diskTail x) (diskTime x),
      continuous_eval.comp ((e.continuous.comp continuous_diskTail).prodMk continuous_diskTime)⟩
  refine ⟨F,ContinuousMap.ext fun x => ?_⟩
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ i, cylinderFace n i by rw [cylinderFace_cover]; trivial)
  rw [ContinuousMap.comp_apply,cylinderBoundaryMap_face a b h i ⟨x,hi⟩]
  cases i with
  | none =>
    change e (diskTail (boundary (n+1) x)) (diskTime (boundary (n+1) x)) =
      a (faceSphere ⟨x,hi⟩) (diskTime (boundary (n+1) x))
    exact congrArg (fun q : C(unitInterval,Y) => q (diskTime (boundary (n+1) x)))
      (he (faceSphere ⟨x,hi⟩))
  | some c =>
    cases c
    · change e (diskTail (boundary (n+1) x)) (diskTime (boundary (n+1) x)) =
        (b (diskTail (boundary (n+1) x))).1
      rw [faceTime_eq_zero x hi]
      exact congrArg Prod.fst (hend _)
    · change e (diskTail (boundary (n+1) x)) (diskTime (boundary (n+1) x)) =
        (b (diskTail (boundary (n+1) x))).2
      rw [faceTime_eq_one x hi]
      exact congrArg Prod.snd (hend _)

def firstHalf : C(unitInterval,unitInterval) :=
  ⟨fun t => ⟨t.1/2,by constructor <;> nlinarith [t.2.1,t.2.2]⟩,
    by apply Continuous.subtype_mk; fun_prop⟩
def secondHalf : C(unitInterval,unitInterval) :=
  ⟨fun t => ⟨(t.1+1)/2,by constructor <;> nlinarith [t.2.1,t.2.2]⟩,
    by apply Continuous.subtype_mk; fun_prop⟩
def mid : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
@[simp] lemma firstHalf_zero : firstHalf 0 = 0 := by ext; norm_num [firstHalf]
@[simp] lemma firstHalf_one : firstHalf 1 = mid := by ext; norm_num [firstHalf,mid]
@[simp] lemma secondHalf_zero : secondHalf 0 = mid := by ext; norm_num [secondHalf,mid]
@[simp] lemma secondHalf_one : secondHalf 1 = 1 := by ext; norm_num [secondHalf]

def restrictPaths (a : C(Sphere n,C(unitInterval,Y))) (r : C(unitInterval,unitInterval)) :
    C(Sphere n,C(unitInterval,Y)) :=
  (a.uncurry.comp ⟨fun p => (p.1,r p.2),continuous_fst.prodMk (r.continuous.comp continuous_snd)⟩).curry
@[simp] lemma restrictPaths_apply (a : C(Sphere n,C(unitInterval,Y)))
    (r : C(unitInterval,unitInterval)) (x : Sphere n) (t : unitInterval) :
    restrictPaths a r x t = a x (r t) := rfl

def leftEnds (b : C(Disk n,Y × Y)) (k : C(Disk n,Y)) : C(Disk n,Y × Y) :=
  ⟨fun x => ((b x).1,k x),(continuous_fst.comp b.continuous).prodMk k.continuous⟩
def rightEnds (b : C(Disk n,Y × Y)) (k : C(Disk n,Y)) : C(Disk n,Y × Y) :=
  ⟨fun x => (k x,(b x).2),k.continuous.prodMk (continuous_snd.comp b.continuous)⟩

variable (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))
  (h : ∀ x, pathEndpoint (a x) = b (boundary n x))
  (k : C(Disk n,Y)) (hk : ∀ x, k (boundary n x) = a x mid)
include h hk in
lemma left_compatible (x : Sphere n) :
    pathEndpoint (restrictPaths a firstHalf x) = leftEnds b k (boundary n x) := by
  apply Prod.ext
  · change a x (firstHalf 0) = (b (boundary n x)).1
    rw [firstHalf_zero]
    exact congrArg Prod.fst (h x)
  · change a x (firstHalf 1) = k (boundary n x)
    rw [firstHalf_one,hk]
include h hk in
lemma right_compatible (x : Sphere n) :
    pathEndpoint (restrictPaths a secondHalf x) = rightEnds b k (boundary n x) := by
  apply Prod.ext
  · change a x (secondHalf 0) = k (boundary n x)
    rw [secondHalf_zero,hk]
  · change a x (secondHalf 1) = (b (boundary n x)).2
    rw [secondHalf_one]
    exact congrArg Prod.snd (h x)

/-- If both spheres cut and capped by the SAME middle disk extend, so does
 the original sphere. This is a topological gluing statement, not word reduction. -/
theorem extends_of_capped_halves
    (hL : SphereTopology.Extends (cylinderBoundaryMap (restrictPaths a firstHalf)
      (leftEnds b k) (left_compatible a b h k hk)))
    (hR : SphereTopology.Extends (cylinderBoundaryMap (restrictPaths a secondHalf)
      (rightEnds b k) (right_compatible a b h k hk))) :
    SphereTopology.Extends (cylinderBoundaryMap a b h) := by
  obtain ⟨FL,hFL⟩ := hL
  obtain ⟨FR,hFR⟩ := hR
  obtain ⟨eL,heL,hendL⟩ := cylinderFill _ _ (left_compatible a b h k hk) FL
    (fun x => congrArg (fun f : C(Sphere (n+1),Y) => f x) hFL)
  obtain ⟨eR,heR,hendR⟩ := cylinderFill _ _ (right_compatible a b h k hk) FR
    (fun x => congrArg (fun f : C(Sphere (n+1),Y) => f x) hFR)
  let b0 : C(Disk n,Y) := ⟨fun x=>(b x).1,continuous_fst.comp b.continuous⟩
  let b1 : C(Disk n,Y) := ⟨fun x=>(b x).2,continuous_snd.comp b.continuous⟩
  let HL : ContinuousMap.Homotopy b0 k :=
    { toFun := fun p => eL p.2 p.1
      continuous_toFun := eL.uncurry.continuous.comp continuous_swap
      map_zero_left := fun x => congrArg Prod.fst (hendL x)
      map_one_left := fun x => congrArg Prod.snd (hendL x) }
  let HR : ContinuousMap.Homotopy k b1 :=
    { toFun := fun p => eR p.2 p.1
      continuous_toFun := eR.uncurry.continuous.comp continuous_swap
      map_zero_left := fun x => congrArg Prod.fst (hendR x)
      map_one_left := fun x => congrArg Prod.snd (hendR x) }
  let H := HL.trans HR
  let e : C(Disk n,C(unitInterval,Y)) :=
    (H.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
  apply extends_of_path_family a b h e
  · intro x
    ext t
    change H (t,boundary n x) = a x t
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · change eL (boundary n x) _ = a x t
      rw [heL,restrictPaths_apply]
      congr 1
      apply Subtype.ext
      change (2*t.1)/2=t.1
      ring
    · change eR (boundary n x) _ = a x t
      rw [heR,restrictPaths_apply]
      congr 1
      apply Subtype.ext
      change (2*t.1-1+1)/2=t.1
      ring
  · intro x
    apply Prod.ext
    · exact H.map_zero_left x
    · exact H.map_one_left x

/-- A nonextendable sphere retains an essential capped component. -/
theorem essential_capped_half
    (hess : ¬ SphereTopology.Extends (cylinderBoundaryMap a b h)) :
    (¬ SphereTopology.Extends (cylinderBoundaryMap (restrictPaths a firstHalf)
      (leftEnds b k) (left_compatible a b h k hk))) ∨
    (¬ SphereTopology.Extends (cylinderBoundaryMap (restrictPaths a secondHalf)
      (rightEnds b k) (right_compatible a b h k hk))) := by
  by_contra hc
  push Not at hc
  exact hess (extends_of_capped_halves a b h k hk hc.1 hc.2)
/-- A common contractible cone supplies one and the same middle cap to both
pieces. No universal-cover homology comparison is needed for this gluing proof. -/
theorem exists_common_cap {Z : Type*} [TopologicalSpace Z] [ContractibleSpace Z]
    [Nonempty (Sphere n)] (j : C(Z,Y)) (m : C(Sphere n,Z))
    (hm : ∀ x, j (m x) = a x mid) :
    ∃ k : C(Disk n,Y), ∀ x, k (boundary n x) = a x mid := by
  have hn : m.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using (id_nullhomotopic Z).comp_left m
  obtain ⟨z,⟨H⟩⟩ := hn
  obtain ⟨K,hK⟩ := SphereTopology.extends_of_nullhomotopic H.symm
  refine ⟨j.comp K,fun x => ?_⟩
  change j (K (boundary n x)) = a x mid
  rw [show K (boundary n x) = m x from ContinuousMap.congr_fun hK x]
  exact hm x

end
end TorsionFreeZeroDivisors.CylinderRetention

end OAI
