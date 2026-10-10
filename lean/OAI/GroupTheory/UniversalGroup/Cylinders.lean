import OAI.GroupTheory.UniversalGroup.ControlledHomotopies

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

namespace UniversalFInfinity.Cylinder

section
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1
abbrev Rim (n : ℕ) := {p : unitInterval × Disk n // p.1 = 0 ∨ p.2.1 ∈ sphere 0 1}

variable {n : ℕ}
def denominator (p : unitInterval × Disk n) : ℝ := max (2-(p.1:ℝ)) (2*‖p.2.1‖)
lemma denominator_bounds (p : unitInterval × Disk n) : 1 ≤ denominator p ∧ denominator p ≤ 2 := by
  have hx : ‖p.2.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using p.2.2
  have ht0 := p.1.2.1
  have ht1 := p.1.2.2
  constructor
  · exact (by linarith : 1 ≤ 2-(p.1:ℝ)).trans (le_max_left _ _)
  · exact max_le (by linarith) (by linarith)
lemma denominator_pos (p : unitInterval × Disk n) : 0 < denominator p :=
  lt_of_lt_of_le (by norm_num) (denominator_bounds p).1

def factor (p : unitInterval × Disk n) : ℝ := 2 / denominator p
lemma factor_mul_denominator (p : unitInterval × Disk n) : factor p * denominator p = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (denominator_pos p))
lemma factor_bounds (p : unitInterval × Disk n) : 1 ≤ factor p ∧ factor p ≤ 2 := by
  have hd := denominator_bounds p
  constructor
  · exact (le_div_iff₀ (denominator_pos p)).mpr (by simpa using hd.2)
  · exact (div_le_iff₀ (denominator_pos p)).mpr (by linarith)
lemma factor_nonneg (p : unitInterval × Disk n) : 0 ≤ factor p := (by norm_num : (0:ℝ)≤1).trans (factor_bounds p).1

lemma retract_time_mem (p : unitInterval × Disk n) :
    2 - factor p * (2-(p.1:ℝ)) ∈ (Set.Icc (0:ℝ) 1) := by
  have hd : 2-(p.1:ℝ) ≤ denominator p := le_max_left _ _
  have hmul := mul_le_mul_of_nonneg_left hd (factor_nonneg p)
  have heq := factor_mul_denominator p
  have hf := (factor_bounds p).1
  have ht0 := p.1.2.1
  have ht1 := p.1.2.2
  have hge := mul_le_mul_of_nonneg_right hf (by linarith : 0 ≤ 2-(p.1:ℝ))
  constructor <;> nlinarith

lemma retract_disk_mem (p : unitInterval × Disk n) :
    factor p • p.2.1 ∈ closedBall (0 : Fin n → ℝ) 1 := by
  simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (factor_nonneg p)]
  have hd : 2*‖p.2.1‖ ≤ denominator p := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left hd (factor_nonneg p)
  have heq := factor_mul_denominator p
  nlinarith

lemma retract_mem_rim (p : unitInterval × Disk n) :
    (⟨2-factor p*(2-(p.1:ℝ)),retract_time_mem p⟩ : unitInterval) = 0 ∨
      factor p • p.2.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
  rcases le_total (2*‖p.2.1‖) (2-(p.1:ℝ)) with h | h
  · left
    apply Subtype.ext
    have hd : denominator p = 2-(p.1:ℝ) := max_eq_left h
    have heq := factor_mul_denominator p
    rw [hd] at heq
    simpa only [Set.Icc.coe_zero,sub_eq_zero] using heq.symm
  · right
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg (factor_nonneg p)]
    have hd : denominator p = 2*‖p.2.1‖ := max_eq_right h
    have heq := factor_mul_denominator p
    rw [hd] at heq
    nlinarith

lemma continuous_denominator : Continuous (@denominator n) :=
  (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).max
    (continuous_const.mul ((continuous_subtype_val.comp continuous_snd).norm))
lemma continuous_factor : Continuous (@factor n) :=
  continuous_const.div continuous_denominator (fun p => ne_of_gt (denominator_pos p))

def retract (n : ℕ) : C(unitInterval × Disk n,Rim n) := by
  have htime : Continuous (fun p : unitInterval × Disk n =>
      (⟨2-factor p*(2-(p.1:ℝ)),retract_time_mem p⟩ : unitInterval)) :=
    (continuous_const.sub (continuous_factor.mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))).subtype_mk _
  have hdisk : Continuous (fun p : unitInterval × Disk n =>
      (⟨factor p • p.2.1,retract_disk_mem p⟩ : Disk n)) :=
    (continuous_factor.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  exact ⟨fun p => ⟨(⟨_,retract_time_mem p⟩,⟨_,retract_disk_mem p⟩),retract_mem_rim p⟩,
    (htime.prodMk hdisk).subtype_mk _⟩

lemma retract_of_rim (p : Rim n) : (retract n p.1).1 = p.1 := by
  have hd : denominator p.1 = 2 := by
    rcases p.2 with ht | hx
    · have hx' : ‖p.1.2.1‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using p.1.2.2
      simp only [denominator,ht,Set.Icc.coe_zero,sub_zero]
      exact max_eq_left (by linarith)
    · have hx' : ‖p.1.2.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hx
      simp only [denominator,hx',mul_one]
      exact max_eq_right (by linarith [p.1.1.2.1])
  have hf : factor p.1 = 1 := by simp [factor,hd]
  apply Prod.ext
  · apply Subtype.ext
    change 2-factor p.1*(2-(p.1.1:ℝ)) = (p.1.1:ℝ)
    rw [hf,one_mul]
    ring
  · apply Subtype.ext
    change factor p.1 • p.1.2.1 = p.1.2.1
    rw [hf,one_smul]

end

open Set Metric Topology
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y]

lemma continuous_finite_closed_paste {A : Type*} [TopologicalSpace A] {ι : Type*} [Finite ι]
    (S : ι → Set A) (f : ∀ i, C(S i,Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x,hi⟩ = f j ⟨x,hj⟩)
    (hcover : ⋃ i, S i = Set.univ) (hclosed : ∀ i, IsClosed (S i)) :
    Continuous (Set.liftCover S (fun i => f i) hcompat hcover) := by
  rw [continuous_iff_isClosed]
  intro D hD
  rw [Set.preimage_liftCover]
  exact isClosed_iUnion_of_finite fun i => (hclosed i).isClosedMap_subtype_val _ (hD.preimage (f i).continuous)

def face (n : ℕ) : Bool → Set (Rim n)
  | false => {p | p.1.1 = 0}
  | true => {p | p.1.2.1 ∈ sphere 0 1}
lemma face_closed (n : ℕ) (i : Bool) : IsClosed (face n i) := by
  cases i
  · exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const
  · exact isClosed_sphere.preimage ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val)
lemma face_cover (n : ℕ) : ⋃ i, face n i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rcases p.2 with h | h
  · exact Set.mem_iUnion.mpr ⟨false,h⟩
  · exact Set.mem_iUnion.mpr ⟨true,h⟩

def faceValue (F : C(Disk n,Y)) (H : C(unitInterval × Sphere n,Y)) : ∀ i : Bool, C(face n i,Y)
  | false => ⟨fun p => F p.1.1.2,F.continuous.comp ((continuous_snd.comp continuous_subtype_val).comp continuous_subtype_val)⟩
  | true => ⟨fun p => H (p.1.1.1,⟨p.1.1.2.1,p.2⟩),H.continuous.comp
      (((continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val).prodMk
        (((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val).comp continuous_subtype_val |>.subtype_mk _))⟩

variable (F : C(Disk n,Y)) (H : C(unitInterval × Sphere n,Y))
variable (h : ∀ x : Sphere n, H (0,x) = F ⟨x.1,sphere_subset_closedBall x.2⟩)
include h in
lemma faceValue_compatible (i j : Bool) (p : Rim n) (hi : p ∈ face n i) (hj : p ∈ face n j) :
    faceValue F H i ⟨p,hi⟩ = faceValue F H j ⟨p,hj⟩ := by
  have hcross (h0 : p.1.1 = 0) (hs : p.1.2.1 ∈ sphere 0 1) :
      F p.1.2 = H (p.1.1,⟨p.1.2.1,hs⟩) := by
    rw [h0,h]
  cases i <;> cases j
  · rfl
  · exact hcross hi hj
  · exact (hcross hj hi).symm
  · rfl

def rimMap : C(Rim n,Y) :=
  ⟨Set.liftCover (face n) (fun i => faceValue F H i) (faceValue_compatible F H h) (face_cover n),
    continuous_finite_closed_paste _ _ _ _ (face_closed n)⟩
lemma rimMap_face (i : Bool) (p : face n i) : rimMap F H h p.1 = faceValue F H i p := by
  exact Set.liftCover_coe (S := face n) (f := fun i => faceValue F H i)
    (hf := faceValue_compatible F H h) (hS := face_cover n) p

def extension : C(unitInterval × Disk n,Y) := (rimMap F H h).comp (retract n)

lemma extension_zero (x : Disk n) : extension F H h (0,x) = F x := by
  let p : Rim n := ⟨(0,x),Or.inl rfl⟩
  have heq : retract n (0,x) = p := Subtype.ext (retract_of_rim p)
  change rimMap F H h (retract n (0,x)) = F x
  rw [heq]
  exact rimMap_face F H h false ⟨p,rfl⟩

lemma extension_boundary (t : unitInterval) (x : Sphere n) :
    extension F H h (t,⟨x.1,sphere_subset_closedBall x.2⟩) = H (t,x) := by
  let p : Rim n := ⟨(t,⟨x.1,sphere_subset_closedBall x.2⟩),Or.inr x.2⟩
  have heq : retract n p.1 = p := Subtype.ext (retract_of_rim p)
  change rimMap F H h (retract n p.1) = H (t,x)
  rw [heq]
  exact rimMap_face F H h true ⟨p,x.2⟩

include h in

theorem homotopy_extension : ∃ E : C(unitInterval × Disk n,Y),
    (∀ x, E (0,x) = F x) ∧ ∀ t (x : Sphere n),
      E (t,⟨x.1,sphere_subset_closedBall x.2⟩) = H (t,x) :=
  ⟨extension F H h,extension_zero F H h,extension_boundary F H h⟩

end UniversalFInfinity.Cylinder

namespace UniversalFInfinity.SphereCube
open Set Metric Topology Cellular
open scoped Topology.Homotopy
universe u v
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]

def rimSphere (n : ℕ) : C(Cylinder.Rim n,Sphere (n+1)) := by
  refine ⟨fun p => ⟨(diskCons p.1.2 p.1.1).1,?_⟩,?_⟩
  · rcases p.2 with h | h
    · rw [h]; exact cons_zero_mem_sphere p.1.2
    · exact cons_mem_sphere_of_boundary ⟨p.1.2.1,h⟩ p.1.1
  · exact (continuous_subtype_val.comp
      (continuous_diskCons.comp ((continuous_snd.comp continuous_subtype_val).prodMk
        (continuous_fst.comp continuous_subtype_val)))).subtype_mk _

def rimSide (n : ℕ) : C(Sphere n × unitInterval,Cylinder.Rim n) :=
  ⟨fun p => ⟨(p.2,boundary n p.1),Or.inr p.1.2⟩,
    (continuous_snd.prodMk ((continuous_boundary n).comp continuous_fst)).subtype_mk _⟩

def rimBottom (n : ℕ) : C(Disk n,Cylinder.Rim n) :=
  ⟨fun x => ⟨(0,x),Or.inl rfl⟩,(continuous_const.prodMk continuous_id).subtype_mk _⟩

def top (n : ℕ) : C(Disk n,Sphere (n+1)) :=
  ⟨fun d => ⟨(diskCons d 1).1,cons_one_mem_sphere d⟩,
    (continuous_subtype_val.comp (continuous_diskCons.comp
      (continuous_id.prodMk continuous_const))).subtype_mk _⟩

lemma rim_contractible (n : ℕ) : ContractibleSpace (Cylinder.Rim n) := by
  let : ContractibleSpace (Disk n) := (convex_closedBall (0 : Fin n → ℝ) 1).contractibleSpace
    ⟨0,by simp⟩
  let : ContractibleSpace unitInterval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by simp⟩
  obtain ⟨p,⟨H⟩⟩ := id_nullhomotopic (unitInterval × Disk n)
  let inc : C(Cylinder.Rim n,unitInterval × Disk n) := ⟨Subtype.val,continuous_subtype_val⟩
  let K := (ContinuousMap.Homotopy.refl (Cylinder.retract n)).comp (H.compContinuousMap inc)
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨Cylinder.retract n p,⟨?_⟩⟩
  have he : (Cylinder.retract n).comp ((ContinuousMap.id _).comp inc) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (Cylinder.retract_of_rim x)
  exact he ▸ K

lemma rim_nullhomotopy [PathConnectedSpace Y] (f : C(Sphere (n+1),Y)) (y : Y) :
    Nonempty ((f.comp (rimSphere n)).Homotopy (ContinuousMap.const _ y)) := by
  let := rim_contractible n
  obtain ⟨p,⟨H⟩⟩ := id_nullhomotopic (Cylinder.Rim n)
  let F := f.comp (rimSphere n)
  let K := (ContinuousMap.Homotopy.refl F).comp H
  let q : Path (F p) y := Classical.choice (PathConnectedSpace.joined _ _)
  let L : (ContinuousMap.const (Cylinder.Rim n) (F p)).Homotopy (ContinuousMap.const _ y) :=
    { toFun := fun z => q z.1
      continuous_toFun := q.continuous.comp continuous_fst
      map_zero_left := fun _ => q.source
      map_one_left := fun _ => q.target }
  exact ⟨K.trans L⟩

variable (f : C(Sphere (n+1),Y)) (y : Y)
variable (K : (f.comp (rimSphere n)).Homotopy (ContinuousMap.const _ y))

def edgeTrace : C(unitInterval × Sphere n,Y) :=
  ⟨fun p => K (p.1,rimSide n (p.2,1)),K.continuous.comp
    (continuous_fst.prodMk ((rimSide n).continuous.comp
      (continuous_snd.prodMk continuous_const)))⟩

lemma edgeTrace_zero (s : Sphere n) : edgeTrace f y K (0,s) = (f.comp (top n)) (boundary n s) := by
  change K (0,rimSide n (s,1)) = _
  rw [ContinuousMap.Homotopy.apply_zero]
  rfl

def topExtension : C(unitInterval × Disk n,Y) :=
  Cylinder.extension (f.comp (top n)) (edgeTrace f y K) (edgeTrace_zero f y K)

lemma topExtension_zero (x : Disk n) : topExtension f y K (0,x) = f (top n x) :=
  Cylinder.extension_zero _ _ _ x
lemma topExtension_boundary (t : unitInterval) (s : Sphere n) :
    topExtension f y K (t,boundary n s) = K (t,rimSide n (s,1)) :=
  Cylinder.extension_boundary _ _ _ t s

def normalizedTop : C(Disk n,Y) := (topExtension f y K).comp
  ⟨fun x => (1,x),continuous_const.prodMk continuous_id⟩
lemma normalizedTop_boundary (s : Sphere n) : normalizedTop f y K (boundary n s) = y := by
  change topExtension f y K (1,boundary n s) = y
  rw [topExtension_boundary,ContinuousMap.Homotopy.apply_one,ContinuousMap.const_apply]

def sidePaths : C(Sphere n,C(unitInterval,C(unitInterval,Y))) :=
  (⟨fun p : (Sphere n × unitInterval) × unitInterval => K (p.2,rimSide n p.1),
    K.continuous.comp (continuous_snd.prodMk ((rimSide n).continuous.comp continuous_fst))⟩ :
      C((Sphere n × unitInterval) × unitInterval,Y)).curry.curry

def bottomPaths : C(Disk n,C(unitInterval,Y)) :=
  (⟨fun p : Disk n × unitInterval => K (p.2,rimBottom n p.1),
    K.continuous.comp (continuous_snd.prodMk ((rimBottom n).continuous.comp continuous_fst))⟩ :
      C(Disk n × unitInterval,Y)).curry

def topPaths : C(Disk n,C(unitInterval,Y)) :=
  ((topExtension f y K).comp ContinuousMap.prodSwap).curry

lemma spherePaths_compatible (s : Sphere n) :
    pathEndpoint (sidePaths f y K s) =
      (bottomPaths f y K (boundary n s),topPaths f y K (boundary n s)) := by
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact (topExtension_boundary f y K t s).symm

private lemma spherePaths_compatible_map (s : Sphere n) :
    pathEndpoint (sidePaths f y K s) =
      ((bottomPaths f y K).prodMk (topPaths f y K)) (boundary n s) :=
  spherePaths_compatible f y K s

def spherePaths : C(Sphere (n+1),C(unitInterval,Y)) :=
  cylinderBoundaryMap (sidePaths f y K)
    ((bottomPaths f y K).prodMk (topPaths f y K)) (spherePaths_compatible_map f y K)

lemma cons_tail_time (x : Disk (n+1)) : diskCons (diskTail x) (diskTime x) = x := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  change 2*((x.1 0+1)/2)-1 = x.1 0
  ring

lemma spherePaths_zero (s : Sphere (n+1)) : spherePaths f y K s 0 = f s := by
  rcases sphere_split s with h | h | h
  · rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨s,h⟩]
    change K (0,rimBottom n (diskTail (boundary (n+1) s))) = f s
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (rimSphere n (rimBottom n (diskTail (boundary (n+1) s)))) = f s
    congr 1
    apply Subtype.ext
    have ht : diskTime (boundary (n+1) s) = 0 := faceTime_eq_zero s h
    exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1) ht).symm.trans
      (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
  · rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨s,h⟩]
    change topExtension f y K (0,diskTail (boundary (n+1) s)) = f s
    rw [topExtension_zero]
    congr 1
    apply Subtype.ext
    have ht : diskTime (boundary (n+1) s) = 1 := faceTime_eq_one s h
    exact (congrArg (fun t => (diskCons (diskTail (boundary (n+1) s)) t).1) ht).symm.trans
      (congrArg Subtype.val (cons_tail_time (boundary (n+1) s)))
  · rw [spherePaths,cylinderBoundaryMap_face _ _ _ none ⟨s,h⟩]
    change K (0,rimSide n (faceSphere ⟨s,h⟩,faceTime none ⟨s,h⟩)) = f s
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (rimSphere n (rimSide n (faceSphere ⟨s,h⟩,faceTime none ⟨s,h⟩))) = f s
    apply congrArg f
    apply Subtype.ext
    change (diskCons (diskTail (boundary (n+1) s)) (diskTime (boundary (n+1) s))).1 = s.1
    exact congrArg Subtype.val (cons_tail_time (boundary (n+1) s))

def normalizedSphere : C(Sphere (n+1),Y) :=
  ⟨fun s => spherePaths f y K s 1,(continuous_eval_const 1).comp (spherePaths f y K).continuous⟩

def normalizeHomotopy : f.Homotopy (normalizedSphere f y K) where
  toFun p := spherePaths f y K p.2 p.1
  continuous_toFun := continuous_eval.comp (((spherePaths f y K).continuous.comp continuous_snd).prodMk continuous_fst)
  map_zero_left s := spherePaths_zero f y K s
  map_one_left _ := rfl

lemma normalizedSphere_rim (x : Cylinder.Rim n) : normalizedSphere f y K (rimSphere n x) = y := by
  rcases x.2 with hx | hx
  · have h : rimSphere n x ∈ cylinderFace n (some false) := by
      change (diskCons x.1.2 x.1.1).1 0 = -1
      simp only [hx,diskCons,Fin.cons_zero,Set.Icc.coe_zero,mul_zero,zero_sub]
    change spherePaths f y K (rimSphere n x) 1 = y
    rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some false) ⟨_,h⟩]
    exact K.apply_one _
  · have h : rimSphere n x ∈ cylinderFace n none := by
      change (diskTail (diskCons x.1.2 x.1.1)).1 ∈ sphere 0 1
      rw [diskTail_cons]; exact hx
    change spherePaths f y K (rimSphere n x) 1 = y
    rw [spherePaths,cylinderBoundaryMap_face _ _ _ none ⟨_,h⟩]
    exact K.apply_one _

lemma normalizedSphere_top (x : Disk n) : normalizedSphere f y K (top n x) = normalizedTop f y K x := by
  have h : top n x ∈ cylinderFace n (some true) := by
    change (diskCons x 1).1 0 = 1
    norm_num [diskCons]
  change spherePaths f y K (top n x) 1 = _
  rw [spherePaths,cylinderBoundaryMap_face _ _ _ (some true) ⟨_,h⟩]
  change topExtension f y K (1,diskTail (diskCons x 1)) = _
  rw [diskTail_cons]
  rfl
end UniversalFInfinity.SphereCube

namespace UniversalFInfinity.DiskCube
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1

def toCube (n : ℕ) : C(Disk n,Fin n → unitInterval) := by
  refine ⟨fun x i => ⟨(x.1 i+1)/2,?_⟩,?_⟩
  · have hx : ‖x.1 i‖ ≤ 1 := (norm_le_pi_norm x.1 i).trans (by simpa only [mem_closedBall,dist_zero_right] using x.2)
    rw [Real.norm_eq_abs,abs_le] at hx
    constructor <;> linarith [hx.1,hx.2]
  · apply continuous_pi
    intro i
    exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const |>.div_const 2).subtype_mk _

def fromCube (n : ℕ) : C((Fin n → unitInterval),Disk n) := by
  refine ⟨fun x => ⟨fun i => 2*(x i:ℝ)-1,?_⟩,?_⟩
  · simp only [mem_closedBall,dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> linarith [(x i).2.1,(x i).2.2]
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const

lemma from_to (n : ℕ) (x : Disk n) : fromCube n (toCube n x) = x := by
  apply Subtype.ext
  funext i
  change 2*((x.1 i+1)/2)-1 = x.1 i
  ring

lemma to_from (n : ℕ) (x : Fin n → unitInterval) : toCube n (fromCube n x) = x := by
  funext i
  apply Subtype.ext
  change ((2*(x i:ℝ)-1)+1)/2 = (x i:ℝ)
  ring

lemma from_boundary (n : ℕ) (x : Fin n → unitInterval) (hx : x ∈ Cube.boundary (Fin n)) :
    (fromCube n x).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi | hi⟩ := hx
  all_goals
    simp only [mem_sphere,dist_zero_right]
    apply le_antisymm
    · simpa only [mem_closedBall,dist_zero_right] using (fromCube n x).2
    · have h := norm_le_pi_norm (fromCube n x).1 i
      change ‖2*(x i:ℝ)-1‖ ≤ _ at h
      norm_num [hi] at h ⊢
      exact h

lemma to_boundary (n : ℕ) (x : Sphere n) :
    toCube n ⟨x.1,sphere_subset_closedBall x.2⟩ ∈ Cube.boundary (Fin n) := by
  have hx : ‖x.1‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using x.2
  have hi : ∃ i, 1 ≤ ‖x.1 i‖ := by
    by_contra! hh
    have := (pi_norm_lt_iff (by norm_num : (0:ℝ)<1)).mpr hh
    linarith
  obtain ⟨i,hi⟩ := hi
  have heq : |x.1 i| = 1 := le_antisymm ((norm_le_pi_norm x.1 i).trans_eq hx) hi
  refine ⟨i,?_⟩
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp heq with h | h
  · right
    apply Subtype.ext
    change (x.1 i+1)/2 = 1
    rw [h]; norm_num
  · left
    apply Subtype.ext
    change (x.1 i+1)/2 = 0
    rw [h]; norm_num

end UniversalFInfinity.DiskCube

end

end OAI
