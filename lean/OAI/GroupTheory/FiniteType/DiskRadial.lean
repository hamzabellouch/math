import Mathlib
import OAI.GroupTheory.FiniteType.RelativeChains

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace DiskRadial
open Set Metric
open scoped unitInterval
variable {E : Type*} [NormedAddCommGroup E]
abbrev Disk := closedBall (0 : E) 1

def denom (v : E) : ℝ := max ‖v‖ (1/2)
lemma denom_pos (v : E) : 0 < denom v := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
lemma le_denom (v : E) : ‖v‖ ≤ denom v := le_max_left _ _
lemma continuous_denom : Continuous (denom : E → ℝ) := continuous_norm.max continuous_const

variable [NormedSpace ℝ E]

def inflate (v : Disk (E := E)) : Disk (E := E) :=
  ⟨(denom (v : E))⁻¹ • (v : E),by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denom_pos _))]
    exact (inv_mul_le_iff₀ (denom_pos (v : E))).mpr (by simpa only [mul_one] using le_denom (v : E))⟩

lemma continuous_inflate : Continuous (inflate (E := E)) := by
  apply Continuous.subtype_mk
  exact ((((continuous_denom (E := E)).comp (continuous_subtype_val : Continuous (Subtype.val : Disk (E := E) → E))).inv₀
    (fun v => (denom_pos (v : E)).ne')).smul continuous_subtype_val)

lemma norm_inflate (v : Disk (E := E)) : ‖(inflate v : E)‖ = (denom (v : E))⁻¹ * ‖(v : E)‖ := by
  simp only [inflate,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (denom_pos _))]

lemma norm_le_inflate (v : Disk (E := E)) : ‖(v : E)‖ ≤ ‖(inflate v : E)‖ := by
  rw [norm_inflate]
  have hd : denom (v : E) ≤ 1 := max_le (by simpa only [mem_closedBall,dist_zero_right] using v.2) (by norm_num)
  have hi : 1 ≤ (denom (v : E))⁻¹ := (one_le_inv₀ (denom_pos _)).mpr hd
  nlinarith [norm_nonneg (v : E)]

lemma inflate_boundary (v : Disk (E := E)) (hv : ‖(v : E)‖ = 1) : inflate v = v := by
  apply Subtype.ext
  norm_num [inflate,denom,hv]

lemma norm_inflate_of_half_lt (v : Disk (E := E)) (hv : 1/2 < ‖(v : E)‖) : ‖(inflate v : E)‖ = 1 := by
  rw [norm_inflate,denom,max_eq_left (le_of_lt hv),inv_mul_cancel₀ (ne_of_gt (lt_trans (by norm_num) hv))]

def radial (t : I) (v : Disk (E := E)) : Disk (E := E) :=
  ⟨(1 - (t : ℝ)) • (v : E) + (t : ℝ) • (inflate v : E),
    (convex_closedBall (0 : E) 1) v.2 (inflate v).2 (sub_nonneg.mpr t.2.2) t.2.1 (by ring)⟩

lemma continuous_radial : Continuous (fun z : I × Disk (E := E) => radial z.1 z.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).add
    ((continuous_subtype_val.comp continuous_fst).smul
      (continuous_subtype_val.comp (continuous_inflate.comp continuous_snd)))

@[simp] lemma radial_zero (v : Disk (E := E)) : radial 0 v = v := by ext; simp [radial]
@[simp] lemma radial_one (v : Disk (E := E)) : radial 1 v = inflate v := by ext; simp [radial]
lemma radial_boundary (t : I) (v : Disk (E := E)) (hv : ‖(v : E)‖ = 1) : radial t v = v := by
  apply Subtype.ext
  change (1-(t:ℝ)) • (v : E) + (t:ℝ) • (inflate v : E) = v
  rw [inflate_boundary v hv,← add_smul]
  simp

lemma norm_radial (t : I) (v : Disk (E := E)) :
    ‖(radial t v : E)‖ = (1-(t:ℝ)) * ‖(v : E)‖ + (t:ℝ) * ‖(inflate v : E)‖ := by
  change ‖(1-(t:ℝ)) • (v:E) + (t:ℝ) • ((denom (v:E))⁻¹ • (v:E))‖ = _
  rw [smul_smul,← add_smul,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (sub_nonneg.mpr t.2.2) (mul_nonneg t.2.1 (inv_nonneg.mpr (le_of_lt (denom_pos _))))),norm_inflate]
  ring

lemma norm_le_radial (t : I) (v : Disk (E := E)) : ‖(v : E)‖ ≤ ‖(radial t v : E)‖ := by
  rw [norm_radial]
  nlinarith [norm_le_inflate v,t.2.1]

end DiskRadial

namespace CWCollar
section
open Set Topology Metric CWExtension
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

def radius (n : ℕ) : C(Skel C (n+1),ℝ) :=
  extendSkel n (ContinuousMap.const _ 1) (fun _ => ⟨fun v => ‖(v : Fin n → ℝ)‖,continuous_norm.comp continuous_subtype_val⟩)
    (by intro i v; change ‖(v : Fin n → ℝ)‖ = 1; simpa only [mem_sphere,dist_zero_right] using v.2)

@[simp] lemma radius_prior (n : ℕ) (x : Skel C n) : radius n (skelIncl n x) = 1 :=
  extendSkel_prior _ _ _ _ _
@[simp] lemma radius_disk (n : ℕ) (i : RelCWComplex.cell C n) (v : Disk n) :
    radius n (charSkel n i v) = ‖(v : Fin n → ℝ)‖ := extendSkel_disk _ _ _ _ _ _

def lower (n : ℕ) : Set (Skel C (n+1)) := Subtype.val ⁻¹' Skel C n

theorem radius_eq_one_iff (n : ℕ) (x : Skel C (n+1)) : radius n x = 1 ↔ x ∈ lower n := by
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · change radius n (skelIncl n a) = 1 ↔ _
    exact ⟨fun _ => a.2,fun _ => radius_prior n a⟩
  · change radius n (charSkel n i v) = 1 ↔ RelCWComplex.map n i v ∈ Skel C n
    rw [radius_disk]
    constructor
    · intro hv
      exact RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨v,by simpa only [mem_sphere,dist_zero_right] using hv,rfl⟩
    · intro hv
      simpa only [mem_sphere,dist_zero_right] using boundary_of_mem_skel n i v hv

def collar (n : ℕ) : Set (Skel C (n+1)) := radius n ⁻¹' Ioi (1/2)
lemma collar_open (n : ℕ) : IsOpen (collar (C := C) n) := isOpen_Ioi.preimage (radius n).continuous
lemma lower_subset_collar (n : ℕ) : lower (C := C) n ⊆ collar n := by
  intro x hx
  change (1/2 : ℝ) < radius n x
  rw [(radius_eq_one_iff n x).mpr hx]
  norm_num

def paths (n : ℕ) : C(Skel C (n+1),C(I,Skel C (n+1))) :=
  extendSkel n
    ⟨fun x => ContinuousMap.const I (skelIncl n x),ContinuousMap.continuous_const'.comp (skelIncl n).continuous⟩
    (fun i => (⟨fun z : Disk n × I => charSkel n i (DiskRadial.radial z.2 z.1),
      (charSkel n i).continuous.comp (DiskRadial.continuous_radial.comp continuous_swap)⟩ : C(_, _)).curry)
    (by
      intro i v
      apply ContinuousMap.ext
      intro t
      change charSkel n i (DiskRadial.radial t ⟨v,sphere_subset_closedBall v.2⟩) = skelIncl n (boundarySkel n i v)
      rw [DiskRadial.radial_boundary t _ (by simpa only [mem_sphere,dist_zero_right] using v.2)]
      rfl)

@[simp] lemma paths_prior (n : ℕ) (x : Skel C n) (t : I) : paths n (skelIncl n x) t = skelIncl n x := by
  change (extendSkel (Y := C(I,Skel C (n+1))) n _ _ _ (skelIncl n x)) t = _
  rw [extendSkel_prior]
  rfl
@[simp] lemma paths_disk (n : ℕ) (i : RelCWComplex.cell C n) (v : Disk n) (t : I) :
    paths n (charSkel n i v) t = charSkel n i (DiskRadial.radial t v) := by
  change (extendSkel (Y := C(I,Skel C (n+1))) n _ _ _ (charSkel n i v)) t = _
  rw [extendSkel_disk]
  rfl

@[simp] lemma paths_zero (n : ℕ) (x : Skel C (n+1)) : paths n x 0 = x := by
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · exact paths_prior n a 0
  · change paths n (charSkel n i v) 0 = charSkel n i v
    rw [paths_disk,DiskRadial.radial_zero]

lemma paths_fixed (n : ℕ) (x : Skel C (n+1)) (hx : x ∈ lower n) (t : I) : paths n x t = x :=
  paths_prior (C := C) n ⟨x.1,hx⟩ t

lemma radius_le_paths (n : ℕ) (x : Skel C (n+1)) (t : I) : radius n x ≤ radius n (paths n x t) := by
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · change radius n (skelIncl n a) ≤ radius n (paths n (skelIncl n a) t)
    rw [paths_prior]
  · change radius n (charSkel n i v) ≤ radius n (paths n (charSkel n i v) t)
    rw [paths_disk,radius_disk,radius_disk]
    exact DiskRadial.norm_le_radial t v

lemma paths_mem_collar (n : ℕ) (x : Skel C (n+1)) (hx : x ∈ collar n) (t : I) : paths n x t ∈ collar n :=
  lt_of_lt_of_le hx (radius_le_paths n x t)

lemma paths_one_lower (n : ℕ) (x : Skel C (n+1)) (hx : x ∈ collar n) : paths n x 1 ∈ lower n := by
  apply (radius_eq_one_iff n _).mp
  obtain ⟨a,rfl⟩ := stageQuot_surjective n x
  rcases a with a | ⟨i,v⟩
  · change radius n (paths n (skelIncl n a) 1) = 1
    rw [paths_prior,radius_prior]
  · change radius n (paths n (charSkel n i v) 1) = 1
    simp only [paths_disk,radius_disk,DiskRadial.radial_one]
    apply DiskRadial.norm_inflate_of_half_lt
    change (1/2:ℝ) < radius n (charSkel n i v) at hx
    rwa [radius_disk] at hx

end

open Set Topology Metric CWExtension
open scoped unitInterval
universe u
variable {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma lower_closed (n : ℕ) : IsClosed (lower (C := C) n) := by
  have he : lower (C := C) n = radius (C := C) n ⁻¹' ({1} : Set ℝ) := by
    ext x
    exact (radius_eq_one_iff (C := C) n x).symm
  rw [he]
  exact isClosed_singleton.preimage (radius (C := C) n).continuous

def collarInclusion (n : ℕ) : C(lower (C := C) n,collar (C := C) n) :=
  ⟨Set.inclusion (lower_subset_collar (C := C) n),continuous_subtype_val.subtype_mk _⟩

def retract (n : ℕ) : C(collar (C := C) n,lower (C := C) n) :=
  ⟨fun x => ⟨paths (C := C) n x 1,paths_one_lower (C := C) n x x.2⟩,
    (((paths (C := C) n).continuous.comp continuous_subtype_val).eval continuous_const).subtype_mk _⟩

def collarHomotopy (n : ℕ) : ContinuousMap.Homotopy (ContinuousMap.id (collar (C := C) n))
    ((collarInclusion (C := C) n).comp (retract (C := C) n)) where
  toFun z := ⟨paths (C := C) n z.2 z.1,paths_mem_collar (C := C) n z.2 z.2.2 z.1⟩
  continuous_toFun := (((paths (C := C) n).continuous.comp (continuous_subtype_val.comp continuous_snd)).eval continuous_fst).subtype_mk _
  map_zero_left x := Subtype.ext (paths_zero (C := C) n x)
  map_one_left _ := rfl

def collarEquiv (n : ℕ) : ContinuousMap.HomotopyEquiv (lower (C := C) n) (collar (C := C) n) where
  toFun := collarInclusion (C := C) n
  invFun := retract (C := C) n
  left_inv := by
    have he : (retract (C := C) n).comp (collarInclusion (C := C) n) = ContinuousMap.id (lower (C := C) n) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (paths_fixed (C := C) n x x.2 1)
    rw [he]
  right_inv := ⟨(collarHomotopy (C := C) n).symm⟩

abbrev OpenDisk (n : ℕ) := ball (0 : Fin n → ℝ) 1
abbrev OpenCells (n : ℕ) := Σ _i : RelCWComplex.cell C n, OpenDisk n

def openDom (n : ℕ) (z : OpenCells (C := C) n) : Skel C n ⊕ (Σ _i : RelCWComplex.cell C n,Disk n) :=
  Sum.inr ⟨z.1,⟨z.2,ball_subset_closedBall z.2.2⟩⟩

lemma openDom_embedding (n : ℕ) : IsEmbedding (openDom (C := C) n) := by
  change IsEmbedding ((Sum.inr : (Σ _i : RelCWComplex.cell C n,Disk n) → Skel C n ⊕ (Σ _i : RelCWComplex.cell C n,Disk n)) ∘ Sigma.map (β₁ := fun _ : RelCWComplex.cell C n => OpenDisk n) (β₂ := fun _ : RelCWComplex.cell C n => Disk n) (id : RelCWComplex.cell C n → RelCWComplex.cell C n) (fun _ => Set.inclusion (ball_subset_closedBall : ball (0 : Fin n → ℝ) 1 ⊆ closedBall 0 1)))
  exact IsEmbedding.inr.comp ((isEmbedding_sigmaMap («σ» := fun _ : RelCWComplex.cell C n => OpenDisk n) («τ» := fun _ : RelCWComplex.cell C n => Disk n) (f₁ := (id : RelCWComplex.cell C n → RelCWComplex.cell C n)) (f₂ := fun _ => Set.inclusion (ball_subset_closedBall : ball (0 : Fin n → ℝ) 1 ⊆ closedBall 0 1)) Function.injective_id).mpr (fun _ => IsEmbedding.inclusion _))

lemma openDom_mem (n : ℕ) (z : OpenCells (C := C) n) : stageQuot (C := C) n (openDom (C := C) n z) ∈ (lower (C := C) n)ᶜ := by
  intro h
  have hb := boundary_of_mem_skel n z.1 ⟨z.2,ball_subset_closedBall z.2.2⟩ h
  have hlt : ‖(z.2 : Fin n → ℝ)‖ < 1 := by simpa only [mem_ball,dist_zero_right] using z.2.2
  have heq : ‖(z.2 : Fin n → ℝ)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hb
  exact (ne_of_lt hlt) heq

def openPreimage (n : ℕ) : OpenCells (C := C) n → ↑(stageQuot (C := C) n ⁻¹' (lower (C := C) n)ᶜ) :=
  fun z => ⟨openDom (C := C) n z,openDom_mem (C := C) n z⟩

lemma openPreimage_surjective (n : ℕ) : Function.Surjective (openPreimage (C := C) n) := by
  rintro ⟨a,ha⟩
  rcases a with x | ⟨i,v⟩
  · exact False.elim (ha x.2)
  · have hv : (v : Fin n → ℝ) ∉ sphere 0 1 := by
      intro hv
      exact ha (RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨v,hv,rfl⟩)
    have hv' : (v : Fin n → ℝ) ∈ ball 0 1 := lt_of_le_of_ne v.2 hv
    exact ⟨⟨i,⟨v,hv'⟩⟩,rfl⟩

def openPreimageEquiv (n : ℕ) : OpenCells (C := C) n ≃ₜ ↑(stageQuot (C := C) n ⁻¹' (lower (C := C) n)ᶜ) :=
  ((openDom_embedding (C := C) n).codRestrict _ (openDom_mem (C := C) n)).toHomeomorphOfSurjective (openPreimage_surjective (C := C) n)

def openCellMap (n : ℕ) : OpenCells (C := C) n → ↑((lower (C := C) n)ᶜ) :=
  fun z => ⟨stageQuot (C := C) n (openDom (C := C) n z),openDom_mem (C := C) n z⟩

lemma openCellMap_quotient (n : ℕ) : IsQuotientMap (openCellMap (C := C) n) :=
  ((stageQuot_isQuotientMap (C := C) n).restrictPreimage_isOpen (lower_closed (C := C) n).isOpen_compl).comp (openPreimageEquiv (C := C) n).isQuotientMap

lemma openCellMap_injective (n : ℕ) : Function.Injective (openCellMap (C := C) n) := by
  rintro ⟨i,v⟩ ⟨j,w⟩ he
  have h : RelCWComplex.map n i v = RelCWComplex.map n j w := congrArg (fun x => (x.1 : X)) he
  have hi : i = j := by
    by_contra hi
    exact (RelCWComplex.disjoint_openCell_of_ne (C := C) (by simp [hi] :
      (⟨n,i⟩ : Σ n,RelCWComplex.cell C n) ≠ ⟨n,j⟩)).notMem_of_mem_left ⟨v,v.2,rfl⟩ ⟨w,w.2,h.symm⟩
  subst j
  have hvw : v = w := Subtype.ext ((RelCWComplex.map n i).injOn
    (by simpa only [RelCWComplex.source_eq] using v.2)
    (by simpa only [RelCWComplex.source_eq] using w.2) h)
  subst w
  rfl

def openCellsEquiv (n : ℕ) : OpenCells (C := C) n ≃ₜ ↑((lower (C := C) n)ᶜ) :=
  (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨openCellMap_quotient (C := C) n,openCellMap_injective (C := C) n⟩).homeomorph _

@[simp] lemma openCellsEquiv_apply (n : ℕ) (z : OpenCells (C := C) n) :
    (openCellsEquiv n z).1 = charSkel n z.1 ⟨z.2,ball_subset_closedBall z.2.2⟩ := rfl

end CWCollar

end

end OAI
