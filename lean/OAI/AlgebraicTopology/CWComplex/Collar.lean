import OAI.AlgebraicTopology.CWComplex.Cover
import OAI.AlgebraicTopology.Cubical.PathChains
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.CWComplex.Classical.Graph

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology
open CWCover
universe u v
variable {X : Type u} [TopologicalSpace X] {J : Type v} {n : ℕ}

/-- Single-dimensional ordinary disk attachment. All fields will be derived
from the actual CW structure, not posited for the classifying-space theorem. -/
structure Attachment (X : Type u) [TopologicalSpace X] (J : Type v) (n : ℕ) where
  lower : Set X
  closed_lower : IsClosed lower
  chart : J → C(Disk n,X)
  boundary : ∀ j (z : Disk n), ‖z.val‖ = 1 → chart j z ∈ lower
  interior : ∀ j (z : Disk n), ‖z.val‖ < 1 → chart j z ∉ lower
  disjoint : ∀ j k (z w : Disk n), ‖z.val‖ < 1 → ‖w.val‖ < 1 →
    chart j z = chart k w → j = k ∧ z = w
  quotient : IsQuotientMap (Sum.elim (Subtype.val : lower → X)
    (fun p : Σ _ : J, Disk n => chart p.1 p.2))

namespace Attachment
variable (a : Attachment X J n)
abbrev Rep := a.lower ⊕ (Σ _ : J, Disk n)
def q : a.Rep → X := Sum.elim Subtype.val (fun p => a.chart p.1 p.2)
def coordinate : a.Rep → ℝ := Sum.elim (fun _ => 1) (fun p => ‖p.2.val‖)

@[simp] theorem disk_norm_le (z : Disk n) : ‖z.val‖ ≤ 1 := by
  simpa only [mem_closedBall,dist_zero_right] using z.property

theorem coordinate_eq_of_q_eq (p r : a.Rep) (h : a.q p = a.q r) :
    a.coordinate p = a.coordinate r := by
  cases p with
  | inl x =>
    cases r with
    | inl y => rfl
    | inr p =>
      change x.val = a.chart p.1 p.2 at h
      change (1:ℝ) = ‖p.2.val‖
      apply le_antisymm _ (disk_norm_le p.2)
      by_contra hn
      exact a.interior p.1 p.2 (lt_of_not_ge hn) (h ▸ x.property)
  | inr p =>
    cases r with
    | inl x =>
      change a.chart p.1 p.2 = x.val at h
      change ‖p.2.val‖ = 1
      apply le_antisymm (disk_norm_le p.2)
      by_contra hn
      exact a.interior p.1 p.2 (lt_of_not_ge hn) (h.symm ▸ x.property)
    | inr r =>
      change a.chart p.1 p.2 = a.chart r.1 r.2 at h
      change ‖p.2.val‖ = ‖r.2.val‖
      by_cases hp : ‖p.2.val‖ < 1
      · have hr : ‖r.2.val‖ < 1 := by
          by_contra hr
          have hr' : ‖r.2.val‖ = 1 := le_antisymm (disk_norm_le r.2) (le_of_not_gt hr)
          exact a.interior p.1 p.2 hp (h.symm ▸ a.boundary r.1 r.2 hr')
        exact congrArg (fun z : Disk n => ‖z.val‖) (a.disjoint p.1 r.1 p.2 r.2 hp hr h).2
      · have hp' : ‖p.2.val‖ = 1 := le_antisymm (disk_norm_le p.2) (le_of_not_gt hp)
        have hr : ¬ ‖r.2.val‖ < 1 := fun hr =>
          a.interior r.1 r.2 hr (h ▸ a.boundary p.1 p.2 hp')
        exact hp'.trans (le_antisymm (disk_norm_le r.2) (le_of_not_gt hr)).symm

def representative (x : X) : a.Rep := (a.quotient.surjective x).choose
@[simp] theorem q_representative (x : X) : a.q (a.representative x) = x :=
  (a.quotient.surjective x).choose_spec

def radius (x : X) : ℝ := a.coordinate (a.representative x)
@[simp] theorem radius_q (p : a.Rep) : a.radius (a.q p) = a.coordinate p :=
  a.coordinate_eq_of_q_eq _ _ (a.q_representative _)

theorem coordinate_continuous : Continuous a.coordinate := by
  apply Continuous.sumElim continuous_const
  exact continuous_sigma (fun _ => continuous_norm.comp continuous_subtype_val)

theorem radius_continuous : Continuous a.radius := by
  apply a.quotient.continuous_iff.mpr
  change Continuous (a.radius ∘ a.q)
  simpa only [Function.comp_def,a.radius_q] using a.coordinate_continuous

@[simp] theorem radius_lower (x : a.lower) : a.radius x.val = 1 := a.radius_q (.inl x)
@[simp] theorem radius_chart (j : J) (z : Disk n) : a.radius (a.chart j z) = ‖z.val‖ :=
  a.radius_q (.inr ⟨j,z⟩)

theorem radius_nonneg (x : X) : 0 ≤ a.radius x := by
  obtain ⟨p,rfl⟩ := a.quotient.surjective x
  change 0 ≤ a.radius (a.q p)
  rw [a.radius_q]
  cases p <;> simp [coordinate]

theorem radius_le_one (x : X) : a.radius x ≤ 1 := by
  obtain ⟨p,rfl⟩ := a.quotient.surjective x
  change a.radius (a.q p) ≤ 1
  rw [a.radius_q]
  cases p with
  | inl x => exact le_rfl
  | inr p => exact disk_norm_le p.2

theorem radius_eq_one_iff (x : X) : a.radius x = 1 ↔ x ∈ a.lower := by
  constructor
  · intro h
    obtain ⟨p,rfl⟩ := a.quotient.surjective x
    change a.radius (a.q p) = 1 at h
    rw [a.radius_q] at h
    cases p with
    | inl y => exact y.property
    | inr p => exact a.boundary p.1 p.2 h
  · intro h
    exact a.radius_lower ⟨x,h⟩

def outer : Set X := {x | 0 < a.radius x}
def inner : Set X := {x | a.radius x < 1}
theorem outer_open : IsOpen a.outer := isOpen_lt continuous_const a.radius_continuous
theorem inner_open : IsOpen a.inner := isOpen_lt a.radius_continuous continuous_const
theorem outer_union_inner : a.outer ∪ a.inner = univ := by
  ext x
  simp only [mem_union,mem_univ,iff_true]
  change 0 < a.radius x ∨ a.radius x < 1
  by_cases h : 0 < a.radius x
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem lower_subset_outer : a.lower ⊆ a.outer := by
  intro x hx
  change 0 < a.radius x
  rw [(a.radius_eq_one_iff x).mpr hx]
  norm_num

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CWComplex (univ : Set X)]

def lowerSkeleton (m : ℕ) : Set X := CWComplex.skeletonLT (univ : Set X) m

theorem characteristic_mem_lower {k m : ℕ} (hk : k < m) (i : Cell (X := X) k) (z : Disk k) :
    characteristic i z ∈ lowerSkeleton (X := X) m := by
  apply RelCWComplex.skeletonLT_mono (show (k:ℕ∞)+1 ≤ (m:ℕ∞) by exact_mod_cast Nat.succ_le_of_lt hk)
    (RelCWComplex.closedCell_subset_skeletonLT k i (show characteristic i z ∈ RelCWComplex.closedCell k i from ?_))
  exact ⟨z.val,z.property,rfl⟩

def topAttachmentQuotient (m : ℕ) :
    lowerSkeleton (X := X) m ⊕ (Σ _ : Cell (X := X) m, Disk m) → X :=
  Sum.elim Subtype.val (fun c => characteristic c.1 c.2)

theorem topAttachmentQuotient_continuous (m : ℕ) :
    Continuous (topAttachmentQuotient (X := X) m) :=
  continuous_subtype_val.sumElim (continuous_sigma (fun i => (characteristic i).continuous))

theorem topAttachmentQuotient_surjective (m : ℕ)
    (hd : ∀ k, m < k → IsEmpty (Cell (X := X) k)) :
    Function.Surjective (topAttachmentQuotient (X := X) m) := by
  intro x
  obtain ⟨⟨⟨k,i⟩,z⟩,rfl⟩ := characteristicSum_surjective (X := X) x
  by_cases hk : k < m
  · exact ⟨.inl ⟨characteristic i z,characteristic_mem_lower hk i z⟩,rfl⟩
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact ⟨.inr ⟨i,z⟩,rfl⟩

theorem topAttachmentQuotient_quotient (m : ℕ)
    (hd : ∀ k, m < k → IsEmpty (Cell (X := X) k)) :
    IsQuotientMap (topAttachmentQuotient (X := X) m) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨topAttachmentQuotient_surjective m hd,fun A =>
    ⟨fun h => h.preimage (topAttachmentQuotient_continuous m),?_⟩⟩
  intro hA
  apply characteristicSum_quotient.isClosed_preimage.mp
  rw [isClosed_sigma_iff]
  rintro ⟨k,i⟩
  by_cases hk : k < m
  · let f : Disk k → lowerSkeleton (X := X) m ⊕ (Σ _ : Cell (X := X) m, Disk m) :=
      fun z => .inl ⟨characteristic i z,characteristic_mem_lower hk i z⟩
    have hf : Continuous f := continuous_inl.comp ((characteristic i).continuous.subtype_mk (characteristic_mem_lower hk i))
    exact hA.preimage hf
  · have hkm : k = m := by
      by_contra h
      have := hd k (by omega)
      exact isEmptyElim i
    subst k
    exact hA.preimage (continuous_inr.comp (continuous_sigmaMk (i := i)))

/-- The abstract single-stage attachment is obtained from the given ordinary
CW complex itself, with no restriction on or enumeration of its cells. -/
def actualAttachment (m : ℕ) (hd : ∀ k, m < k → IsEmpty (Cell (X := X) k)) :
    Attachment X (Cell (X := X) m) m where
  lower := lowerSkeleton m
  closed_lower := (CWComplex.skeletonLT (univ : Set X) m).closed'
  chart := characteristic
  boundary := by
    intro i z hz
    exact RelCWComplex.cellFrontier_subset_skeletonLT m i
      ⟨z.val,by simpa only [mem_sphere,dist_zero_right] using hz,rfl⟩
  interior := by
    intro i z hz hl
    exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeletonLT_openCell le_rfl) hl
      ⟨z.val,by simpa only [mem_ball,dist_zero_right] using hz,rfl⟩
  disjoint := by
    intro i j z w hz hw he
    have hz' : z.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hz
    have hw' : w.val ∈ ball (0 : Fin m → ℝ) 1 := by simpa only [mem_ball,dist_zero_right] using hw
    by_cases hij : i = j
    · subst j
      refine ⟨rfl,Subtype.ext ((RelCWComplex.map m i).injOn ?_ ?_ he)⟩
      · simpa only [RelCWComplex.source_eq] using hz'
      · simpa only [RelCWComplex.source_eq] using hw'
    · exfalso
      exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne
        (show (⟨m,i⟩ : Σ k,Cell (X := X) k) ≠ ⟨m,j⟩ by simpa using hij))
        ⟨z.val,hz',rfl⟩ ⟨w.val,hw',he.symm⟩
  quotient := topAttachmentQuotient_quotient m hd

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
open scoped unitInterval
variable {n : ℕ}
abbrev PuncturedDisk (n : ℕ) := {z : Disk n // 0 < ‖z.val‖}
def radialScale (t : I) (z : PuncturedDisk n) : ℝ := (1-t.val) + t.val / ‖z.val.val‖

theorem radialScale_nonneg (t : I) (z : PuncturedDisk n) : 0 ≤ radialScale t z :=
  add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 (norm_nonneg _))

def radialCoords (t : I) (z : PuncturedDisk n) : Fin n → ℝ := radialScale t z • z.val.val

theorem radialCoords_norm (t : I) (z : PuncturedDisk n) :
    ‖radialCoords t z‖ = (1-t.val)*‖z.val.val‖ + t.val := by
  rw [radialCoords,norm_smul,Real.norm_eq_abs,abs_of_nonneg (radialScale_nonneg t z)]
  dsimp [radialScale]
  rw [add_mul,div_mul_cancel₀ _ (ne_of_gt z.property)]

theorem radialCoords_pos (t : I) (z : PuncturedDisk n) : 0 < ‖radialCoords t z‖ := by
  rw [radialCoords_norm]
  have hz := z.property
  have hb := Attachment.disk_norm_le z.val
  have ht := mul_nonneg t.property.1 (sub_nonneg.mpr hb)
  nlinarith

theorem radialCoords_le (t : I) (z : PuncturedDisk n) : ‖radialCoords t z‖ ≤ 1 := by
  rw [radialCoords_norm]
  have h := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (Attachment.disk_norm_le z.val))
  nlinarith

def radialDisk (t : I) (z : PuncturedDisk n) : PuncturedDisk n :=
  ⟨⟨radialCoords t z,by simpa only [mem_closedBall,dist_zero_right] using radialCoords_le t z⟩,
    radialCoords_pos t z⟩

@[simp] theorem radialDisk_zero (z : PuncturedDisk n) : radialDisk 0 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [radialDisk,radialCoords,radialScale]

@[simp] theorem radialDisk_norm_one (z : PuncturedDisk n) : ‖(radialDisk 1 z).val.val‖ = 1 := by
  change ‖radialCoords 1 z‖ = 1
  rw [radialCoords_norm]
  norm_num

theorem radialDisk_boundary (t : I) (z : PuncturedDisk n) (hz : ‖z.val.val‖ = 1) :
    radialDisk t z = z := by
  apply Subtype.ext
  apply Subtype.ext
  change ((1-t.val) + t.val / ‖z.val.val‖) • z.val.val = z.val.val
  rw [hz,div_one,sub_add_cancel,one_smul]

theorem radialDisk_continuous : Continuous (fun p : I × PuncturedDisk n => radialDisk p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun p : I × PuncturedDisk n =>
    ((1-p.1.val) + p.1.val / ‖p.2.val.val‖) • p.2.val.val)
  have hz : Continuous (fun p : I × PuncturedDisk n => p.2.val.val) := by fun_prop
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_fst).div (continuous_norm.comp hz)
      (fun p => ne_of_gt p.2.property))).smul hz

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
open scoped unitInterval
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}
namespace Attachment
variable (a : Attachment X J n)
abbrev OuterRep := a.lower ⊕ (Σ _ : J, PuncturedDisk n)

def outerIn : a.OuterRep → a.Rep := Sum.map id (Sigma.map id (fun _ z => z.val))
def outerQ : a.OuterRep → a.outer := fun p => ⟨a.q (a.outerIn p),by
  change 0 < a.radius (a.q (a.outerIn p))
  rw [a.radius_q]
  cases p with
  | inl x => exact (zero_lt_one : (0:ℝ) < 1)
  | inr p => exact p.2.property⟩

theorem outerIn_continuous : Continuous a.outerIn :=
  continuous_id.sumMap (continuous_sigma fun _ => continuous_sigmaMk.comp continuous_subtype_val)

theorem outerIn_openMap : IsOpenMap a.outerIn :=
  IsOpenMap.id.sumMap (isOpenMap_sigma.mpr (fun _ => isOpenMap_sigmaMk.comp
    ((isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).isOpenMap_subtype_val)))

theorem outerQ_continuous : Continuous a.outerQ :=
  (a.quotient.continuous.comp a.outerIn_continuous).subtype_mk _

theorem range_outerIn : Set.range a.outerIn = {p | 0 < a.coordinate p} := by
  ext p
  constructor
  · rintro ⟨p,rfl⟩
    cases p with
    | inl x => exact (zero_lt_one : (0:ℝ) < 1)
    | inr p => exact p.2.property
  · intro hp
    cases p with
    | inl x => exact ⟨.inl x,rfl⟩
    | inr p => exact ⟨.inr ⟨p.1,⟨p.2,hp⟩⟩,rfl⟩

theorem outerQ_surjective : Function.Surjective a.outerQ := by
  intro x
  obtain ⟨p,hp⟩ := a.quotient.surjective x.val
  change a.q p = x.val at hp
  have hr : 0 < a.coordinate p := by
    rw [← a.radius_q]
    rw [hp]
    exact x.property
  obtain ⟨r,rfl⟩ := (show p ∈ Set.range a.outerIn from by rw [a.range_outerIn]; exact hr)
  exact ⟨r,Subtype.ext hp⟩

theorem outerQ_quotient : IsQuotientMap a.outerQ := by
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen (fun A => ?_),a.outerQ_surjective⟩
  constructor
  · intro hA
    have he : a.outerIn '' (a.outerQ ⁻¹' A) = a.q ⁻¹' ((Subtype.val : a.outer → X) '' A) := by
      ext p
      constructor
      · rintro ⟨r,hr,rfl⟩
        exact ⟨a.outerQ r,hr,rfl⟩
      · rintro ⟨x,hx,hp⟩
        have hr : 0 < a.coordinate p := by
          rw [← a.radius_q,← hp]
          exact x.property
        obtain ⟨r,rfl⟩ := (show p ∈ Set.range a.outerIn from by rw [a.range_outerIn]; exact hr)
        refine ⟨r,?_,rfl⟩
        have hh : a.outerQ r = x := Subtype.ext hp.symm
        change a.outerQ r ∈ A
        rw [hh]
        exact hx
    have ho : IsOpen ((Subtype.val : a.outer → X) '' A) :=
      a.quotient.isOpen_preimage.mp (he ▸ a.outerIn_openMap _ hA)
    have := ho.preimage (continuous_subtype_val (p := fun x => x ∈ a.outer))
    simpa only [Set.preimage_image_eq _ Subtype.val_injective] using this
  · intro hA
    exact hA.preimage a.outerQ_continuous

end Attachment

private theorem continuous_sum_prod {A B C T : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace T] {f : (A ⊕ B) × T → C}
    (hA : Continuous (fun p : A × T => f (.inl p.1,p.2)))
    (hB : Continuous (fun p : B × T => f (.inr p.1,p.2))) : Continuous f := by
  have h : Continuous (f ∘ (Homeomorph.sumProdDistrib : (A ⊕ B) × T ≃ₜ (A × T) ⊕ (B × T)).symm) :=
    continuous_sum_dom.mpr ⟨hA,hB⟩
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using h.comp (Homeomorph.sumProdDistrib).continuous

private theorem continuous_sigma_prod {A : Type*} {B : A → Type*} {C T : Type*}
    [∀ a,TopologicalSpace (B a)] [TopologicalSpace C] [TopologicalSpace T]
    {f : (Sigma B) × T → C}
    (h : ∀ a, Continuous (fun p : B a × T => f (⟨a,p.1⟩,p.2))) : Continuous f := by
  have hh : Continuous (f ∘ (Homeomorph.sigmaProdDistrib : (Sigma B) × T ≃ₜ Σ a,B a × T).symm) :=
    continuous_sigma h
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hh.comp (Homeomorph.sigmaProdDistrib).continuous

namespace Attachment
variable (a : Attachment X J n)
def repFlow : a.OuterRep × I → a.OuterRep := fun p =>
  match p.1 with
  | .inl x => .inl x
  | .inr c => .inr ⟨c.1,radialDisk p.2 c.2⟩

theorem repFlow_continuous : Continuous a.repFlow := by
  apply continuous_sum_prod
  · exact continuous_inl.comp continuous_fst
  · apply continuous_sigma_prod
    intro j
    exact continuous_inr.comp (continuous_sigmaMk.comp (radialDisk_continuous.comp continuous_swap))

@[simp] theorem repFlow_zero (p : a.OuterRep) : a.repFlow (p,0) = p := by
  cases p with
  | inl x => rfl
  | inr c => simp [repFlow]

theorem outerQ_repFlow_one (p : a.OuterRep) : (a.outerQ (a.repFlow (p,1))).val ∈ a.lower := by
  cases p with
  | inl x => exact x.property
  | inr c => exact a.boundary c.1 (radialDisk 1 c.2).val (radialDisk_norm_one c.2)

theorem repFlow_respects (t : I) {p r : a.OuterRep} (h : a.outerQ p = a.outerQ r) :
    a.outerQ (a.repFlow (p,t)) = a.outerQ (a.repFlow (r,t)) := by
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  cases p with
  | inl x =>
    cases r with
    | inl y => exact h'
    | inr c =>
      change x.val = a.chart c.1 c.2.val at h'
      have hc : ‖c.2.val.val‖ = 1 := by
        rw [← a.radius_chart,← h',a.radius_lower]
      change x.val = a.chart c.1 (radialDisk t c.2).val
      rw [radialDisk_boundary t c.2 hc]
      exact h'
  | inr c =>
    cases r with
    | inl x =>
      change a.chart c.1 c.2.val = x.val at h'
      have hc : ‖c.2.val.val‖ = 1 := by
        rw [← a.radius_chart,h',a.radius_lower]
      change a.chart c.1 (radialDisk t c.2).val = x.val
      rw [radialDisk_boundary t c.2 hc]
      exact h'
    | inr d =>
      change a.chart c.1 c.2.val = a.chart d.1 d.2.val at h'
      by_cases hc : ‖c.2.val.val‖ < 1
      · have hd : ‖d.2.val.val‖ < 1 := by
          rw [← a.radius_chart,← h',a.radius_chart]
          exact hc
        obtain ⟨hj,hz⟩ := a.disjoint c.1 d.1 c.2.val d.2.val hc hd h'
        have he : c = d := by
          cases c with
          | mk j z =>
            cases d with
            | mk k w =>
              dsimp at hj hz
              subst k
              have hw : z = w := Subtype.ext hz
              subst w
              rfl
        subst d
        rfl
      · have hc' : ‖c.2.val.val‖ = 1 := le_antisymm (disk_norm_le c.2.val) (le_of_not_gt hc)
        have hd : ‖d.2.val.val‖ = 1 := by rw [← a.radius_chart,← h',a.radius_chart,hc']
        change a.chart c.1 (radialDisk t c.2).val = a.chart d.1 (radialDisk t d.2).val
        rw [radialDisk_boundary t c.2 hc',radialDisk_boundary t d.2 hd]
        exact h'

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar.Attachment
open Classical Set Metric Topology
open scoped unitInterval
variable {X J : Type*} [TopologicalSpace X] {n : ℕ} (a : Attachment X J n)

def outerRepresentative (x : a.outer) : a.OuterRep := (a.outerQ_surjective x).choose
@[simp] theorem outerQ_representative (x : a.outer) : a.outerQ (a.outerRepresentative x) = x :=
  (a.outerQ_surjective x).choose_spec

def flow (p : a.outer × I) : a.outer := a.outerQ (a.repFlow (a.outerRepresentative p.1,p.2))
@[simp] theorem flow_q (p : a.OuterRep) (t : I) : a.flow (a.outerQ p,t) = a.outerQ (a.repFlow (p,t)) :=
  a.repFlow_respects t (a.outerQ_representative (a.outerQ p))

theorem flow_continuous : Continuous a.flow := by
  apply a.outerQ_quotient.continuous_lift_prod_left
  have h := a.outerQ_continuous.comp a.repFlow_continuous
  simpa only [Function.comp_def,a.flow_q] using h

@[simp] theorem flow_zero (x : a.outer) : a.flow (x,0) = x := by
  change a.outerQ (a.repFlow (a.outerRepresentative x,0)) = x
  rw [a.repFlow_zero,a.outerQ_representative]

theorem flow_one_lower (x : a.outer) : (a.flow (x,1)).val ∈ a.lower :=
  a.outerQ_repFlow_one (a.outerRepresentative x)

def sectionMap : C(a.lower,a.outer) :=
  ⟨fun x => ⟨x.val,a.lower_subset_outer x.property⟩,continuous_subtype_val.subtype_mk _⟩

def retractMap : C(a.outer,a.lower) :=
  ⟨fun x => ⟨(a.flow (x,1)).val,a.flow_one_lower x⟩,
    (continuous_subtype_val.comp (a.flow_continuous.comp (continuous_id.prodMk continuous_const))).subtype_mk _⟩

@[simp] theorem flow_section (x : a.lower) (t : I) : a.flow (a.sectionMap x,t) = a.sectionMap x := by
  change a.flow (a.outerQ (.inl x),t) = a.outerQ (.inl x)
  rw [a.flow_q]
  rfl

@[simp] theorem retract_section (x : a.lower) : a.retractMap (a.sectionMap x) = x := by
  apply Subtype.ext
  change (a.flow (a.sectionMap x,1)).val = x.val
  exact congrArg Subtype.val (a.flow_section x 1)

/-- The radial collar is a genuine strong deformation neighborhood of the
lower-dimensional CW skeleton. -/
def collarHomotopy : (ContinuousMap.id a.outer).Homotopy (a.sectionMap.comp a.retractMap) where
  toFun p := a.flow (p.2,p.1)
  continuous_toFun := a.flow_continuous.comp continuous_swap
  map_zero_left := a.flow_zero
  map_one_left _ := rfl

end EilenbergGanea.CWCollar.Attachment

namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}
abbrev OpenDisk (n : ℕ) := {z : Disk n // ‖z.val‖ < 1}
namespace Attachment
variable (a : Attachment X J n)

theorem q_injective_interior {p r : a.Rep} (hp : a.coordinate p < 1) (h : a.q p = a.q r) : p = r := by
  have hr : a.coordinate r < 1 := (a.coordinate_eq_of_q_eq p r h) ▸ hp
  cases p with
  | inl x => exact (lt_irrefl (1:ℝ) hp).elim
  | inr p =>
    cases r with
    | inl x => exact (lt_irrefl (1:ℝ) hr).elim
    | inr r =>
      obtain ⟨hj,hz⟩ := a.disjoint p.1 r.1 p.2 r.2 hp hr h
      congr 1
      exact Sigma.ext hj (heq_of_eq hz)

def innerIn : (Σ _ : J, OpenDisk n) → a.Rep := fun p => .inr ⟨p.1,p.2.val⟩
def innerQ : (Σ _ : J, OpenDisk n) → a.inner := fun p => ⟨a.q (a.innerIn p),by
  change a.radius (a.chart p.1 p.2.val) < 1
  rw [a.radius_chart]
  exact p.2.property⟩

theorem innerIn_continuous : Continuous a.innerIn :=
  continuous_inr.comp (continuous_sigma fun _ => continuous_sigmaMk.comp continuous_subtype_val)

theorem innerIn_openMap : IsOpenMap a.innerIn :=
  isOpenMap_inr.comp (isOpenMap_sigma.mpr (fun _ => isOpenMap_sigmaMk.comp
    ((isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const).isOpenMap_subtype_val)))

theorem innerQ_continuous : Continuous a.innerQ :=
  (a.quotient.continuous.comp a.innerIn_continuous).subtype_mk _

theorem innerQ_injective : Function.Injective a.innerQ := by
  intro p r h
  have he := a.q_injective_interior (p := a.innerIn p) (r := a.innerIn r) p.2.property (congrArg Subtype.val h)
  have hh : (⟨p.1,p.2.val⟩ : Σ _ : J, Disk n) = ⟨r.1,r.2.val⟩ := Sum.inr_injective he
  cases p with
  | mk j z =>
    cases r with
    | mk k w =>
      have hj : j = k := congrArg Sigma.fst hh
      subst k
      have hz : z.val = w.val := by simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hh
      have hz' : z = w := Subtype.ext hz
      subst w
      rfl

theorem innerQ_surjective : Function.Surjective a.innerQ := by
  intro x
  obtain ⟨p,hp⟩ := a.quotient.surjective x.val
  change a.q p = x.val at hp
  have hr : a.coordinate p < 1 := by rw [← a.radius_q,hp]; exact x.property
  cases p with
  | inl y => exact (lt_irrefl (1:ℝ) hr).elim
  | inr p => exact ⟨⟨p.1,⟨p.2,hr⟩⟩,Subtype.ext hp⟩

theorem innerQ_openMap : IsOpenMap a.innerQ := by
  have h : IsOpenMap (a.q ∘ a.innerIn) := by
    intro W hW
    apply a.quotient.isOpen_preimage.mp
    have he : a.q ⁻¹' ((a.q ∘ a.innerIn) '' W) = a.innerIn '' W := by
      ext p
      constructor
      · rintro ⟨r,hr,he⟩
        exact ⟨r,hr,a.q_injective_interior (p := a.innerIn r) r.2.property he⟩
      · rintro ⟨r,hr,rfl⟩
        exact ⟨r,hr,rfl⟩
    change IsOpen (a.q ⁻¹' ((a.q ∘ a.innerIn) '' W))
    rw [he]
    exact a.innerIn_openMap W hW
  exact h.subtype_mk _

/-- Actual pairwise-disjoint open top-dimensional cells, including arbitrary
index universes, with their ordinary disk interiors. -/
def innerHomeomorph : (Σ _ : J, OpenDisk n) ≃ₜ a.inner :=
  (Equiv.ofBijective a.innerQ ⟨a.innerQ_injective,a.innerQ_surjective⟩).toHomeomorphOfContinuousOpen
    a.innerQ_continuous a.innerQ_openMap

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover
variable {X J : Type*} [TopologicalSpace X] {n : ℕ}
abbrev Annulus (n : ℕ) := {z : OpenDisk n // 0 < ‖z.val.val‖}

def annulusSigmaIn : (Σ _ : J, Annulus n) → (Σ _ : J, OpenDisk n) :=
  fun p => ⟨p.1,p.2.val⟩

theorem annulusSigmaIn_continuous : Continuous (annulusSigmaIn (J:=J) (n:=n)) :=
  continuous_sigma (fun _ => continuous_sigmaMk.comp continuous_subtype_val)

theorem annulusSigmaIn_openMap : IsOpenMap (annulusSigmaIn (J:=J) (n:=n)) :=
  isOpenMap_sigma.mpr (fun _ => isOpenMap_sigmaMk.comp
    ((isOpen_lt continuous_const (continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val))).isOpenMap_subtype_val))

def annulusSigmaHomeomorph : (Σ _ : J, Annulus n) ≃ₜ
    {p : (Σ _ : J, OpenDisk n) // 0 < ‖p.2.val.val‖} :=
  (show (Σ _ : J, Annulus n) ≃ {p : (Σ _ : J, OpenDisk n) // 0 < ‖p.2.val.val‖} from
    { toFun := fun p => ⟨annulusSigmaIn p,p.2.property⟩
      invFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).toHomeomorphOfContinuousOpen
    (annulusSigmaIn_continuous.subtype_mk _) (annulusSigmaIn_openMap.subtype_mk _)

namespace Attachment
variable (a : Attachment X J n)

def innerOuterHomeomorph : {x : a.inner // x.val ∈ a.outer} ≃ₜ (a.outer ∩ a.inner : Set X) where
  toFun x := ⟨x.val.val,x.property,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2⟩,x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual overlap of the two CW collar open sets is the disjoint union of
punctured open disks, even for an unrestricted cell index. -/
def annulusHomeomorph : (Σ _ : J, Annulus n) ≃ₜ (a.outer ∩ a.inner : Set X) :=
  annulusSigmaHomeomorph.trans ((a.innerHomeomorph.subtype (p := fun p => 0 < ‖p.2.val.val‖)
    (q := fun x => x.val ∈ a.outer) (by
      intro p
      change (0 < ‖p.2.val.val‖) ↔ (0 < a.radius (a.chart p.1 p.2.val))
      rw [a.radius_chart])).trans a.innerOuterHomeomorph)

end Attachment
end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover

def openDiskBallHomeomorph (n : ℕ) : OpenDisk n ≃ₜ ball (0 : Fin n → ℝ) 1 where
  toFun z := ⟨z.val.val,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  invFun z := ⟨⟨z.val,ball_subset_closedBall z.property⟩,by simpa only [mem_ball,dist_zero_right] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def spaceOpenDiskHomeomorph (n : ℕ) : (Fin n → ℝ) ≃ₜ OpenDisk n :=
  Homeomorph.unitBall.trans (openDiskBallHomeomorph n).symm

@[simp] theorem spaceOpenDiskHomeomorph_zero (n : ℕ) :
    (spaceOpenDiskHomeomorph n 0).val.val = 0 := Homeomorph.coe_unitBall_apply_zero

def puncturedAnnulusHomeomorph (n : ℕ) : ({0}ᶜ : Set (Fin n → ℝ)) ≃ₜ Annulus n :=
  (spaceOpenDiskHomeomorph n).subtype (p := fun x => x ∈ ({0}ᶜ : Set (Fin n → ℝ)))
    (q := fun z => 0 < ‖z.val.val‖) (by
      intro x
      simp only [mem_compl_iff,mem_singleton_iff,norm_pos_iff]
      have he : (spaceOpenDiskHomeomorph n x).val.val = 0 ↔ x = 0 := by
        constructor
        · intro h
          apply (spaceOpenDiskHomeomorph n).injective
          apply Subtype.ext
          apply Subtype.ext
          simpa only [spaceOpenDiskHomeomorph_zero] using h
        · rintro rfl; exact spaceOpenDiskHomeomorph_zero n
      exact not_congr he.symm)

instance annulusTwoPathConnected : PathConnectedSpace (Annulus 2) := by
  have hr : 1 < Module.rank ℝ (Fin 2 → ℝ) := by simp
  let : PathConnectedSpace ({0}ᶜ : Set (Fin 2 → ℝ)) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank hr 0)
  exact (puncturedAnnulusHomeomorph 2).surjective.pathConnectedSpace (puncturedAnnulusHomeomorph 2).continuous

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover CategoryTheory
open scoped ContinuousMap

def planeComplexHomeomorph : (Fin 2 → ℝ) ≃ₜ ℂ :=
  (Homeomorph.piFinTwo (fun _ => ℝ)).trans Complex.equivRealProdCLM.symm.toHomeomorph

@[simp] theorem planeComplexHomeomorph_zero : planeComplexHomeomorph 0 = 0 := by
  simp [planeComplexHomeomorph,Homeomorph.piFinTwo]

def puncturedPlaneComplexHomeomorph : ({0}ᶜ : Set (Fin 2 → ℝ)) ≃ₜ ({0}ᶜ : Set ℂ) :=
  planeComplexHomeomorph.subtype (p := fun x => x ∈ ({0}ᶜ : Set (Fin 2 → ℝ)))
    (q := fun z => z ∈ ({0}ᶜ : Set ℂ)) (by
      intro x
      simp only [mem_compl_iff,mem_singleton_iff]
      constructor
      · intro hx he
        apply hx
        apply planeComplexHomeomorph.injective
        simpa only [planeComplexHomeomorph_zero] using he
      · intro hx he
        apply hx
        rw [he,planeComplexHomeomorph_zero])

def circleSphereHomeomorph : sphere (0 : ℂ) 1 ≃ₜ Circle :=
  Homeomorph.setCongr rfl

def annulusCircleProdHomeomorph : Annulus 2 ≃ₜ Circle × Ioi (0 : ℝ) :=
  (puncturedAnnulusHomeomorph 2).symm.trans (puncturedPlaneComplexHomeomorph.trans
    ((homeomorphUnitSphereProd ℂ).trans (circleSphereHomeomorph.prodCongr (Homeomorph.refl _))))

instance positiveRealsContractible : ContractibleSpace (Ioi (0 : ℝ)) :=
  (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1,by norm_num⟩

noncomputable def annulusCircleEquiv : Annulus 2 ≃ₕ Circle :=
  annulusCircleProdHomeomorph.toHomotopyEquiv.trans
    (((ContinuousMap.HomotopyEquiv.refl Circle).prodCongr (ContractibleSpace.hequiv_unit (Ioi (0:ℝ))).some).trans
      (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv)

noncomputable def homotopyFundamentalEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x)
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.homEquiv.bijective

noncomputable def periodIntEquiv : ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) := by
  let f : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) :=
    { toFun := fun n => ⟨n • (2 * Real.pi),AddSubgroup.zsmul_mem_zmultiples _ _⟩
      map_zero' := Subtype.ext (zero_zsmul _)
      map_add' := fun m n => Subtype.ext (add_zsmul _ _ _) }
  apply AddEquiv.ofBijective f
  constructor
  · intro m n h
    have he := congrArg Subtype.val h
    change m • (2*Real.pi) = n • (2*Real.pi) at he
    simp only [zsmul_eq_mul] at he
    exact_mod_cast mul_right_cancel₀ (show 2*Real.pi ≠ 0 by positivity) he
  · intro x
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp x.property
    exact ⟨n,Subtype.ext hn⟩

noncomputable def circleFundamentalInt : FundamentalGroup Circle 1 ≃* Multiplicative ℤ := by
  let : ContractibleSpace ℝ := inferInstance
  exact (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv (⟨0,by simp⟩ : Circle.exp ⁻¹' {1})).trans
    ((MulEquiv.inv' (Multiplicative (AddSubgroup.zmultiples (2*Real.pi)))).symm.trans
      periodIntEquiv.symm.toMultiplicative)

noncomputable def annulusFundamentalInt (x : Annulus 2) : FundamentalGroup (Annulus 2) x ≃* Multiplicative ℤ :=
  (homotopyFundamentalEquiv annulusCircleEquiv x).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (annulusCircleEquiv x) 1).trans circleFundamentalInt)

end EilenbergGanea.CWCollar

namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport

noncomputable def annulusOppositeInt (x : Annulus 2) : (FundamentalGroup (Annulus 2) x)ᵐᵒᵖ ≃* Multiplicative ℤ :=
  (annulusFundamentalInt x).op.trans (MulEquiv.inv' (Multiplicative ℤ)).symm

noncomputable def annulusAbInt (x : Annulus 2) : AbLoops (Annulus 2) x ≃ₗ[ℤ] ℤ :=
  (((annulusOppositeInt x).abelianizationCongr.trans (Abelianization.equivOfComm (H:=Multiplicative ℤ)).symm).toAdditive).toIntLinearEquiv

noncomputable def annulusHomologyInt (x : Annulus 2) : HomologyOne (Annulus 2) ≃ₗ[ℤ] ℤ :=
  (hurewiczOne (fun y => (PathConnectedSpace.joined x y).somePath)).trans (annulusAbInt x)

noncomputable def annulusGenerator (x : Annulus 2) : Path x x :=
  Quotient.out ((annulusOppositeInt x).symm (Multiplicative.ofAdd 1)).unop

theorem annulusGenerator_class (x : Annulus 2) :
    annulusOppositeInt x (MulOpposite.op (asClass (annulusGenerator x))) = Multiplicative.ofAdd 1 := by
  have he : asClass (annulusGenerator x) = ((annulusOppositeInt x).symm (Multiplicative.ofAdd 1)).unop := Quotient.out_eq _
  rw [he,MulOpposite.op_unop,MulEquiv.apply_symm_apply]

theorem annulus_loop_power (x : Annulus 2) (p : Path x x) :
    ∃ n : ℤ, MulOpposite.op (asClass p) = (MulOpposite.op (asClass (annulusGenerator x)) : (FundamentalGroup (Annulus 2) x)ᵐᵒᵖ) ^ n := by
  refine ⟨(annulusOppositeInt x (MulOpposite.op (asClass p))).toAdd,?_⟩
  apply (annulusOppositeInt x).injective
  rw [map_zpow,annulusGenerator_class]
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow]
  change _ = _ • (1 : ℤ)
  simp

def loopCycle {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) : cyclesOn (Set.univ : Set X) :=
  ⟨gen₁ p.toContinuousMap,by rw [L₁_univ]; trivial,by
    change d₁ (gen₁ p.toContinuousMap) = 0
    simp only [gen₁,d₁_mk,b₁_single,one_smul]
    change Finsupp.single (p 1) (1:ℤ) - Finsupp.single (p 0) (1:ℤ) = 0
    rw [p.target,p.source,sub_self]⟩

def loopHomology {X : Type*} [TopologicalSpace X] {x : X} (p : Path x x) : HomologyOne X :=
  (boundaries Set.univ).mkQ (loopCycle p)

theorem hurewiczOne_loop {X : Type*} [TopologicalSpace X] {r x : X}
    (q : ∀ y, Path r y) (p : Path x x) :
    hurewiczOne q (loopHomology p) = Additive.ofMul (Abelianization.of (basedPath q p)) := by
  change abHolonomyMap q (gen₁ p.toContinuousMap) = _
  rw [abHolonomyMap_gen]
  simp only [abHolonomy,holonomy_path]

theorem annulusGenerator_homology (x : Annulus 2) :
    loopHomology (annulusGenerator x) = (annulusHomologyInt x).symm 1 := by
  apply (annulusHomologyInt x).injective
  rw [LinearEquiv.apply_symm_apply]
  change annulusAbInt x (hurewiczOne _ (loopHomology _)) = 1
  rw [hurewiczOne_loop]
  have he (w : (FundamentalGroup (Annulus 2) x)ᵐᵒᵖ) :
      annulusAbInt x (Additive.ofMul (Abelianization.of w)) = (annulusOppositeInt x w).toAdd := by
    rfl
  rw [he]
  have hb := ab_based_loop (fun y => (PathConnectedSpace.joined x y).somePath) (asClass (annulusGenerator x))
  have hh := congrArg (fun z => annulusAbInt x (Additive.ofMul z)) hb
  rw [he,he] at hh
  change (annulusOppositeInt x (based _ (asClass (annulusGenerator x)))).toAdd = 1
  rw [hh,annulusGenerator_class]
  rfl

end EilenbergGanea.CWCollar


end

end OAI
