import Mathlib.Tactic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

noncomputable section

open Classical Set Topology

open Classical Set Topology
namespace EilenbergGanea.DescendingCube
variable {G A : Type*} [Group G]

/-- Finite descending directions with literal word-length decrease. These
combinatorial fields will be supplied by the checked Artin trace normal form. -/
structure Data (f : A → G) where
  length : G → ℕ
  desc : G → Finset A
  decrease : ∀ g a, a ∈ desc g → length (g * f a) + 1 = length g
  preserve : ∀ g a b, a ∈ desc g → b ∈ desc g → a ≠ b → b ∈ desc (g * f a)
  commute : ∀ g a b, a ∈ desc g → b ∈ desc g → a ≠ b → Commute (f a) (f b)
  nonempty : ∀ g, 0 < length g → (desc g).Nonempty
  zero : ∀ g, length g = 0 ↔ g = 1

namespace Data
variable {f : A → G} (D : Data f)
def product (g : G) (s : Finset A) (hs : s ⊆ D.desc g) : G :=
  s.noncommProd f (fun a ha b hb hne => D.commute g a b (hs ha) (hs hb) hne)

@[simp] theorem product_empty (g : G) : D.product g ∅ (by simp) = 1 :=
  Finset.noncommProd_empty _ _

theorem product_insert (g : G) (s : Finset A) (a : A) (ha : a ∉ s)
    (hs : insert a s ⊆ D.desc g) :
    D.product g (insert a s) hs = f a * D.product g s (fun _ hb => hs (Finset.mem_insert_of_mem hb)) := by
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

/-- Simultaneous finite descent and preservation of all untouched directions. -/
theorem product_descent (g : G) (s : Finset A) (hs : s ⊆ D.desc g) :
    D.length (g * D.product g s hs) + s.card = D.length g ∧
    ∀ a ∈ D.desc g, a ∉ s → a ∈ D.desc (g * D.product g s hs) := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | @insert a s ha ih =>
      have hga : a ∈ D.desc g := hs (Finset.mem_insert_self _ _)
      have hs' : s ⊆ D.desc (g * f a) := by
        intro b hb
        exact D.preserve g a b hga (hs (Finset.mem_insert_of_mem hb))
          (fun he => ha (he ▸ hb))
      have hh := ih (g * f a) hs'
      have he : D.product (g * f a) s hs' =
          D.product g s (fun _ hb => hs (Finset.mem_insert_of_mem hb)) := rfl
      rw [he] at hh
      rw [product_insert _ _ _ _ ha,← mul_assoc]
      constructor
      · have hd := D.decrease g a hga
        rw [Finset.card_insert_of_notMem ha]
        omega
      · intro b hb hbs
        exact hh.2 b (D.preserve g a b hga hb (by
          intro he; exact hbs (he ▸ Finset.mem_insert_self a s)))
          (fun hb' => hbs (Finset.mem_insert_of_mem hb'))

structure Cell where
  top : G
  directions : Finset A
  subset : directions ⊆ D.desc top

@[ext] structure Point where
  top : G
  coord : A → ℝ
  nonneg : ∀ a, 0 ≤ coord a
  lt_one : ∀ a, coord a < 1
  support : ∀ a, coord a ≠ 0 → a ∈ D.desc top

abbrev Coordinates (c : D.Cell) := c.directions → Set.Icc (0 : ℝ) 1

def ones (c : D.Cell) (x : D.Coordinates c) : Finset A :=
  c.directions.attach.filter (fun a => (x a : ℝ) = 1) |>.image Subtype.val

@[simp] theorem mem_ones (c : D.Cell) (x : D.Coordinates c) (a : A) :
    a ∈ D.ones c x ↔ ∃ h : a ∈ c.directions, (x ⟨a,h⟩ : ℝ) = 1 := by simp [ones]

theorem ones_subset (c : D.Cell) (x : D.Coordinates c) : D.ones c x ⊆ c.directions := by
  intro a ha
  exact ((D.mem_ones c x a).mp ha).1

def normalizedCoord (c : D.Cell) (x : D.Coordinates c) (a : A) : ℝ :=
  if h : a ∈ c.directions then if (x ⟨a,h⟩ : ℝ) = 1 then 0 else x ⟨a,h⟩ else 0

/-- Crossing a far face removes a descent and strictly lowers the top vertex. -/
def characteristic (c : D.Cell) (x : D.Coordinates c) : D.Point where
  top := c.top * D.product c.top (D.ones c x) ((D.ones_subset c x).trans c.subset)
  coord := D.normalizedCoord c x
  nonneg a := by
    by_cases h : a ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs
      · exact le_rfl
      · exact (x ⟨a,h⟩).property.1
    · simp [normalizedCoord,h]
  lt_one a := by
    by_cases h : a ∈ c.directions
    · simp only [normalizedCoord,dite_eq_left h]
      split_ifs with he
      · norm_num
      · exact lt_of_le_of_ne (x ⟨a,h⟩).property.2 he
    · simp [normalizedCoord,h]
  support a ha := by
    have h : a ∈ c.directions := by
      by_contra hn
      exact ha (by simp [normalizedCoord,hn])
    have hne : (x ⟨a,h⟩ : ℝ) ≠ 1 := by
      intro he
      exact ha (by simp [normalizedCoord,h,he])
    exact (D.product_descent c.top (D.ones c x) _).2 a (c.subset h) (by
      intro hm
      obtain ⟨_,he⟩ := (D.mem_ones c x a).mp hm
      exact hne he)

variable [Fintype A]

def active (p : D.Point) : Finset A := Finset.univ.filter (fun a => p.coord a ≠ 0)

@[simp] theorem mem_active (p : D.Point) (a : A) : a ∈ D.active p ↔ p.coord a ≠ 0 := by
  simp [active]

def pointCell (p : D.Point) : D.Cell :=
  ⟨p.top,D.active p,fun a ha => p.support a ((D.mem_active p a).mp ha)⟩

def pointCoordinates (p : D.Point) : D.Coordinates (D.pointCell p) :=
  fun a => ⟨p.coord a,p.nonneg a,(p.lt_one a).le⟩

@[simp] theorem ones_pointCoordinates (p : D.Point) :
    D.ones (D.pointCell p) (D.pointCoordinates p) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨h,hh⟩ := (D.mem_ones _ _ _).mp ha
  exact (p.lt_one a).ne hh

@[simp] theorem characteristic_point (p : D.Point) :
    D.characteristic (D.pointCell p) (D.pointCoordinates p) = p := by
  apply Point.ext
  · change p.top * D.product p.top (D.ones (D.pointCell p) (D.pointCoordinates p)) _ = p.top
    simp only [product,ones_pointCoordinates,Finset.noncommProd_empty,mul_one]
  · funext a
    by_cases h : p.coord a = 0
    · simp [characteristic,normalizedCoord,pointCell,h]
    · simp [characteristic,normalizedCoord,pointCell,h,pointCoordinates,(p.lt_one a).ne]

abbrev CubeSum := (c : D.Cell) × D.Coordinates c

def evaluation : D.CubeSum → D.Point := fun z => D.characteristic z.1 z.2

theorem evaluation_surjective : Function.Surjective D.evaluation := by
  intro p
  exact ⟨⟨D.pointCell p,D.pointCoordinates p⟩,D.characteristic_point p⟩

instance pointTopology : TopologicalSpace D.Point :=
  TopologicalSpace.coinduced D.evaluation inferInstance

theorem evaluation_quotient : IsQuotientMap D.evaluation := ⟨⟨rfl⟩,D.evaluation_surjective⟩

theorem characteristic_continuous (c : D.Cell) : Continuous (D.characteristic c) :=
  D.evaluation_quotient.continuous.comp (continuous_sigmaMk (i := c))

omit [Fintype A] in
theorem characteristic_length (c : D.Cell) (x : D.Coordinates c) :
    D.length (D.characteristic c x).top + (D.ones c x).card = D.length c.top :=
  (D.product_descent c.top (D.ones c x) _).1

end Data
end EilenbergGanea.DescendingCube

namespace EilenbergGanea.DescendingCube.Data

section
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
def fullCell (g : G) : D.Cell := ⟨g,D.desc g,fun _ => id⟩

def fullCoord (c : D.Cell) (x : D.Coordinates c) (a : A) : ℝ :=
  if h : a ∈ c.directions then x ⟨a,h⟩ else 0

@[simp] theorem fullCoord_mem (c : D.Cell) (x : D.Coordinates c) (a : c.directions) :
    D.fullCoord c x a = (x a : ℝ) := by simp [fullCoord,a.property]

theorem fullCoord_nonneg (c : D.Cell) (x : D.Coordinates c) (a : A) :
    0 ≤ D.fullCoord c x a := by
  unfold fullCoord
  split
  · exact (x _).property.1
  · exact le_rfl

theorem fullCoord_le_one (c : D.Cell) (x : D.Coordinates c) (a : A) :
    D.fullCoord c x a ≤ 1 := by
  unfold fullCoord
  split
  · exact (x _).property.2
  · norm_num

theorem fullCoord_continuous (c : D.Cell) (a : A) : Continuous (fun x => D.fullCoord c x a) := by
  unfold fullCoord
  split
  · exact continuous_subtype_val.comp (continuous_apply _)
  · exact continuous_const

def extendCoordinates (c : D.Cell) (x : D.Coordinates c) : D.Coordinates (D.fullCell c.top) :=
  fun a => ⟨D.fullCoord c x a,D.fullCoord_nonneg c x a,D.fullCoord_le_one c x a⟩

@[simp] theorem ones_extend (c : D.Cell) (x : D.Coordinates c) :
    D.ones (D.fullCell c.top) (D.extendCoordinates c x) = D.ones c x := by
  ext a
  simp only [mem_ones,extendCoordinates]
  constructor
  · rintro ⟨ha,he⟩
    by_cases h : a ∈ c.directions
    · exact ⟨h,by simpa only [fullCoord,dite_eq_left h] using he⟩
    · simp [fullCoord,h] at he
  · rintro ⟨ha,he⟩
    exact ⟨c.subset ha,by simpa only [fullCoord,dite_eq_left ha] using he⟩

@[simp] theorem characteristic_extend (c : D.Cell) (x : D.Coordinates c) :
    D.characteristic (D.fullCell c.top) (D.extendCoordinates c x) = D.characteristic c x := by
  apply Point.ext
  · change c.top * D.product c.top (D.ones (D.fullCell c.top) (D.extendCoordinates c x)) _ =
      c.top * D.product c.top (D.ones c x) _
    simp only [product,ones_extend]
  · funext a
    change D.normalizedCoord (D.fullCell c.top) (D.extendCoordinates c x) a = D.normalizedCoord c x a
    by_cases hc : a ∈ c.directions
    · simp [normalizedCoord,fullCell,extendCoordinates,fullCoord,hc,c.subset hc]
    · by_cases ha : a ∈ D.desc c.top <;>
        simp [normalizedCoord,fullCell,extendCoordinates,fullCoord,hc,ha]

variable [Fintype A] [Nonempty A]

def radius (u : A → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty u

theorem radius_continuous : Continuous (radius (A := A)) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun a _ => continuous_apply a)

theorem le_radius (u : A → ℝ) (a : A) : u a ≤ radius u :=
  Finset.le_sup' u (Finset.mem_univ a)

theorem radius_le {u : A → ℝ} {r : ℝ} (h : ∀ a, u a ≤ r) : radius u ≤ r :=
  Finset.sup'_le _ _ (fun a _ => h a)

theorem radius_lt {u : A → ℝ} {r : ℝ} (h : ∀ a, u a < r) : radius u < r :=
  (Finset.sup'_lt_iff _).mpr (fun a _ => h a)

theorem radius_nonneg {u : A → ℝ} (h : ∀ a, 0 ≤ u a) : 0 ≤ radius u :=
  (h (Classical.arbitrary A)).trans (le_radius _ _)

theorem radius_eq_one_iff (c : D.Cell) (x : D.Coordinates c) :
    radius (D.fullCoord c x) = 1 ↔ (D.ones c x).Nonempty := by
  constructor
  · intro hr
    obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (D.fullCoord c x)
    have hh : D.fullCoord c x a = 1 := ha.symm.trans hr
    have hm : a ∈ c.directions := by
      by_contra hn
      simp [fullCoord,hn] at hh
    exact ⟨a,(D.mem_ones c x a).mpr ⟨hm,by simpa [fullCoord,hm] using hh⟩⟩
  · rintro ⟨a,ha⟩
    obtain ⟨ha,he⟩ := (D.mem_ones c x a).mp ha
    apply le_antisymm (radius_le (D.fullCoord_le_one c x))
    have hh := le_radius (D.fullCoord c x) a
    simpa [fullCoord,ha,he] using hh

open scoped unitInterval

def deformCoordinates (c : D.Cell) (x : D.Coordinates c) (t : unitInterval) :
    D.Coordinates (D.fullCell c.top) := fun a =>
  ⟨D.fullCoord c x a + (t : ℝ) * (1 - radius (D.fullCoord c x)),
    add_nonneg (D.fullCoord_nonneg c x a)
      (mul_nonneg t.property.1 (sub_nonneg.mpr (radius_le (D.fullCoord_le_one c x)))),by
        have ha := le_radius (D.fullCoord c x) a
        have hr := radius_le (D.fullCoord_le_one c x)
        have ht := mul_le_of_le_one_left (sub_nonneg.mpr hr) t.property.2
        linarith⟩

theorem deformCoordinates_continuous (c : D.Cell) :
    Continuous (fun z : unitInterval × D.Coordinates c => D.deformCoordinates c z.2 z.1) := by
  apply continuous_pi
  intro a
  apply Continuous.subtype_mk
  exact ((D.fullCoord_continuous c a).comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.sub (radius_continuous.comp
        (continuous_pi (fun a => (D.fullCoord_continuous c a).comp continuous_snd)))))

@[simp] theorem deformCoordinates_zero (c : D.Cell) (x : D.Coordinates c) :
    D.deformCoordinates c x 0 = D.extendCoordinates c x := by
  funext a
  apply Subtype.ext
  simp [deformCoordinates,extendCoordinates]

theorem deformCoordinates_fixed (c : D.Cell) (x : D.Coordinates c) (t : unitInterval)
    (hx : (D.ones c x).Nonempty) :
    D.deformCoordinates c x t = D.extendCoordinates c x := by
  funext a
  apply Subtype.ext
  simp only [deformCoordinates,extendCoordinates,(D.radius_eq_one_iff c x).mpr hx,
    sub_self,mul_zero,add_zero]

/-- The time-one radial deformation reaches a far face whenever the top is
not the identity. It is fixed on every far face from the outset. -/
theorem deformCoordinates_one_ones (c : D.Cell) (x : D.Coordinates c)
    (hc : 0 < D.length c.top) :
    (D.ones (D.fullCell c.top) (D.deformCoordinates c x 1)).Nonempty := by
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (D.fullCoord c x)
  by_cases hm : a ∈ D.desc c.top
  · refine ⟨a,(D.mem_ones _ _ _).mpr ⟨hm,?_⟩⟩
    change D.fullCoord c x a + (1 : ℝ) * (1 - radius (D.fullCoord c x)) = 1
    change D.fullCoord c x a + 1 * (1 - Finset.univ.sup' _ (D.fullCoord c x)) = 1
    rw [ha]
    ring
  · have hn : a ∉ c.directions := fun h => hm (c.subset h)
    have hr : radius (D.fullCoord c x) = 0 := by
      rw [fullCoord,dite_eq_right hn] at ha
      exact ha
    obtain ⟨b,hb⟩ := D.nonempty c.top hc
    have hb0 : D.fullCoord c x b = 0 :=
      le_antisymm (by simpa only [hr] using le_radius (D.fullCoord c x) b)
        (D.fullCoord_nonneg c x b)
    refine ⟨b,(D.mem_ones _ _ _).mpr ⟨hb,?_⟩⟩
    change D.fullCoord c x b + (1 : ℝ) * (1 - radius (D.fullCoord c x)) = 1
    rw [hb0,hr]
    norm_num

def cellDeform (c : D.Cell) (x : D.Coordinates c) (t : unitInterval) : D.Point :=
  D.characteristic (D.fullCell c.top) (D.deformCoordinates c x t)

theorem cellDeform_continuous (c : D.Cell) :
    Continuous (fun z : unitInterval × D.Coordinates c => D.cellDeform c z.2 z.1) :=
  (D.characteristic_continuous _).comp (D.deformCoordinates_continuous c)

@[simp] theorem cellDeform_zero (c : D.Cell) (x : D.Coordinates c) :
    D.cellDeform c x 0 = D.characteristic c x := by
  simp only [cellDeform,deformCoordinates_zero,characteristic_extend]

theorem cellDeform_fixed (c : D.Cell) (x : D.Coordinates c) (t : unitInterval)
    (hx : (D.ones c x).Nonempty) : D.cellDeform c x t = D.characteristic c x := by
  simp only [cellDeform,D.deformCoordinates_fixed c x t hx,characteristic_extend]

theorem cellDeform_one_length (c : D.Cell) (x : D.Coordinates c)
    (hc : 0 < D.length c.top) : D.length (D.cellDeform c x 1).top < D.length c.top := by
  have h := D.characteristic_length (D.fullCell c.top) (D.deformCoordinates c x 1)
  have hp := Finset.card_pos.mpr (D.deformCoordinates_one_ones c x hc)
  change D.length (D.cellDeform c x 1).top + _ = D.length c.top at h
  omega

end

section
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
def farFaceCell (c : D.Cell) (a : c.directions) : D.Cell where
  top := c.top * f a
  directions := c.directions.erase a
  subset := by
    intro b hb
    obtain ⟨hne,hb⟩ := Finset.mem_erase.mp hb
    exact D.preserve c.top a b (c.subset a.property) (c.subset hb) hne.symm

def farFaceCoordinates (c : D.Cell) (a : c.directions) (x : D.Coordinates c) :
    D.Coordinates (D.farFaceCell c a) := fun b => x ⟨b,Finset.mem_of_mem_erase b.property⟩

theorem farFaceCoordinates_continuous (c : D.Cell) (a : c.directions) :
    Continuous (D.farFaceCoordinates c a) := by
  apply continuous_pi
  intro b
  exact continuous_apply _

@[simp] theorem ones_farFace (c : D.Cell) (a : c.directions) (x : D.Coordinates c) :
    D.ones (D.farFaceCell c a) (D.farFaceCoordinates c a x) = (D.ones c x).erase a := by
  ext b
  constructor
  · intro hb
    obtain ⟨hb, he⟩ := (D.mem_ones (D.farFaceCell c a) (D.farFaceCoordinates c a x) b).mp hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    exact Finset.mem_erase.mpr ⟨hne, (D.mem_ones c x b).mpr ⟨hb, he⟩⟩
  · intro hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    obtain ⟨hb, he⟩ := (D.mem_ones c x b).mp hb
    exact (D.mem_ones (D.farFaceCell c a) (D.farFaceCoordinates c a x) b).mpr
      ⟨Finset.mem_erase.mpr ⟨hne, hb⟩, he⟩

theorem characteristic_farFace (c : D.Cell) (a : c.directions) (x : D.Coordinates c)
    (ha : (x a : ℝ) = 1) :
    D.characteristic (D.farFaceCell c a) (D.farFaceCoordinates c a x) =
      D.characteristic c x := by
  have hm : (a : A) ∈ D.ones c x := (D.mem_ones c x a).mpr ⟨a.property,ha⟩
  apply Point.ext
  · change c.top * f a * D.product (c.top * f a)
      (D.ones (D.farFaceCell c a) (D.farFaceCoordinates c a x)) _ =
        c.top * D.product c.top (D.ones c x) _
    simp only [product,ones_farFace]
    rw [mul_assoc]
    congr 1
    have hi : insert (a : A) ((D.ones c x).erase a) = D.ones c x := Finset.insert_erase hm
    have hc : Set.Pairwise (↑(insert (a : A) ((D.ones c x).erase a)) : Set A)
        (fun b d => Commute (f b) (f d)) := by
      intro b hb d hd hne
      rw [hi] at hb hd
      exact D.commute c.top b d (c.subset (D.ones_subset c x hb))
        (c.subset (D.ones_subset c x hd)) hne
    have he := Finset.noncommProd_insert_of_notMem ((D.ones c x).erase a) a f hc
      (Finset.notMem_erase _ _)
    simpa only [hi] using he.symm
  · funext b
    change D.normalizedCoord (D.farFaceCell c a) (D.farFaceCoordinates c a x) b =
      D.normalizedCoord c x b
    by_cases he : b = a
    · subst b
      simp [normalizedCoord,farFaceCell,a.property,ha]
    · by_cases hb : b ∈ c.directions
      · simp [normalizedCoord,farFaceCell,farFaceCoordinates,he,hb]
      · simp [normalizedCoord,farFaceCell,he,hb]

theorem farFaceCell_length (c : D.Cell) (a : c.directions) :
    D.length (D.farFaceCell c a).top + 1 = D.length c.top :=
  D.decrease c.top a (c.subset a.property)

variable [Fintype A]

theorem fullCoord_point (p : D.Point) :
    D.fullCoord (D.pointCell p) (D.pointCoordinates p) = p.coord := by
  funext a
  by_cases h : p.coord a = 0
  · simp [fullCoord,pointCell,h]
  · simp [fullCoord,pointCell,h,pointCoordinates]

omit [Fintype A] in
theorem characteristic_top_of_ones_empty (c : D.Cell) (x : D.Coordinates c)
    (hx : D.ones c x = ∅) : (D.characteristic c x).top = c.top := by
  change c.top * D.product c.top (D.ones c x) _ = c.top
  simp only [product,hx,Finset.noncommProd_empty,mul_one]

omit [Fintype A] in
theorem characteristic_coord_of_ones_empty (c : D.Cell) (x : D.Coordinates c)
    (hx : D.ones c x = ∅) : (D.characteristic c x).coord = D.fullCoord c x := by
  funext a
  change D.normalizedCoord c x a = D.fullCoord c x a
  by_cases ha : a ∈ c.directions
  · have hne : (x ⟨a,ha⟩ : ℝ) ≠ 1 := by
      intro he
      have hh := (D.mem_ones c x a).mpr ⟨ha,he⟩
      rw [hx] at hh
      exact Finset.notMem_empty a hh
    simp [normalizedCoord,fullCoord,ha,hne]
  · simp [normalizedCoord,fullCoord,ha]

variable [Nonempty A]
open scoped unitInterval

def pointDeform (p : D.Point) (t : unitInterval) : D.Point :=
  D.cellDeform (D.pointCell p) (D.pointCoordinates p) t

@[simp] theorem pointDeform_zero (p : D.Point) : D.pointDeform p 0 = p := by
  simp only [pointDeform,cellDeform_zero,characteristic_point]

theorem pointDeform_one_length (p : D.Point) (hp : 0 < D.length p.top) :
    D.length (D.pointDeform p 1).top < D.length p.top :=
  D.cellDeform_one_length (D.pointCell p) (D.pointCoordinates p) hp

theorem cellDeform_congr (c d : D.Cell) (x : D.Coordinates c) (y : D.Coordinates d)
    (t : unitInterval) (ht : c.top = d.top) (hx : D.fullCoord c x = D.fullCoord d y) :
    D.cellDeform c x t = D.cellDeform d y t := by
  rcases c with ⟨g,s,hs⟩
  rcases d with ⟨h,r,hr⟩
  dsimp only at ht
  subst h
  unfold cellDeform
  congr 1
  funext a
  apply Subtype.ext
  change D.fullCoord _ x a + (t : ℝ) * (1 - radius (D.fullCoord _ x)) =
    D.fullCoord _ y a + (t : ℝ) * (1 - radius (D.fullCoord _ y))
  rw [hx]

/-- On the open part of a cube, radial deformation in its full descending
cube is independent of which zero coordinates were omitted. -/
theorem pointDeform_characteristic (c : D.Cell) (x : D.Coordinates c) (t : unitInterval)
    (hx : D.ones c x = ∅) : D.pointDeform (D.characteristic c x) t = D.cellDeform c x t := by
  have ht := D.characteristic_top_of_ones_empty c x hx
  have hc := D.characteristic_coord_of_ones_empty c x hx
  exact D.cellDeform_congr (D.pointCell (D.characteristic c x)) c
    (D.pointCoordinates _) x t ht ((D.fullCoord_point _).trans hc)

end

variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
variable [Fintype A] [Nonempty A]
open scoped unitInterval NNReal
def clip (r : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one r

theorem clip_continuous : Continuous clip := continuous_projIcc (h := zero_le_one)

theorem clip_zero {r : ℝ} (h : r ≤ 0) : clip r = 0 := by
  apply Subtype.ext
  simp [clip,h]

theorem clip_one {r : ℝ} (h : 1 ≤ r) : clip r = 1 := by
  apply Subtype.ext
  simp [clip,h]

/-- Flow to word-length height r, stopping part-way across its unique top shell. -/
def flow (r : ℝ≥0) (p : D.Point) : D.Point :=
  if _h : (D.length p.top : ℝ) ≤ r then p
  else if (D.length p.top : ℝ) - 1 ≤ r then
    D.pointDeform p (clip ((D.length p.top : ℝ) - r))
  else flow r (D.pointDeform p 1)
termination_by D.length p.top
decreasing_by
  apply D.pointDeform_one_length
  have hr := r.property
  by_contra hn
  have hz : D.length p.top = 0 := by omega
  simp only [hz,Nat.cast_zero] at _h
  exact _h hr

theorem flow_fixed (r : ℝ≥0) (p : D.Point) (h : (D.length p.top : ℝ) ≤ r) :
    D.flow r p = p := by rw [flow, dite_eq_left h]

theorem flow_partial (r : ℝ≥0) (p : D.Point)
    (h : (D.length p.top : ℝ) - 1 ≤ r) :
    D.flow r p = D.pointDeform p (clip ((D.length p.top : ℝ) - r)) := by
  rw [flow]
  split_ifs with hh
  · rw [clip_zero (by linarith),pointDeform_zero]
  · rfl

theorem flow_lower (r : ℝ≥0) (p : D.Point)
    (h : (r : ℝ) ≤ (D.length p.top : ℝ) - 1) :
    D.flow r p = D.flow r (D.pointDeform p 1) := by
  have hp : 0 < D.length p.top := by
    by_contra hn
    have hz : D.length p.top = 0 := by omega
    have hr := r.property
    simp only [hz,Nat.cast_zero] at h
    linarith
  have hn : ¬ (D.length p.top : ℝ) ≤ r := by linarith
  rw [flow,dite_eq_right hn]
  split_ifs with hh
  · have he : (r : ℝ) = (D.length p.top : ℝ) - 1 := le_antisymm h hh
    rw [clip_one (by linarith)]
    symm
    apply D.flow_fixed
    have hl := D.pointDeform_one_length p hp
    have hy : (D.length (D.pointDeform p 1).top : ℝ) + 1 ≤ (D.length p.top : ℝ) := by
      exact_mod_cast hl
    linarith
  · rfl

theorem flow_characteristic_high (c : D.Cell) (x : D.Coordinates c) (r : ℝ≥0)
    (hr : (D.length c.top : ℝ) - 1 ≤ r) :
    D.flow r (D.characteristic c x) =
      D.cellDeform c x (clip ((D.length c.top : ℝ) - r)) := by
  by_cases hx : D.ones c x = ∅
  · rw [D.flow_partial r _ (by rw [D.characteristic_top_of_ones_empty c x hx]; exact hr)]
    rw [D.characteristic_top_of_ones_empty c x hx]
    exact D.pointDeform_characteristic c x _ hx
  · have hne := Finset.nonempty_iff_ne_empty.mpr hx
    rw [D.cellDeform_fixed c x _ hne]
    apply D.flow_fixed
    have hl := D.characteristic_length c x
    have hc : 0 < (D.ones c x).card := Finset.card_pos.mpr hne
    have hh : D.length (D.characteristic c x).top + 1 ≤ D.length c.top := by omega
    have hh' : (D.length (D.characteristic c x).top : ℝ) + 1 ≤ D.length c.top := by
      exact_mod_cast hh
    linarith

theorem flow_characteristic_low (c : D.Cell) (x : D.Coordinates c) (r : ℝ≥0)
    (hr : (r : ℝ) ≤ (D.length c.top : ℝ) - 1) :
    D.flow r (D.characteristic c x) = D.flow r (D.cellDeform c x 1) := by
  by_cases hx : D.ones c x = ∅
  · rw [D.flow_lower r _ (by rw [D.characteristic_top_of_ones_empty c x hx]; exact hr)]
    rw [D.pointDeform_characteristic c x 1 hx]
  · rw [D.cellDeform_fixed c x 1 (Finset.nonempty_iff_ne_empty.mpr hx)]

theorem flow_cell_zero_continuous (c : D.Cell) (hc : D.length c.top = 0) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
  have he : (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) =
      fun z => D.characteristic c z.2 := by
    funext z
    apply D.flow_fixed
    have hl := D.characteristic_length c z.2
    have hh : D.length (D.characteristic c z.2).top = 0 := by omega
    rw [hh,Nat.cast_zero]
    exact z.1.property
  rw [he]
  exact (D.characteristic_continuous c).comp continuous_snd

theorem flow_cell_boundary_continuous (c : D.Cell) (hp : 0 < D.length c.top)
    (ih : ∀ d : D.Cell, D.length d.top < D.length c.top →
      Continuous (fun z : ℝ≥0 × D.Coordinates d => D.flow z.1 (D.characteristic d z.2))) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.cellDeform c z.2 1)) := by
  have hcoord : Continuous (fun z : ℝ≥0 × D.Coordinates c => D.deformCoordinates c z.2 1) :=
    (D.deformCoordinates_continuous c).comp (continuous_const.prodMk continuous_snd)
  let S : D.desc c.top → Set (ℝ≥0 × D.Coordinates c) := fun a =>
    {z | (D.deformCoordinates c z.2 1 a : ℝ) = 1}
  have hs : ∀ a, IsClosed (S a) := by
    intro a
    exact isClosed_eq (continuous_subtype_val.comp ((continuous_apply a).comp hcoord)) continuous_const
  have hcov : ⋃ a, S a = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨a,ha⟩ := D.deformCoordinates_one_ones c z.2 hp
    obtain ⟨ha,he⟩ := (D.mem_ones _ _ _).mp ha
    exact Set.mem_iUnion.mpr ⟨⟨a,ha⟩,he⟩
  apply (locallyFinite_of_finite S).continuous hcov hs
  intro a
  let d := D.farFaceCell (D.fullCell c.top) a
  have hd : D.length d.top < D.length c.top := by
    have he := D.farFaceCell_length (D.fullCell c.top) a
    change D.length d.top + 1 = D.length c.top at he
    omega
  have hh := ih d hd
  have hf : Continuous (fun z : ℝ≥0 × D.Coordinates c =>
      (z.1,D.farFaceCoordinates (D.fullCell c.top) a (D.deformCoordinates c z.2 1))) :=
    continuous_fst.prodMk ((D.farFaceCoordinates_continuous (D.fullCell c.top) a).comp hcoord)
  apply (hh.comp hf).continuousOn.congr
  intro z hz
  exact congrArg (D.flow z.1)
    (D.characteristic_farFace (D.fullCell c.top) a (D.deformCoordinates c z.2 1) hz).symm

theorem flow_cell_glue_continuous (c : D.Cell)
    (hlower : Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.cellDeform c z.2 1))) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
  have hhigh : Continuous (fun z : ℝ≥0 × D.Coordinates c =>
      D.cellDeform c z.2 (clip ((D.length c.top : ℝ) - z.1))) := by
    have ht : Continuous (fun z : ℝ≥0 × D.Coordinates c =>
        (clip ((D.length c.top : ℝ) - z.1),z.2)) :=
      (clip_continuous.comp (continuous_const.sub
        (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd
    change Continuous ((fun z : unitInterval × D.Coordinates c => D.cellDeform c z.2 z.1) ∘
      (fun z : ℝ≥0 × D.Coordinates c => (clip ((D.length c.top : ℝ) - (z.1 : ℝ)),z.2)))
    exact Continuous.comp (D.cellDeform_continuous c) ht
  let L : Set (ℝ≥0 × D.Coordinates c) := {z | (z.1 : ℝ) ≤ (D.length c.top : ℝ) - 1}
  let U : Set (ℝ≥0 × D.Coordinates c) := {z | (D.length c.top : ℝ) - 1 ≤ z.1}
  have hL : IsClosed L := isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const
  have hU : IsClosed U := isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst)
  have hcover : L ∪ U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    change (z.1 : ℝ) ≤ (D.length c.top : ℝ) - 1 ∨ (D.length c.top : ℝ) - 1 ≤ z.1
    exact le_total _ _
  apply continuousOn_univ.mp
  rw [← hcover]
  apply ContinuousOn.union_of_isClosed _ _ hL hU
  · apply hlower.continuousOn.congr
    intro z hz
    exact D.flow_characteristic_low c z.2 z.1 hz
  · apply hhigh.continuousOn.congr
    intro z hz
    exact D.flow_characteristic_high c z.2 z.1 hz

theorem flow_cell_continuous (c : D.Cell) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
  have H : ∀ n : ℕ, ∀ c : D.Cell, D.length c.top = n →
      Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hn
      by_cases hz : n = 0
      · exact D.flow_cell_zero_continuous c (hn.trans hz)
      apply D.flow_cell_glue_continuous c
      apply D.flow_cell_boundary_continuous c (by omega)
      intro d hd
      exact ih (D.length d.top) (by omega) d rfl
  exact H (D.length c.top) c rfl

theorem flow_continuous : Continuous (fun z : ℝ≥0 × D.Point => D.flow z.1 z.2) := by
  apply D.evaluation_quotient.continuous_lift_prod_right
  have hc : Continuous (fun z : (c : D.Cell) × (D.Coordinates c × ℝ≥0) =>
      D.flow z.2.2 (D.characteristic z.1 z.2.1)) := by
    apply continuous_sigma
    intro c
    exact (D.flow_cell_continuous c).comp continuous_swap
  exact hc.comp ((Homeomorph.sigmaProdDistrib (X := fun c : D.Cell => D.Coordinates c) (Y := ℝ≥0)).continuous.comp
    continuous_swap)

def origin : D.Point where
  top := 1
  coord := fun _ => 0
  nonneg _ := le_rfl
  lt_one _ := zero_lt_one
  support _ h := False.elim (h rfl)

omit [Fintype A] [Nonempty A] in
theorem point_eq_origin_of_length_zero (p : D.Point) (hp : D.length p.top = 0) :
    p = D.origin := by
  apply Point.ext
  · exact (D.zero p.top).mp hp
  · funext a
    change p.coord a = 0
    by_contra ha
    have hh := D.decrease p.top a (p.support a ha)
    omega

@[simp] theorem flow_zero (p : D.Point) : D.flow 0 p = D.origin := by
  have H : ∀ n : ℕ, ∀ p : D.Point, D.length p.top = n → D.flow 0 p = D.origin := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hz : n = 0
      · have hp : D.length p.top = 0 := hn.trans hz
        rw [D.flow_fixed 0 p (by simp [hp])]
        exact D.point_eq_origin_of_length_zero p hp
      have hp : 0 < D.length p.top := by omega
      have hr : (0 : ℝ) ≤ (D.length p.top : ℝ) - 1 := by
        have hh : (1 : ℝ) ≤ D.length p.top := by exact_mod_cast hp
        linarith
      rw [D.flow_lower 0 p hr]
      have hl := D.pointDeform_one_length p hp
      exact ih (D.length (D.pointDeform p 1).top) (by omega) (D.pointDeform p 1) rfl
  exact H (D.length p.top) p rfl

def contraction (t : unitInterval) (p : D.Point) : D.Point :=
  if (t : ℝ) = 0 then p else D.flow (Real.toNNReal ((1 - (t : ℝ)) / t)) p

@[simp] theorem contraction_zero (p : D.Point) : D.contraction 0 p = p := by
  simp [contraction]

@[simp] theorem contraction_one (p : D.Point) : D.contraction 1 p = D.origin := by
  simp [contraction]

theorem heightTime_large (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hb : s ≤ 1 / ((n : ℝ) + 1)) :
    (n : ℝ) ≤ (Real.toNNReal ((1 - s) / s) : ℝ) := by
  apply le_trans _ (Real.le_coe_toNNReal _)
  apply (le_div_iff₀ hs).mpr
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh := (le_div_iff₀ hn).mp hb
  nlinarith

theorem contraction_cell_eventually_zero (c : D.Cell) (z : unitInterval × D.Coordinates c)
    (hz : (z.1 : ℝ) = 0) :
    (fun w : unitInterval × D.Coordinates c => D.contraction w.1 (D.characteristic c w.2))
      =ᶠ[nhds z] (fun w => D.characteristic c w.2) := by
  have he : 0 < 1 / ((D.length c.top : ℝ) + 1) := by positivity
  have hn : {w : unitInterval × D.Coordinates c | (w.1 : ℝ) < 1 / ((D.length c.top : ℝ) + 1)}
      ∈ nhds z :=
    (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).mem_nhds
      (by change (z.1 : ℝ) < _; rw [hz]; exact he)
  filter_upwards [hn] with w hw
  unfold contraction
  split_ifs with hs
  · rfl
  · apply D.flow_fixed
    have hp : 0 < (w.1 : ℝ) := lt_of_le_of_ne w.1.property.1 (Ne.symm hs)
    have ht := heightTime_large (D.length c.top) hp hw.le
    have hl := D.characteristic_length c w.2
    have hh : D.length (D.characteristic c w.2).top ≤ D.length c.top := by omega
    exact (by exact_mod_cast hh : (D.length (D.characteristic c w.2).top : ℝ) ≤ D.length c.top).trans ht

theorem contraction_cell_continuous (c : D.Cell) :
    Continuous (fun z : unitInterval × D.Coordinates c => D.contraction z.1 (D.characteristic c z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : (z.1 : ℝ) = 0
  · exact ((D.characteristic_continuous c).comp continuous_snd).continuousAt.congr_of_eventuallyEq
      (D.contraction_cell_eventually_zero c z hz)
  · have hs : ContinuousAt (fun w : unitInterval × D.Coordinates c =>
        Real.toNNReal ((1 - (w.1 : ℝ)) / w.1)) z := by
      apply (continuous_real_toNNReal).continuousAt.comp
      exact (continuousAt_const.sub (continuous_subtype_val.comp continuous_fst).continuousAt).div
        (continuous_subtype_val.comp continuous_fst).continuousAt hz
    have hh : ContinuousAt (fun w : unitInterval × D.Coordinates c =>
        D.flow (Real.toNNReal ((1 - (w.1 : ℝ)) / w.1)) (D.characteristic c w.2)) z :=
      D.flow_continuous.continuousAt.comp (hs.prodMk
        ((D.characteristic_continuous c).comp continuous_snd).continuousAt)
    apply hh.congr_of_eventuallyEq
    have hn : {w : unitInterval × D.Coordinates c | (w.1 : ℝ) ≠ 0} ∈ nhds z :=
      ((continuous_subtype_val.comp continuous_fst).isOpen_preimage _ isOpen_ne).mem_nhds hz
    filter_upwards [hn] with w hw
    simp only [contraction,ite_eq_right hw]

theorem contraction_continuous : Continuous (fun z : unitInterval × D.Point => D.contraction z.1 z.2) := by
  apply D.evaluation_quotient.continuous_lift_prod_right
  have hc : Continuous (fun z : (c : D.Cell) × (D.Coordinates c × unitInterval) =>
      D.contraction z.2.2 (D.characteristic z.1 z.2.1)) := by
    apply continuous_sigma
    intro c
    exact (D.contraction_cell_continuous c).comp continuous_swap
  exact hc.comp ((Homeomorph.sigmaProdDistrib (X := fun c : D.Cell => D.Coordinates c)
    (Y := unitInterval)).continuous.comp continuous_swap)

/-- Direct radial-shell contraction; no cellular homology or Whitehead theorem is used. -/
theorem contractibleSpace : ContractibleSpace D.Point := by
  apply (contractible_iff_id_nullhomotopic D.Point).mpr
  refine ⟨D.origin,⟨?_⟩⟩
  exact { toFun := fun z => D.contraction z.1 z.2
          continuous_toFun := D.contraction_continuous
          map_zero_left := D.contraction_zero
          map_one_left := D.contraction_one }

end EilenbergGanea.DescendingCube.Data

end

end OAI
