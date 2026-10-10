import OAI.Analysis.SphereIsometry.RadialContact
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.ContinuousOn

namespace OAI

/-!
# The actual radial return map

For fixed `f`, `y` and `0 < t < 1`, the two interior centers are `t • y`
and `t • f y`. The map follows the two radial contacts.
The opposite direction is literal vector negation, with no antipodality
assumption on `f`. The ambient extensions are continuous on the unit sphere;
no continuity away from that sphere is asserted.
-/

noncomputable section

namespace Tingley

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Literal negation of a unit vector. -/
def sphereNeg (v : UnitSphere X) : UnitSphere X :=
  ⟨-(v : X), by simpa only [norm_neg] using v.property⟩

omit [NormedSpace ℝ X] in
@[simp] theorem sphereNeg_coe (v : UnitSphere X) :
    (sphereNeg v : X) = -(v : X) := rfl

omit [NormedSpace ℝ X] in
theorem continuous_sphereNeg : Continuous (sphereNeg : UnitSphere X → UnitSphere X) :=
  continuous_subtype_val.neg.subtype_mk _

theorem norm_smul_unitSphere (y : UnitSphere X) (t : ℝ) (ht : 0 ≤ t) :
    ‖t • (y : X)‖ = t := by
  rw [norm_smul, Real.norm_of_nonneg ht, y.property, mul_one]

theorem returnCenter_lt_one (y : UnitSphere X) (t : ℝ) (ht : 0 < t ∧ t < 1) :
    ‖t • (y : X)‖ < 1 := by
  rw [norm_smul_unitSphere y t ht.1.le]
  exact ht.2

/-- Distances from any unit point to either interior center have uniform bounds. -/
theorem norm_unit_sub_center_bounds (x y : UnitSphere X) (t : ℝ) (ht : 0 ≤ t) :
    1 - t ≤ ‖(x : X) - t • (y : X)‖ ∧
      ‖(x : X) - t • (y : X)‖ ≤ 1 + t := by
  constructor
  · simpa only [x.property, norm_smul_unitSphere y t ht] using
      norm_sub_norm_le (x : X) (t • (y : X))
  · simpa only [x.property, norm_smul_unitSphere y t ht] using
      norm_sub_le (x : X) (t • (y : X))

theorem unit_sub_center_ne_zero (x y : UnitSphere X) (t : ℝ)
    (ht : 0 < t ∧ t < 1) : (x : X) - t • (y : X) ≠ 0 := by
  intro h
  have hbound := (norm_unit_sub_center_bounds x y t ht.1.le).1
  rw [h, norm_zero] at hbound
  linarith [ht.2]

theorem center_sub_unit_ne_zero (x y : UnitSphere X) (t : ℝ)
    (ht : 0 < t ∧ t < 1) : t • (y : X) - (x : X) ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (unit_sub_center_ne_zero x y t ht)))

/-- The first radial radius. The isometry is an explicit common parameter even
though this first contact only uses the domain center. -/
def pRadius (_f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
    (t : ℝ) (ht : 0 < t ∧ t < 1) (v : UnitSphere X) : ℝ :=
  radialRadius (t • (y : X)) (returnCenter_lt_one y t ht) v

variable (f : UnitSphere X ≃ᵢ UnitSphere Y) (y : UnitSphere X)
variable (t : ℝ) (ht : 0 < t ∧ t < 1)

/-- The first contact point `t y + p v`. -/
def xPoint (v : UnitSphere X) : UnitSphere X :=
  ⟨t • (y : X) + pRadius f y t ht v • (v : X),
    norm_radialRadius (t • (y : X)) (returnCenter_lt_one y t ht) v⟩

def sRadius (v : UnitSphere X) : ℝ :=
  ‖(f (xPoint f y t ht v) : Y) - t • (f y : Y)‖

/-- The image-side outward unit direction. -/
def wDirection (v : UnitSphere X) : UnitSphere Y :=
  normalize ((f (xPoint f y t ht v) : Y) - t • (f y : Y))
    (unit_sub_center_ne_zero (f (xPoint f y t ht v)) (f y) t ht)

/-- The second radial contact uses the negative of the actual direction `w`. -/
def uRadius (v : UnitSphere X) : ℝ :=
  radialRadius (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v))

def zPoint (v : UnitSphere X) : UnitSphere X :=
  f.symm (radialContact (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v)))

def rRadius (v : UnitSphere X) : ℝ :=
  ‖(zPoint f y t ht v : X) - t • (y : X)‖

/-- The genuine return map on the unit sphere. -/
def returnSphere (v : UnitSphere X) : UnitSphere X :=
  normalize (t • (y : X) - (zPoint f y t ht v : X))
    (center_sub_unit_ne_zero (zPoint f y t ht v) y t ht)

omit [NormedSpace ℝ Y] in
theorem pRadius_pos (v : UnitSphere X) : 0 < pRadius f y t ht v :=
  radialRadius_pos (t • (y : X)) (returnCenter_lt_one y t ht) v

omit [NormedSpace ℝ Y] in
theorem pRadius_bounds (v : UnitSphere X) :
    1 - t ≤ pRadius f y t ht v ∧ pRadius f y t ht v ≤ 1 + t := by
  simpa only [pRadius, norm_smul_unitSphere y t ht.1.le] using
    radialRadius_bounds (t • (y : X)) (returnCenter_lt_one y t ht) v

theorem sRadius_bounds (v : UnitSphere X) :
    1 - t ≤ sRadius f y t ht v ∧ sRadius f y t ht v ≤ 1 + t :=
  norm_unit_sub_center_bounds (f (xPoint f y t ht v)) (f y) t ht.1.le

theorem sRadius_pos (v : UnitSphere X) : 0 < sRadius f y t ht v :=
  (sub_pos.mpr ht.2).trans_le (sRadius_bounds f y t ht v).1

theorem uRadius_pos (v : UnitSphere X) : 0 < uRadius f y t ht v :=
  radialRadius_pos (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
    (sphereNeg (wDirection f y t ht v))

theorem uRadius_bounds (v : UnitSphere X) :
    1 - t ≤ uRadius f y t ht v ∧ uRadius f y t ht v ≤ 1 + t := by
  simpa only [uRadius, norm_smul_unitSphere (f y) t ht.1.le] using
    radialRadius_bounds (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)
      (sphereNeg (wDirection f y t ht v))

theorem rRadius_bounds (v : UnitSphere X) :
    1 - t ≤ rRadius f y t ht v ∧ rRadius f y t ht v ≤ 1 + t :=
  norm_unit_sub_center_bounds (zPoint f y t ht v) y t ht.1.le

theorem rRadius_pos (v : UnitSphere X) : 0 < rRadius f y t ht v :=
  (sub_pos.mpr ht.2).trans_le (rRadius_bounds f y t ht v).1

theorem radii_pos (v : UnitSphere X) :
    0 < pRadius f y t ht v ∧ 0 < sRadius f y t ht v ∧
      0 < uRadius f y t ht v ∧ 0 < rRadius f y t ht v :=
  ⟨pRadius_pos f y t ht v, sRadius_pos f y t ht v,
    uRadius_pos f y t ht v, rRadius_pos f y t ht v⟩

theorem radii_bounds (v : UnitSphere X) :
    pRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      sRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      uRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) ∧
      rRadius f y t ht v ∈ Set.Icc (1 - t) (1 + t) :=
  ⟨pRadius_bounds f y t ht v, sRadius_bounds f y t ht v,
    uRadius_bounds f y t ht v, rRadius_bounds f y t ht v⟩

omit [NormedSpace ℝ Y] in
theorem xPoint_eq (v : UnitSphere X) :
    (xPoint f y t ht v : X) = t • (y : X) + pRadius f y t ht v • (v : X) := rfl

theorem fxPoint_eq (v : UnitSphere X) :
    (f (xPoint f y t ht v) : Y) =
      t • (f y : Y) + sRadius f y t ht v • (wDirection f y t ht v : Y) := by
  have h : sRadius f y t ht v • (wDirection f y t ht v : Y) =
      (f (xPoint f y t ht v) : Y) - t • (f y : Y) :=
    norm_smul_normalize _ _
  rw [h]
  abel

theorem fzPoint_eq (v : UnitSphere X) :
    (f (zPoint f y t ht v) : Y) =
      t • (f y : Y) - uRadius f y t ht v • (wDirection f y t ht v : Y) := by
  simp only [zPoint, IsometryEquiv.apply_symm_apply, radialContact_coe,
    sphereNeg_coe, smul_neg, sub_eq_add_neg, uRadius]

theorem zPoint_eq (v : UnitSphere X) :
    (zPoint f y t ht v : X) =
      t • (y : X) - rRadius f y t ht v • (returnSphere f y t ht v : X) := by
  have h : ‖t • (y : X) - (zPoint f y t ht v : X)‖ •
      (returnSphere f y t ht v : X) = t • (y : X) - (zPoint f y t ht v : X) :=
    norm_smul_normalize _ _
  rw [norm_sub_rev] at h
  change rRadius f y t ht v • (returnSphere f y t ht v : X) = _ at h
  rw [h]
  abel

omit [NormedSpace ℝ Y] in
theorem norm_xPoint_sub_center (v : UnitSphere X) :
    ‖(xPoint f y t ht v : X) - t • (y : X)‖ = pRadius f y t ht v := by
  rw [xPoint_eq, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (pRadius_pos f y t ht v).le, v.property, mul_one]

theorem norm_fxPoint_sub_center (v : UnitSphere X) :
    ‖(f (xPoint f y t ht v) : Y) - t • (f y : Y)‖ = sRadius f y t ht v := rfl

theorem norm_zPoint_sub_center (v : UnitSphere X) :
    ‖(zPoint f y t ht v : X) - t • (y : X)‖ = rRadius f y t ht v := rfl

omit [NormedSpace ℝ Y] in
/-- Radial uniqueness recovers any given unit endpoint from its direction. -/
theorem pRadius_normalize_sub (x : UnitSphere X) :
    pRadius f y t ht (normalize ((x : X) - t • (y : X))
      (unit_sub_center_ne_zero x y t ht)) = ‖(x : X) - t • (y : X)‖ := by
  symm
  apply radialRadius_unique (t • (y : X)) (returnCenter_lt_one y t ht) _ (norm_nonneg _)
  rw [norm_smul_normalize]
  have he : t • (y : X) + ((x : X) - t • (y : X)) = (x : X) := by abel
  rw [he]
  exact x.property

omit [NormedSpace ℝ Y] in
theorem xPoint_normalize_sub (x : UnitSphere X) :
    xPoint f y t ht (normalize ((x : X) - t • (y : X))
      (unit_sub_center_ne_zero x y t ht)) = x := by
  apply Subtype.ext
  rw [xPoint_eq, pRadius_normalize_sub, norm_smul_normalize]
  abel

omit [NormedSpace ℝ Y] in
theorem xPoint_surjective : Function.Surjective (xPoint f y t ht) := by
  intro x
  exact ⟨normalize ((x : X) - t • (y : X)) (unit_sub_center_ne_zero x y t ht),
    xPoint_normalize_sub f y t ht x⟩

/-- Normalizing a continuous everywhere-nonzero map preserves continuity. -/
theorem continuous_normalize_map {A : Type*} [TopologicalSpace A]
    (g : A → X) (hg : Continuous g) (hzero : ∀ a, g a ≠ 0) :
    Continuous (fun a => normalize (g a) (hzero a)) := by
  exact ((hg.norm.inv₀ (fun a => norm_ne_zero_iff.mpr (hzero a))).smul hg).subtype_mk _

omit [NormedSpace ℝ Y] in
theorem continuous_pRadius : Continuous (pRadius f y t ht) :=
  continuous_radialRadius (t • (y : X)) (returnCenter_lt_one y t ht)

omit [NormedSpace ℝ Y] in
theorem continuous_xPoint : Continuous (xPoint f y t ht) :=
  continuous_radialContact (t • (y : X)) (returnCenter_lt_one y t ht)

theorem continuous_sRadius : Continuous (sRadius f y t ht) :=
  ((continuous_subtype_val.comp (f.continuous.comp (continuous_xPoint f y t ht))).sub
    continuous_const).norm

theorem continuous_wDirection : Continuous (wDirection f y t ht) :=
  continuous_normalize_map _
    ((continuous_subtype_val.comp (f.continuous.comp (continuous_xPoint f y t ht))).sub
      continuous_const)
    (fun v => unit_sub_center_ne_zero (f (xPoint f y t ht v)) (f y) t ht)

theorem continuous_uRadius : Continuous (uRadius f y t ht) :=
  (continuous_radialRadius (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)).comp
    (continuous_sphereNeg.comp (continuous_wDirection f y t ht))

theorem continuous_zPoint : Continuous (zPoint f y t ht) :=
  f.symm.continuous.comp
    ((continuous_radialContact (t • (f y : Y)) (returnCenter_lt_one (f y) t ht)).comp
      (continuous_sphereNeg.comp (continuous_wDirection f y t ht)))

theorem continuous_rRadius : Continuous (rRadius f y t ht) :=
  ((continuous_subtype_val.comp (continuous_zPoint f y t ht)).sub continuous_const).norm

theorem continuous_returnSphere : Continuous (returnSphere f y t ht) :=
  continuous_normalize_map _
    (continuous_const.sub (continuous_subtype_val.comp (continuous_zPoint f y t ht)))
    (fun v => center_sub_unit_ne_zero (zPoint f y t ht v) y t ht)

/-- Total ambient functions, used only on the sphere by the convex-set argument. -/
def pAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then pRadius f y t ht ⟨v, hv⟩ else 0

def sAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then sRadius f y t ht ⟨v, hv⟩ else 0

def uAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then uRadius f y t ht ⟨v, hv⟩ else 0

def rAmbient (v : X) : ℝ :=
  if hv : ‖v‖ = 1 then rRadius f y t ht ⟨v, hv⟩ else 0

def returnAmbient (v : X) : X :=
  if hv : ‖v‖ = 1 then (returnSphere f y t ht ⟨v, hv⟩ : X) else 0

omit [NormedSpace ℝ Y] in
@[simp] theorem pAmbient_coe (v : UnitSphere X) :
    pAmbient f y t ht (v : X) = pRadius f y t ht v := by
  simp only [pAmbient, v.property, dite_eq_left]

@[simp] theorem sAmbient_coe (v : UnitSphere X) :
    sAmbient f y t ht (v : X) = sRadius f y t ht v := by
  simp only [sAmbient, v.property, dite_eq_left]

@[simp] theorem uAmbient_coe (v : UnitSphere X) :
    uAmbient f y t ht (v : X) = uRadius f y t ht v := by
  simp only [uAmbient, v.property, dite_eq_left]

@[simp] theorem rAmbient_coe (v : UnitSphere X) :
    rAmbient f y t ht (v : X) = rRadius f y t ht v := by
  simp only [rAmbient, v.property, dite_eq_left]

@[simp] theorem returnAmbient_coe (v : UnitSphere X) :
    returnAmbient f y t ht (v : X) = (returnSphere f y t ht v : X) := by
  simp only [returnAmbient, v.property, dite_eq_left]

omit [NormedSpace ℝ Y] in
theorem continuousOn_pAmbient :
    ContinuousOn (pAmbient f y t ht) {v : X | ‖v‖ = 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : ({v : X | ‖v‖ = 1}).domRestrict (pAmbient f y t ht) = pRadius f y t ht := by
    funext v
    exact pAmbient_coe f y t ht v
  rw [he]
  exact continuous_pRadius f y t ht

theorem continuousOn_sAmbient :
    ContinuousOn (sAmbient f y t ht) {v : X | ‖v‖ = 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : ({v : X | ‖v‖ = 1}).domRestrict (sAmbient f y t ht) = sRadius f y t ht := by
    funext v
    exact sAmbient_coe f y t ht v
  rw [he]
  exact continuous_sRadius f y t ht

theorem continuousOn_uAmbient :
    ContinuousOn (uAmbient f y t ht) {v : X | ‖v‖ = 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : ({v : X | ‖v‖ = 1}).domRestrict (uAmbient f y t ht) = uRadius f y t ht := by
    funext v
    exact uAmbient_coe f y t ht v
  rw [he]
  exact continuous_uRadius f y t ht

theorem continuousOn_rAmbient :
    ContinuousOn (rAmbient f y t ht) {v : X | ‖v‖ = 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : ({v : X | ‖v‖ = 1}).domRestrict (rAmbient f y t ht) = rRadius f y t ht := by
    funext v
    exact rAmbient_coe f y t ht v
  rw [he]
  exact continuous_rRadius f y t ht

theorem continuousOn_returnAmbient :
    ContinuousOn (returnAmbient f y t ht) {v : X | ‖v‖ = 1} := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : ({v : X | ‖v‖ = 1}).domRestrict (returnAmbient f y t ht) =
      fun v : UnitSphere X => (returnSphere f y t ht v : X) := by
    funext v
    exact returnAmbient_coe f y t ht v
  rw [he]
  exact continuous_subtype_val.comp (continuous_returnSphere f y t ht)

end Tingley

end

end OAI
