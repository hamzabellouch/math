import Mathlib
import OAI.Geometry.NearbyLagrangian.QuadraticStability
import OAI.Topology.Homotopy.ConeHomotopy

namespace OAI

/-! Fiberwise suspension equivalences and spherical quotient coordinates. -/

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.FiberCone.Contraction
variable {B A X : Type*} [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace X]
variable {f : C(A,X)} {p : C(X,B)} {q : C(A,B)} {hf : ∀ a, p (f a) = q a}

def suspensionEquiv (H : Contraction f p q hf) :
    Tubes.FiberwiseHomotopyEquiv (suspProjection q) (suspProjection p) where
  toFun := suspMap f p q hf
  invFun := H.inverse
  toFun_over := suspMap_over f p q hf
  invFun_over := H.inverse_over
  left := H.leftHomotopy
  right := H.rightHomotopy
  left_over := H.leftHomotopy_over
  right_over := H.rightHomotopy_over

end NearbyLagrangian.FiberCone.Contraction

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.Tubes.FiberwiseHomotopyEquiv
open FiberCone
variable {B A X : Type*} [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace X]
variable {p : C(X,B)} {q : C(A,B)}

def suspension (e : Tubes.FiberwiseHomotopyEquiv q p) :
    Tubes.FiberwiseHomotopyEquiv (suspProjection q) (suspProjection p) where
  toFun := suspMap e.toFun p q e.toFun_over
  invFun := suspMap e.invFun q p e.invFun_over
  toFun_over := suspMap_over e.toFun p q e.toFun_over
  invFun_over := suspMap_over e.invFun q p e.invFun_over
  left := (suspHomotopy
    (fun a => (e.invFun_over (e.toFun a)).trans (e.toFun_over a))
    (fun _ => rfl) e.left e.left_over).cast (suspMap_comp _ _ _ _ _ _ _).symm (suspMap_id q)
  right := (suspHomotopy
    (fun x => (e.toFun_over (e.invFun x)).trans (e.invFun_over x))
    (fun _ => rfl) e.right e.right_over).cast (suspMap_comp _ _ _ _ _ _ _).symm (suspMap_id p)
  left_over := suspHomotopy_over
    (fun a => (e.invFun_over (e.toFun a)).trans (e.toFun_over a))
    (fun _ => rfl) e.left e.left_over
  right_over := suspHomotopy_over
    (fun x => (e.toFun_over (e.invFun x)).trans (e.invFun_over x))
    (fun _ => rfl) e.right e.right_over

end NearbyLagrangian.Tubes.FiberwiseHomotopyEquiv

end

noncomputable section
universe u v w


namespace NearbyLagrangian.Tubes.FiberwiseHomotopyEquiv
open ContinuousMap
variable {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]

def ofHomeomorph {p : C(X,B)} {q : C(Y,B)} (e : X ≃ₜ Y)
    (he : ∀ x, q (e x) = p x) : FiberwiseHomotopyEquiv p q where
  toFun := ⟨e,e.continuous⟩
  invFun := ⟨e.symm,e.symm.continuous⟩
  toFun_over := he
  invFun_over y := by
    change p (e.symm y) = q y
    simpa only [e.apply_symm_apply] using (he (e.symm y)).symm
  left := {
    toFun := Prod.snd
    continuous_toFun := continuous_snd
    map_zero_left := fun x => (e.symm_apply_apply x).symm
    map_one_left := fun _ => rfl }
  right := {
    toFun := Prod.snd
    continuous_toFun := continuous_snd
    map_zero_left := fun y => (e.apply_symm_apply y).symm
    map_one_left := fun _ => rfl }
  left_over _ _ := rfl
  right_over _ _ := rfl

end NearbyLagrangian.Tubes.FiberwiseHomotopyEquiv

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.RadialTopology.SphereFamily
open FiberCone
variable {B W : Type*} [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W]

def latitude (t : unitInterval) : ℝ := 2*(t:ℝ)-1
lemma latitude_range (t : unitInterval) : -1 ≤ latitude t ∧ latitude t ≤ 1 := by
  have h₀ := t.property.1
  have h₁ := t.property.2
  dsimp [latitude]
  constructor <;> linarith
lemma latitude_sq_le (t : unitInterval) : latitude t ^ 2 ≤ 1 := by
  have := latitude_range t
  nlinarith
lemma latitude_injective : Function.Injective latitude := by
  intro t s h
  apply Subtype.ext
  dsimp [latitude] at h
  linarith
@[simp] lemma latitude_zero : latitude 0 = -1 := by norm_num [latitude]
@[simp] lemma latitude_one : latitude 1 = 1 := by norm_num [latitude]

def equatorialRadius (t : unitInterval) : ℝ := Real.sqrt (1-latitude t ^ 2)
lemma equatorialRadius_nonneg (t : unitInterval) : 0 ≤ equatorialRadius t := Real.sqrt_nonneg _
lemma equatorialRadius_sq (t : unitInterval) : equatorialRadius t ^ 2 = 1-latitude t ^ 2 :=
  Real.sq_sqrt (sub_nonneg.mpr (latitude_sq_le t))
@[simp] lemma equatorialRadius_zero : equatorialRadius 0 = 0 := by simp [equatorialRadius]
@[simp] lemma equatorialRadius_one : equatorialRadius 1 = 0 := by simp [equatorialRadius]
lemma equatorialRadius_pos {t : unitInterval} (h₀ : t ≠ 0) (h₁ : t ≠ 1) :
    0 < equatorialRadius t := by
  have ht₀ : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm (Subtype.coe_ne_coe.mpr h₀))
  have ht₁ : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 (Subtype.coe_ne_coe.mpr h₁)
  apply Real.sqrt_pos.mpr
  dsimp [latitude]
  nlinarith
lemma continuous_latitude : Continuous latitude :=
  (continuous_const.mul continuous_subtype_val).sub continuous_const
lemma continuous_equatorialRadius : Continuous equatorialRadius :=
  (continuous_const.sub (continuous_latitude.pow 2)).sqrt

def southPole (A : SphereFamily B W) : C(B,A.Suspension ℝ) where
  toFun b := ⟨(b,(0,-1)),Or.inl rfl,by norm_num⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _
def northPole (A : SphereFamily B W) : C(B,A.Suspension ℝ) where
  toFun b := ⟨(b,(0,1)),Or.inl rfl,by norm_num⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk _

omit [TopologicalSpace B] in
lemma sphereMeridian_mem (A : SphereFamily B W) (z : unitInterval × A.Total) :
    (equatorialRadius z.1 • z.2.val.2 = 0 ∨
      (z.2.val.1,NormedSpace.normalize (equatorialRadius z.1 • z.2.val.2)) ∈ A.carrier) ∧
      ‖equatorialRadius z.1 • z.2.val.2‖^2 + ‖latitude z.1‖^2 = 1 := by
    constructor
    · by_cases hz : equatorialRadius z.1 = 0
      · left
        rw [hz,zero_smul]
      · right
        have hp : 0 < equatorialRadius z.1 := lt_of_le_of_ne
          (equatorialRadius_nonneg _) (Ne.symm hz)
        simpa only [NormedSpace.normalize_smul_of_pos hp,
          NormedSpace.normalize_eq_self_of_norm_eq_one (A.unit _ z.2.property)]
          using z.2.property
    · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (equatorialRadius_nonneg _),
        A.unit _ z.2.property,mul_one,Real.norm_eq_abs,sq_abs,equatorialRadius_sq]
      ring

def sphereMeridian (A : SphereFamily B W) : C(unitInterval × A.Total,A.Suspension ℝ) where
  toFun z := ⟨(z.2.val.1,(equatorialRadius z.1 • z.2.val.2,latitude z.1)),sphereMeridian_mem A z⟩
  continuous_toFun := ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
    (((continuous_equatorialRadius.comp continuous_fst).smul
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).prodMk
      (continuous_latitude.comp continuous_fst))).subtype_mk _

lemma sphereMeridian_zero (A : SphereFamily B W) (a : A.Total) :
    sphereMeridian A (0,a) = southPole A (A.projection a) := by
  apply Subtype.ext
  simp [sphereMeridian,southPole,projection]
lemma sphereMeridian_one (A : SphereFamily B W) (a : A.Total) :
    sphereMeridian A (1,a) = northPole A (A.projection a) := by
  apply Subtype.ext
  simp [sphereMeridian,northPole,projection]

def quotientSuspensionMap (A : SphereFamily B W) : C(Susp A.projection,A.Suspension ℝ) :=
  FiberCone.lift A.projection A.projection (southPole A) (sphereMeridian A)
    (northPole A) (sphereMeridian_zero A) (sphereMeridian_one A)

lemma quotientSuspensionMap_over (A : SphereFamily B W) (x : Susp A.projection) :
    A.suspensionProjection (quotientSuspensionMap A x) = suspProjection A.projection x := by
  induction x using FiberCone.induction with
  | hbase b => rfl
  | hray ta => rfl
  | hapex b => rfl

end NearbyLagrangian.RadialTopology.SphereFamily

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology unitInterval

namespace NearbyLagrangian.RadialTopology.SphereFamily
open FiberCone
variable {B W : Type*} [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma meridian_eq_of_sphereMeridian_eq (A : SphereFamily B W)
    (ta tb : unitInterval × A.Total) (h : sphereMeridian A ta = sphereMeridian A tb) :
    meridian A.projection ta = meridian A.projection tb := by
  have ht : ta.1 = tb.1 := latitude_injective (congrArg (fun p => p.val.2.2) h)
  have hb : ta.2.val.1 = tb.2.val.1 := congrArg (fun p => p.val.1) h
  by_cases h₀ : ta.1 = 0
  · have hb₀ : tb.1 = 0 := ht.symm.trans h₀
    rcases ta with ⟨t,a⟩
    rcases tb with ⟨s,b⟩
    dsimp at h₀ hb₀ hb
    subst t
    subst s
    simp only [meridian,ray_zero]
    exact congrArg (south A.projection) hb
  by_cases h₁ : ta.1 = 1
  · have hb₁ : tb.1 = 1 := ht.symm.trans h₁
    rcases ta with ⟨t,a⟩
    rcases tb with ⟨s,b⟩
    dsimp at h₁ hb₁ hb
    subst t
    subst s
    simp only [meridian,ray_one]
    exact congrArg (north A.projection) hb
  have hw : ta.2.val.2 = tb.2.val.2 := by
    apply smul_right_injective W (equatorialRadius_pos h₀ h₁).ne'
    have hx := congrArg (fun p => p.val.2.1) h
    change equatorialRadius ta.1 • ta.2.val.2 = equatorialRadius tb.1 • tb.2.val.2 at hx
    rwa [← ht] at hx
  have ha : ta.2 = tb.2 := Subtype.ext (Prod.ext hb hw)
  exact congrArg (meridian A.projection) (Prod.ext ht ha)

lemma south_eq_of_quotientSuspensionMap_eq (A : SphereFamily B W)
    (b : B) (x : Susp A.projection)
    (h : southPole A b = quotientSuspensionMap A x) : south A.projection b = x := by
  induction x using FiberCone.induction with
  | hbase c =>
    exact congrArg (south A.projection) (congrArg (fun p => p.val.1) h)
  | hray ta =>
    have ht : ta.1 = 0 := latitude_injective (by
      rw [latitude_zero]
      exact (congrArg (fun p => p.val.2.2) h).symm)
    have hb : b = ta.2.val.1 := congrArg (fun p => p.val.1) h
    rcases ta with ⟨t,a⟩
    dsimp at ht hb
    subst t
    change south A.projection b = ray A.projection A.projection (0,a)
    rw [ray_zero]
    exact congrArg (south A.projection) hb
  | hapex c =>
    have hl : (-1:ℝ) = 1 := congrArg (fun p => p.val.2.2) h
    norm_num at hl

lemma north_eq_of_quotientSuspensionMap_eq (A : SphereFamily B W)
    (b : B) (x : Susp A.projection)
    (h : northPole A b = quotientSuspensionMap A x) : north A.projection b = x := by
  induction x using FiberCone.induction with
  | hbase c =>
    have hl : (1:ℝ) = -1 := congrArg (fun p => p.val.2.2) h
    norm_num at hl
  | hray ta =>
    have ht : ta.1 = 1 := latitude_injective (by
      rw [latitude_one]
      exact (congrArg (fun p => p.val.2.2) h).symm)
    have hb : b = ta.2.val.1 := congrArg (fun p => p.val.1) h
    rcases ta with ⟨t,a⟩
    dsimp at ht hb
    subst t
    change north A.projection b = ray A.projection A.projection (1,a)
    rw [ray_one]
    exact congrArg (north A.projection) hb
  | hapex c =>
    exact congrArg (north A.projection) (congrArg (fun p => p.val.1) h)

theorem quotientSuspensionMap_injective (A : SphereFamily B W) :
    Function.Injective (quotientSuspensionMap A) := by
  intro x y h
  induction x using FiberCone.induction with
  | hbase b => exact south_eq_of_quotientSuspensionMap_eq A b y h
  | hapex b => exact north_eq_of_quotientSuspensionMap_eq A b y h
  | hray ta =>
    induction y using FiberCone.induction with
    | hbase b => exact (south_eq_of_quotientSuspensionMap_eq A b _ h.symm).symm
    | hapex b => exact (north_eq_of_quotientSuspensionMap_eq A b _ h.symm).symm
    | hray tb => exact meridian_eq_of_sphereMeridian_eq A ta tb h

theorem quotientSuspensionMap_surjective (A : SphereFamily B W) :
    Function.Surjective (quotientSuspensionMap A) := by
  intro p
  have hs : ‖p.val.2.1‖^2 + p.val.2.2^2 = 1 := by
    simpa only [Real.norm_eq_abs,sq_abs] using p.property.2
  have hz₀ : -1 ≤ p.val.2.2 := by nlinarith [sq_nonneg ‖p.val.2.1‖]
  have hz₁ : p.val.2.2 ≤ 1 := by nlinarith [sq_nonneg ‖p.val.2.1‖]
  by_cases hw : p.val.2.1 = 0
  · have hz : p.val.2.2 = -1 ∨ p.val.2.2 = 1 := by
      rw [hw,norm_zero] at hs
      rcases le_or_gt p.val.2.2 0 with h | h
      · left; nlinarith
      · right; nlinarith
    rcases hz with hz | hz
    · refine ⟨south A.projection p.val.1,?_⟩
      apply Subtype.ext
      change (p.val.1,(0,-1)) = p.val
      exact Prod.ext rfl (Prod.ext hw.symm hz.symm)
    · refine ⟨north A.projection p.val.1,?_⟩
      apply Subtype.ext
      change (p.val.1,(0,1)) = p.val
      exact Prod.ext rfl (Prod.ext hw.symm hz.symm)
  · let t : unitInterval := ⟨(p.val.2.2+1)/2,by constructor <;> linarith⟩
    let a : A.Total := ⟨(p.val.1,NormedSpace.normalize p.val.2.1),p.property.1.resolve_left hw⟩
    have ht : latitude t = p.val.2.2 := by dsimp [latitude,t]; ring
    have hr : equatorialRadius t = ‖p.val.2.1‖ := by
      have hsq := equatorialRadius_sq t
      rw [ht] at hsq
      nlinarith [equatorialRadius_nonneg t,norm_nonneg p.val.2.1]
    refine ⟨meridian A.projection (t,a),?_⟩
    apply Subtype.ext
    change (p.val.1,(equatorialRadius t • NormedSpace.normalize p.val.2.1,latitude t)) = p.val
    have hv : equatorialRadius t • NormedSpace.normalize p.val.2.1 = p.val.2.1 := by
      rw [hr,NormedSpace.norm_smul_normalize]
    exact Prod.ext rfl (Prod.ext hv ht)

def quotientSuspensionEquiv (A : SphereFamily B W) : Susp A.projection ≃ A.Suspension ℝ :=
  Equiv.ofBijective (quotientSuspensionMap A)
    ⟨quotientSuspensionMap_injective A,quotientSuspensionMap_surjective A⟩

def quotientSuspensionHomeomorph [CompactSpace B] [T2Space B] (A : SphereFamily B W)
    [CompactSpace A.Total] : Susp A.projection ≃ₜ A.Suspension ℝ := by
  letI : CompactSpace (Raw B A.Total B) := inferInstance
  letI : CompactSpace (Susp A.projection) := Quot.compactSpace
  exact Continuous.homeoOfEquivCompactToT2 (f:=quotientSuspensionEquiv A)
    (quotientSuspensionMap A).continuous

lemma quotientSuspensionHomeomorph_over [CompactSpace B] [T2Space B] (A : SphereFamily B W)
    [CompactSpace A.Total] (x : Susp A.projection) :
    A.suspensionProjection (quotientSuspensionHomeomorph A x) = suspProjection A.projection x :=
  quotientSuspensionMap_over A x

end NearbyLagrangian.RadialTopology.SphereFamily

end

end OAI
