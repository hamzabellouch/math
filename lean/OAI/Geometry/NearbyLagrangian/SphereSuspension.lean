import Mathlib
import OAI.Geometry.NearbyLagrangian.Stabilization
import OAI.Geometry.NearbyLagrangian.CotangentModel

namespace OAI

/-! Continuous radial lifts and fiberwise suspension of sphere families. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialTopology
open Set Filter
open scoped Topology
variable {X W : Type*} [TopologicalSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]

def radialLift (r : X → ℝ) (a : {x : X // r x ≠ 0} → W) (x : X) : W :=
  if h : r x = 0 then 0 else r x • a ⟨x,h⟩

omit [TopologicalSpace X] in
lemma radialLift_of_zero (r : X → ℝ) (a : {x : X // r x ≠ 0} → W)
    {x : X} (h : r x = 0) : radialLift r a x = 0 := dite_eq_left h

omit [TopologicalSpace X] in
lemma radialLift_of_ne_zero (r : X → ℝ) (a : {x : X // r x ≠ 0} → W)
    {x : X} (h : r x ≠ 0) : radialLift r a x = r x • a ⟨x,h⟩ := dite_eq_right h

omit [TopologicalSpace X] in
lemma norm_radialLift_le (r : X → ℝ) (a : {x : X // r x ≠ 0} → W)
    {M : ℝ} (ha : ∀ x, ‖a x‖ ≤ M) (x : X) :
    ‖radialLift r a x‖ ≤ |r x| * M := by
  by_cases hx : r x = 0
  · simp [radialLift,hx]
  · rw [radialLift_of_ne_zero r a hx,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (ha ⟨x,hx⟩) (abs_nonneg _)

theorem continuous_radialLift {r : X → ℝ} (hr : Continuous r)
    {a : {x : X // r x ≠ 0} → W} (ha : Continuous a)
    {M : ℝ} (hbound : ∀ x, ‖a x‖ ≤ M) :
    Continuous (radialLift r a) := by
  have haway : ContinuousOn (radialLift r a) {x | r x ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun x : {x : X // r x ≠ 0} => radialLift r a x) =
        fun x : {x : X // r x ≠ 0} => r x • a x := by
      funext x
      exact radialLift_of_ne_zero r a x.property
    change Continuous (fun x : {x : X // r x ≠ 0} => radialLift r a x)
    rw [he]
    exact (hr.comp continuous_subtype_val).smul ha
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : r x = 0
  · rw [ContinuousAt,radialLift_of_zero r a hx]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun z => norm_nonneg _) (norm_radialLift_le r a hbound)
    have hc : Continuous (fun t => |r t| * M) := hr.abs.mul continuous_const
    simpa only [hx,abs_zero,zero_mul] using hc.tendsto x
  · exact (haway x hx).continuousAt ((isOpen_ne_fun hr continuous_const).mem_nhds hx)

omit [TopologicalSpace X] in
lemma norm_radialLift (r : X → ℝ) (a : {x : X // r x ≠ 0} → W)
    (ha : ∀ x, ‖a x‖ = 1) (x : X) : ‖radialLift r a x‖ = |r x| := by
  by_cases hx : r x = 0
  · simp [radialLift,hx]
  · rw [radialLift_of_ne_zero r a hx,norm_smul,Real.norm_eq_abs,ha,mul_one]

end NearbyLagrangian.RadialTopology

namespace NearbyLagrangian.RadialTopology
open Set Filter
open scoped Topology

structure SphereFamily (B W : Type*) [NormedAddCommGroup W] where
  carrier : Set (B × W)
  unit : ∀ p ∈ carrier, ‖p.2‖ = 1

namespace SphereFamily
variable {B W W' Z T : Type*} [TopologicalSpace B] [TopologicalSpace T]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [NormedAddCommGroup Z]

abbrev Total (A : SphereFamily B W) := A.carrier

def projection (A : SphereFamily B W) : C(A.Total,B) :=
  ⟨fun p => p.val.1,continuous_fst.comp continuous_subtype_val⟩

abbrev Suspension (A : SphereFamily B W) (Z : Type*) [NormedAddCommGroup Z] :=
  {p : B × (W × Z) //
    (p.2.1 = 0 ∨ (p.1,NormedSpace.normalize p.2.1) ∈ A.carrier) ∧
      ‖p.2.1‖^2 + ‖p.2.2‖^2 = 1}

def suspensionProjection (A : SphereFamily B W) : C(A.Suspension Z,B) :=
  ⟨fun p => p.val.1,continuous_fst.comp continuous_subtype_val⟩

def direction (A : SphereFamily B W) (p : {p : A.Suspension Z // ‖p.val.2.1‖ ≠ 0}) :
    A.Total :=
  ⟨(p.val.val.1,NormedSpace.normalize p.val.val.2.1),
    p.val.property.1.resolve_left (norm_ne_zero_iff.mp p.property)⟩

lemma continuous_direction (A : SphereFamily B W) :
    Continuous (A.direction (Z:=Z)) := by
  have hv : Continuous (fun p : {p : A.Suspension Z // ‖p.val.2.1‖ ≠ 0} => p.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  apply Continuous.subtype_mk
  exact hv.fst.prodMk ((hv.snd.fst.norm.inv₀ (fun p => p.property)).smul hv.snd.fst)

def suspendedVector {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) (q : T × A.Suspension Z) : W' :=
  radialLift (fun q : T × A.Suspension Z => ‖q.2.val.2.1‖)
    (fun q => (e (q.val.1,A.direction ⟨q.val.2,q.property⟩)).val.2) q

lemma norm_suspendedVector {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) (q : T × A.Suspension Z) :
    ‖suspendedVector e q‖ = ‖q.2.val.2.1‖ := by
  unfold suspendedVector
  rw [norm_radialLift _ _ (fun q => C.unit _ (e _).property),abs_of_nonneg (norm_nonneg _)]

lemma continuous_suspendedVector {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) : Continuous (suspendedVector (Z:=Z) e) := by
  have hv : Continuous (fun q : T × A.Suspension Z => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  unfold suspendedVector
  apply continuous_radialLift hv.snd.fst.norm
  · have hq : Continuous (fun q : {q : T × A.Suspension Z // ‖q.2.val.2.1‖ ≠ 0} =>
        (⟨q.val.2,q.property⟩ : {p : A.Suspension Z // ‖p.val.2.1‖ ≠ 0})) :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    exact continuous_snd.comp (continuous_subtype_val.comp
      (e.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
        (A.continuous_direction.comp hq))))
  · intro q
    exact (C.unit _ (e _).property).le

lemma suspendedVector_zero {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) {q : T × A.Suspension Z} (hq : q.2.val.2.1 = 0) :
    suspendedVector e q = 0 := by
  apply norm_eq_zero.mp
  rw [norm_suspendedVector,hq,norm_zero]

lemma suspendedVector_nonzero {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) {q : T × A.Suspension Z} (hq : q.2.val.2.1 ≠ 0) :
    suspendedVector e q = ‖q.2.val.2.1‖ •
      (e (q.1,A.direction ⟨q.2,norm_ne_zero_iff.mpr hq⟩)).val.2 := by
  unfold suspendedVector
  exact radialLift_of_ne_zero (fun p : T × A.Suspension Z => ‖p.2.val.2.1‖) _
    (x:=q) (norm_ne_zero_iff.mpr hq)

def suspend {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) (he : ∀ t x, (e (t,x)).val.1 = x.val.1) :
    C(T × A.Suspension Z,C.Suspension Z) where
  toFun q := ⟨(q.2.val.1,suspendedVector e q,q.2.val.2.2),by
    constructor
    · by_cases hq : q.2.val.2.1 = 0
      · exact Or.inl (suspendedVector_zero e hq)
      · right
        rw [suspendedVector_nonzero e hq,NormedSpace.normalize_smul_of_pos (norm_pos_iff.mpr hq),
          NormedSpace.normalize_eq_self_of_norm_eq_one (C.unit _ (e _).property)]
        have hbase := he q.1 (A.direction ⟨q.2,norm_ne_zero_iff.mpr hq⟩)
        change (e _).val.1 = q.2.val.1 at hbase
        rw [← hbase]
        exact (e _).property
    · rw [norm_suspendedVector]
      exact q.2.property.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hv : Continuous (fun q : T × A.Suspension Z => q.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact hv.fst.prodMk ((continuous_suspendedVector e).prodMk hv.snd.snd)

@[simp] lemma suspend_base {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) (he : ∀ t x, (e (t,x)).val.1 = x.val.1)
    (q : T × A.Suspension Z) : (suspend e he q).val.1 = q.2.val.1 := rfl

@[simp] lemma suspend_latitude {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(T × A.Total,C.Total)) (he : ∀ t x, (e (t,x)).val.1 = x.val.1)
    (q : T × A.Suspension Z) : (suspend e he q).val.2.2 = q.2.val.2.2 := rfl

end SphereFamily
end NearbyLagrangian.RadialTopology

namespace NearbyLagrangian.RadialTopology.SphereFamily
open Set
open scoped Topology
variable {B W W' W'' Z : Type*} [TopologicalSpace B]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W']
  [NormedAddCommGroup W''] [NormedSpace ℝ W''] [NormedAddCommGroup Z]

def suspendMap {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(A.Total,C.Total)) (he : ∀ x, (e x).val.1 = x.val.1) :
    C(A.Suspension Z,C.Suspension Z) :=
  (suspend (⟨fun q : Unit × A.Total => e q.2,
    e.continuous.comp continuous_snd⟩ : C(Unit × A.Total,C.Total)) (fun _ x => he x)).comp
      ⟨fun x => ((),x),continuous_const.prodMk continuous_id⟩

@[simp] lemma suspendMap_base {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(A.Total,C.Total)) (he : ∀ x, (e x).val.1 = x.val.1) (q : A.Suspension Z) :
    (suspendMap e he q).val.1 = q.val.1 := rfl

@[simp] lemma suspendMap_latitude {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(A.Total,C.Total)) (he : ∀ x, (e x).val.1 = x.val.1) (q : A.Suspension Z) :
    (suspendMap e he q).val.2.2 = q.val.2.2 := rfl

lemma norm_suspendMap_vector {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(A.Total,C.Total)) (he : ∀ x, (e x).val.1 = x.val.1) (q : A.Suspension Z) :
    ‖(suspendMap e he q).val.2.1‖ = ‖q.val.2.1‖ := norm_suspendedVector _ _

lemma suspendMap_vector_zero {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(A.Total,C.Total)) (he : ∀ x, (e x).val.1 = x.val.1) {q : A.Suspension Z}
    (hq : q.val.2.1 = 0) : (suspendMap e he q).val.2.1 = 0 :=
  suspendedVector_zero _ hq

lemma suspendMap_vector_nonzero {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(A.Total,C.Total)) (he : ∀ x, (e x).val.1 = x.val.1) {q : A.Suspension Z}
    (hq : q.val.2.1 ≠ 0) : (suspendMap e he q).val.2.1 =
      ‖q.val.2.1‖ • (e (A.direction ⟨q,norm_ne_zero_iff.mpr hq⟩)).val.2 :=
  suspendedVector_nonzero _ hq

lemma suspendMap_direction {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : C(A.Total,C.Total)) (he : ∀ x, (e x).val.1 = x.val.1) {q : A.Suspension Z}
    (hq : ‖q.val.2.1‖ ≠ 0) :
    C.direction ⟨suspendMap e he q,by rw [norm_suspendMap_vector]; exact hq⟩ =
      e (A.direction ⟨q,hq⟩) := by
  apply Subtype.ext
  apply Prod.ext
  · change q.val.1 = (e (A.direction ⟨q,hq⟩)).val.1
    exact (he (A.direction ⟨q,hq⟩)).symm
  · change NormedSpace.normalize (suspendMap e he q).val.2.1 = _
    rw [suspendMap_vector_nonzero e he (norm_ne_zero_iff.mp hq),
      NormedSpace.normalize_smul_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hq)),
      NormedSpace.normalize_eq_self_of_norm_eq_one (C.unit _ (e _).property)]

lemma suspendMap_id (A : SphereFamily B W) :
    suspendMap (Z:=Z) (ContinuousMap.id A.Total) (fun _ => rfl) =
      ContinuousMap.id (A.Suspension Z) := by
  ext q : 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  apply Prod.ext
  swap
  · rfl
  by_cases hq : q.val.2.1 = 0
  · exact (suspendMap_vector_zero (ContinuousMap.id A.Total) (fun _ => rfl) hq).trans hq.symm
  · exact (suspendMap_vector_nonzero (ContinuousMap.id A.Total) (fun _ => rfl) hq).trans
      (NormedSpace.norm_smul_normalize _)

lemma suspendMap_comp {A : SphereFamily B W} {C : SphereFamily B W'}
    {D : SphereFamily B W''} (e : C(A.Total,C.Total)) (f : C(C.Total,D.Total))
    (he : ∀ x, (e x).val.1 = x.val.1) (hf : ∀ x, (f x).val.1 = x.val.1) :
    suspendMap (Z:=Z) (f.comp e) (fun x => (hf _).trans (he x)) =
      (suspendMap f hf).comp (suspendMap e he) := by
  ext q : 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  apply Prod.ext
  swap
  · rfl
  change (suspendMap (f.comp e) _ q).val.2.1 =
    (suspendMap f hf (suspendMap e he q)).val.2.1
  by_cases hq : q.val.2.1 = 0
  · rw [suspendMap_vector_zero _ _ hq,
      suspendMap_vector_zero _ _ (suspendMap_vector_zero _ _ hq)]
  · have hn : (suspendMap e he q).val.2.1 ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [norm_suspendMap_vector]
      exact norm_ne_zero_iff.mpr hq
    rw [suspendMap_vector_nonzero _ _ hq,suspendMap_vector_nonzero _ _ hn,
      suspendMap_direction,norm_suspendMap_vector]
    rfl

def suspendHomotopy {A : SphereFamily B W} {C : SphereFamily B W'}
    {e f : C(A.Total,C.Total)}
    (he : ∀ x, (e x).val.1 = x.val.1) (hf : ∀ x, (f x).val.1 = x.val.1)
    (H : e.Homotopy f) (hH : ∀ t x, (H (t,x)).val.1 = x.val.1) :
    (suspendMap (Z:=Z) e he).Homotopy (suspendMap f hf) where
  toFun := suspend H.toContinuousMap hH
  continuous_toFun := (suspend H.toContinuousMap hH).continuous
  map_zero_left q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Prod.ext
    swap
    · rfl
    change suspendedVector H.toContinuousMap (0,q) = (suspendMap e he q).val.2.1
    by_cases hq : q.val.2.1 = 0
    · rw [suspendedVector_zero _ hq,suspendMap_vector_zero _ _ hq]
    · rw [suspendedVector_nonzero _ hq,suspendMap_vector_nonzero _ _ hq]
      exact congrArg (fun x : C.Total => ‖q.val.2.1‖ • x.val.2) (H.apply_zero _)
  map_one_left q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    apply Prod.ext
    swap
    · rfl
    change suspendedVector H.toContinuousMap (1,q) = (suspendMap f hf q).val.2.1
    by_cases hq : q.val.2.1 = 0
    · rw [suspendedVector_zero _ hq,suspendMap_vector_zero _ _ hq]
    · rw [suspendedVector_nonzero _ hq,suspendMap_vector_nonzero _ _ hq]
      exact congrArg (fun x : C.Total => ‖q.val.2.1‖ • x.val.2) (H.apply_one _)

@[simp] lemma suspendHomotopy_base {A : SphereFamily B W} {C : SphereFamily B W'}
    {e f : C(A.Total,C.Total)}
    (he : ∀ x, (e x).val.1 = x.val.1) (hf : ∀ x, (f x).val.1 = x.val.1)
    (H : e.Homotopy f) (hH : ∀ t x, (H (t,x)).val.1 = x.val.1)
    (t : unitInterval) (q : A.Suspension Z) :
    (suspendHomotopy he hf H hH (t,q)).val.1 = q.val.1 := rfl

end NearbyLagrangian.RadialTopology.SphereFamily

namespace NearbyLagrangian.RadialTopology.SphereFamily
open scoped Topology
variable {B W W' Z : Type*} [TopologicalSpace B]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [NormedAddCommGroup Z]

def suspendFiberwise {A : SphereFamily B W} {C : SphereFamily B W'}
    (e : Tubes.FiberwiseHomotopyEquiv A.projection C.projection) :
    Tubes.FiberwiseHomotopyEquiv (A.suspensionProjection (Z:=Z))
      (C.suspensionProjection (Z:=Z)) where
  toFun := suspendMap e.toFun e.toFun_over
  invFun := suspendMap e.invFun e.invFun_over
  toFun_over _ := rfl
  invFun_over _ := rfl
  left := (suspendHomotopy (A:=A) (C:=A) (e:=e.invFun.comp e.toFun)
    (f:=ContinuousMap.id A.Total) (fun x => (e.invFun_over _).trans (e.toFun_over x))
    (fun _ => rfl) e.left e.left_over).cast
      (suspendMap_comp e.toFun e.invFun e.toFun_over e.invFun_over) (suspendMap_id A)
  right := (suspendHomotopy (A:=C) (C:=C) (e:=e.toFun.comp e.invFun)
    (f:=ContinuousMap.id C.Total) (fun x => (e.toFun_over _).trans (e.invFun_over x))
    (fun _ => rfl) e.right e.right_over).cast
      (suspendMap_comp e.invFun e.toFun e.invFun_over e.toFun_over) (suspendMap_id C)
  left_over _ _ := rfl
  right_over _ _ := rfl

end NearbyLagrangian.RadialTopology.SphereFamily

end

end OAI
