import Mathlib
import OAI.Geometry.NearbyLagrangian.SuspensionEquivalence

namespace OAI

/-! Stable fiber families and the negative spherical class. -/

noncomputable section
universe u v w
open scoped Topology

namespace NearbyLagrangian
open FiberCone Tubes

structure FiberFamily (B : Type u) [TopologicalSpace B] where
  Total : Type u
  topology : TopologicalSpace Total
  projection : @ContinuousMap Total B topology _

attribute [instance] FiberFamily.topology

namespace FiberFamily
variable {B : Type u} [TopologicalSpace B]

def ofProjection {X : Type u} [TopologicalSpace X] (p : C(X,B)) : FiberFamily B :=
  ⟨X,inferInstance,p⟩

def suspend (A : FiberFamily B) : FiberFamily B :=
  ofProjection (suspProjection A.projection)

def iterate (A : FiberFamily B) : ℕ → FiberFamily B
  | 0 => A
  | n+1 => (iterate A n).suspend

@[simp] lemma iterate_zero (A : FiberFamily B) : A.iterate 0 = A := rfl
@[simp] lemma iterate_succ (A : FiberFamily B) (n : ℕ) :
    A.iterate (n+1) = (A.iterate n).suspend := rfl

lemma iterate_add (A : FiberFamily B) (n m : ℕ) :
    A.iterate (n+m) = (A.iterate n).iterate m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Nat.add_succ,iterate_succ,ih]

lemma suspend_iterate (A : FiberFamily B) (n : ℕ) :
    A.suspend.iterate n = (A.iterate n).suspend := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate_succ,ih]

def Equiv (A C : FiberFamily B) : Prop :=
  Nonempty (FiberwiseHomotopyEquiv A.projection C.projection)

namespace Equiv
@[refl] theorem refl (A : FiberFamily B) : Equiv A A := ⟨.refl _⟩
@[symm] theorem symm {A C : FiberFamily B} (h : Equiv A C) : Equiv C A := by
  obtain ⟨h⟩ := h
  exact ⟨h.symm⟩
@[trans] theorem trans {A C D : FiberFamily B} (h : Equiv A C) (k : Equiv C D) :
    Equiv A D := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨h.trans k⟩

theorem suspend {A C : FiberFamily B} (h : Equiv A C) : Equiv A.suspend C.suspend := by
  obtain ⟨h⟩ := h
  exact ⟨h.suspension⟩

theorem iterate {A C : FiberFamily B} (h : Equiv A C) (n : ℕ) :
    Equiv (A.iterate n) (C.iterate n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.suspend
end Equiv

def StableEquiv (A C : FiberFamily B) : Prop :=
  ∃ n : ℕ, Equiv (A.iterate n) (C.iterate n)

namespace StableEquiv
@[refl] theorem refl (A : FiberFamily B) : StableEquiv A A := ⟨0,.refl A⟩
@[symm] theorem symm {A C : FiberFamily B} (h : StableEquiv A C) : StableEquiv C A := by
  obtain ⟨n,h⟩ := h
  exact ⟨n,h.symm⟩

@[trans] theorem trans {A C D : FiberFamily B} (h : StableEquiv A C)
    (k : StableEquiv C D) : StableEquiv A D := by
  obtain ⟨n,h⟩ := h
  obtain ⟨m,k⟩ := k
  refine ⟨n+m,?_⟩
  have h' := h.iterate m
  have k' := k.iterate n
  rw [← iterate_add,← iterate_add] at h'
  rw [← iterate_add,← iterate_add,Nat.add_comm m n] at k'
  exact h'.trans k'

theorem suspend {A C : FiberFamily B} (h : StableEquiv A C) :
    StableEquiv A.suspend C.suspend := by
  obtain ⟨n,h⟩ := h
  refine ⟨n,?_⟩
  rw [suspend_iterate,suspend_iterate]
  exact h.suspend

theorem of_suspend {A C : FiberFamily B} (h : StableEquiv A.suspend C.suspend) :
    StableEquiv A C := by
  obtain ⟨n,h⟩ := h
  refine ⟨n+1,?_⟩
  simpa only [suspend_iterate,iterate_succ] using h

@[simp] theorem suspend_iff (A C : FiberFamily B) :
    StableEquiv A.suspend C.suspend ↔ StableEquiv A C := ⟨of_suspend,suspend⟩

@[simp] theorem iterate_iff (A C : FiberFamily B) (n : ℕ) :
    StableEquiv (A.iterate n) (C.iterate n) ↔ StableEquiv A C := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterate_succ,suspend_iff] using ih
end StableEquiv

theorem Equiv.stable {A C : FiberFamily B} (h : Equiv A C) : StableEquiv A C := ⟨0,h⟩

end FiberFamily
end NearbyLagrangian

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology Manifold ContDiff

namespace NearbyLagrangian
open FiberCone Tubes RadialTopology

namespace RadialTopology
variable {B W : Type} [TopologicalSpace B] [NormedAddCommGroup W]

lemma isCompact_negativeSphere [CompactSpace B] [ProperSpace W]
    {f : B → W → ℝ} (hf : Continuous (Function.uncurry f)) :
    IsCompact (negativeSphere f).carrier := by
  have hc : IsClosed (negativeSphere f).carrier :=
    (isClosed_eq continuous_snd.norm continuous_const).inter (isClosed_le hf continuous_const)
  apply (isCompact_univ.prod (isCompact_sphere (0:W) 1)).of_isClosed_subset hc
  intro z hz
  exact ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hz.1⟩

lemma isCompact_fullSphere [CompactSpace B] [ProperSpace W] :
    IsCompact (fullSphere B W).carrier := by
  have he : (fullSphere B W).carrier = Set.univ ×ˢ Metric.sphere (0:W) 1 := by
    ext z
    change (‖z.2‖=1) ↔ (z.1 ∈ Set.univ ∧ z.2 ∈ Metric.sphere 0 1)
    simp only [mem_univ,true_and,Metric.mem_sphere,dist_zero_right]
  rw [he]
  exact isCompact_univ.prod (isCompact_sphere (0:W) 1)

def sphereFiberFamily (A : SphereFamily B W) : FiberFamily B :=
  .ofProjection A.projection

def suspendedSphereFiberFamily [NormedSpace ℝ W] (A : SphereFamily B W) : FiberFamily B :=
  .ofProjection (A.suspensionProjection (Z:=ℝ))

lemma sphereFiberFamily_suspend [NormedSpace ℝ W] [CompactSpace B] [T2Space B]
    (A : SphereFamily B W) [CompactSpace A.Total] :
    FiberFamily.Equiv (sphereFiberFamily A).suspend (suspendedSphereFiberFamily A) :=
  ⟨FiberwiseHomotopyEquiv.ofHomeomorph A.quotientSuspensionHomeomorph
    A.quotientSuspensionHomeomorph_over⟩
end RadialTopology

namespace Tubes
variable {B : Type} [TopologicalSpace B]

def angularFamily {k l : ℕ} (a : C(B,Tube k l)) : FiberFamily B :=
  sphereFiberFamily (negativeSphere (fun b w => (a b).val w))

def roundFamily (B : Type) [TopologicalSpace B] (k : ℕ) : FiberFamily B :=
  sphereFiberFamily (fullSphere B (Euclidean k))

lemma angularFamily_addPositive {k l : ℕ} (a : C(B,Tube k l)) :
    FiberFamily.Equiv (angularFamily a) (angularFamily ((addPositiveOne k l).comp a)) := by
  let hE := positiveSquareCoordinatesEquiv
    (fun b r hr w => (a b).val.homogeneity_nonneg hr w)
    (positiveSquareCoordinates k l) (positiveSquareCoordinates_norm_sq k l)
  have hg : (fun b w => (((addPositiveOne k l).comp a) b).val w) =
      (fun b w => (a b).val (positiveSquareCoordinates k l w).1+
        (positiveSquareCoordinates k l w).2^2) := by
    funext b w
    exact addPositiveOne_apply k l (a b) w
  change Nonempty (FiberwiseHomotopyEquiv _ (negativeSphere _).projection)
  rw [hg]
  exact ⟨hE⟩

variable [CompactSpace B] [T2Space B]

lemma roundFamily_succ (k : ℕ) :
    FiberFamily.Equiv (roundFamily B k).suspend (roundFamily B (k+1)) := by
  let A := fullSphere B (Euclidean k)
  let : CompactSpace A.Total := isCompact_iff_compactSpace.mp isCompact_fullSphere
  let e := suspensionFullSphereHomeomorph (B:=B) (positiveSquareCoordinates k 0)
    (positiveSquareCoordinates_norm_sq k 0)
  have h : FiberFamily.Equiv (suspendedSphereFiberFamily A) (roundFamily B (k+1)) :=
    ⟨FiberwiseHomotopyEquiv.ofHomeomorph e (fun _ => rfl)⟩
  exact (sphereFiberFamily_suspend A).trans h

lemma roundFamily_iterate (k n : ℕ) :
    FiberFamily.Equiv ((roundFamily B k).iterate n) (roundFamily B (k+n)) := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact ih.suspend.trans (roundFamily_succ (k+n))

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]

include V in
lemma angularFamily_addNegative {k l : ℕ} (hdim : 0 < k+l) (a : C(B,Tube k l)) :
    FiberFamily.Equiv (angularFamily a).suspend
      (angularFamily ((addNegativeOne k l).comp a)) := by
  let : NeZero (k+l) := ⟨by omega⟩
  let : NeZero ((k+1)+l) := ⟨by omega⟩
  let f : C(B,RegularHomogeneous (Euclidean (k+l))) :=
    ⟨fun b => (a b).val,continuous_subtype_val.comp a.continuous⟩
  obtain ⟨hE⟩ := RegularHomogeneous.negativeSquare_equiv (V:=V) f
    (negativeSquareCoordinates k l) (negativeSquareCoordinates_norm_sq k l)
  have hg : (fun b w => (((addNegativeOne k l).comp a) b).val w) =
      (fun b w => (a b).val (negativeSquareCoordinates k l w).1-
        (negativeSquareCoordinates k l w).2^2) := by
    funext b w
    exact addNegativeOne_apply k l (a b) w
  let N := negativeSphere (fun b w => (a b).val w)
  have hN : Continuous (Function.uncurry (fun b w => (a b).val w)) :=
    RegularHomogeneous.continuous_eval.comp
      ((continuous_subtype_val.comp (a.continuous.comp continuous_fst)).prodMk continuous_snd)
  let : CompactSpace N.Total := isCompact_iff_compactSpace.mp (isCompact_negativeSphere hN)
  have hn : FiberFamily.Equiv (suspendedSphereFiberFamily N)
      (angularFamily ((addNegativeOne k l).comp a)) := by
    change Nonempty (FiberwiseHomotopyEquiv _ (negativeSphere _).projection)
    rw [hg]
    exact ⟨hE⟩
  exact (sphereFiberFamily_suspend N).trans hn

include V in

theorem angularFamily_stabilize {m : ℕ} (hm : 0 < m) (a : C(B,Tube m m)) :
    FiberFamily.Equiv (angularFamily a).suspend
      (angularFamily ((stabilize m).comp a)) := by
  rw [← addPositiveNegative_eq_stabilize]
  exact (angularFamily_addNegative (V:=V) (by omega : 0 < m+m) a).trans
    (angularFamily_addPositive ((addNegativeOne m m).comp a))

include V in

theorem angularFamily_stabilizeFor {m : ℕ} (hm : 0 < m) (a : C(B,Tube m m)) (r : ℕ) :
    FiberFamily.Equiv ((angularFamily a).iterate r)
      (angularFamily ((stabilizeFor m r).comp a)) := by
  induction r with
  | zero => exact .refl _
  | succ r ih =>
    exact ih.suspend.trans (angularFamily_stabilize (V:=V) (by omega : 0 < m+r)
      ((stabilizeFor m r).comp a))

include V in

theorem StableNegativeTrivial.finite_spherical {m : ℕ} (hm : 0 < m)
    {a : C(B,Tube m m)} (ha : StableNegativeTrivial a) :
    FiberFamily.StableEquiv (angularFamily a) (roundFamily B m) := by
  obtain ⟨r,hr⟩ := ha
  have h : FiberFamily.Equiv (angularFamily ((stabilizeFor m r).comp a))
      (roundFamily B (m+r)) := (negativeTrivial_iff_sphere _).mp hr
  exact ⟨r,(angularFamily_stabilizeFor (V:=V) hm a r).trans
    (h.trans (roundFamily_iterate m r).symm)⟩

end Tubes
end NearbyLagrangian

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology Manifold ContDiff

namespace NearbyLagrangian
namespace FiberFamily
variable {B : Type u} [TopologicalSpace B]

abbrev Graded (B : Type u) [TopologicalSpace B] := ℕ × FiberFamily B

def Graded.Rel (A C : Graded B) : Prop :=
  StableEquiv (A.2.iterate C.1) (C.2.iterate A.1)

namespace Graded.Rel
@[refl] theorem refl (A : Graded B) : A.Rel A := StableEquiv.refl _
@[symm] theorem symm {A C : Graded B} (h : A.Rel C) : C.Rel A := StableEquiv.symm h
@[trans] theorem trans {A C D : Graded B} (h : A.Rel C) (k : C.Rel D) : A.Rel D := by
  have h' := (StableEquiv.iterate_iff _ _ D.1).mpr h
  have k' := (StableEquiv.iterate_iff _ _ A.1).mpr k
  rw [← iterate_add,← iterate_add] at h' k'
  rw [Nat.add_comm D.1 A.1] at k'
  have t := h'.trans k'
  rw [Nat.add_comm C.1 D.1,Nat.add_comm C.1 A.1,iterate_add,iterate_add] at t
  exact (StableEquiv.iterate_iff _ _ C.1).mp t
end Graded.Rel

def gradedSetoid (B : Type u) [TopologicalSpace B] : Setoid (Graded B) where
  r := Graded.Rel
  iseqv := ⟨Graded.Rel.refl,Graded.Rel.symm,Graded.Rel.trans⟩

abbrev StableClass (B : Type u) [TopologicalSpace B] := Quotient (gradedSetoid B)

def classOf (n : ℕ) (A : FiberFamily B) : StableClass B := Quotient.mk (gradedSetoid B) (n,A)

theorem classOf_eq_iff (n m : ℕ) (A C : FiberFamily B) :
    classOf n A = classOf m C ↔ StableEquiv (A.iterate m) (C.iterate n) := Quotient.eq

theorem classOf_sameGrade (n : ℕ) (A C : FiberFamily B) :
    classOf n A = classOf n C ↔ StableEquiv A C := by
  rw [classOf_eq_iff,StableEquiv.iterate_iff]

theorem classOf_suspend (n : ℕ) (A : FiberFamily B) :
    classOf (n+1) A.suspend = classOf n A := by
  rw [classOf_eq_iff,suspend_iterate,iterate_succ]

theorem classOf_equiv (n : ℕ) {A C : FiberFamily B} (h : Equiv A C) :
    classOf n A = classOf n C := (classOf_sameGrade _ _ _).mpr h.stable

end FiberFamily

namespace Tubes
variable {B V : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]

include V in
theorem stableNegativeTrivial_iff_finite_spherical {m : ℕ} (hm : 0 < m)
    (a : C(B,Tube m m)) : StableNegativeTrivial a ↔
      FiberFamily.StableEquiv (angularFamily a) (roundFamily B m) := by
  refine ⟨fun h => h.finite_spherical (V:=V) hm,?_⟩
  rintro ⟨r,h⟩
  refine ⟨r,(negativeTrivial_iff_sphere _).mpr ?_⟩
  exact (angularFamily_stabilizeFor (V:=V) hm a r).symm.trans
    (h.trans (roundFamily_iterate m r))

def standardSphericalClass (B : Type) [TopologicalSpace B] : FiberFamily.StableClass B :=
  FiberFamily.classOf 0 (roundFamily B 0)

theorem round_family_class (m : ℕ) :
    FiberFamily.classOf m (roundFamily B m) = standardSphericalClass B := by
  apply (FiberFamily.classOf_eq_iff _ _ _ _).mpr
  simpa only [Nat.zero_add,FiberFamily.iterate_zero] using
    (roundFamily_iterate (B:=B) 0 m).symm.stable

def negativeStableClass {m : ℕ} (a : C(B,Tube m m)) : FiberFamily.StableClass B :=
  FiberFamily.classOf (m+1) (angularFamily ((stabilize m).comp a))

include V in
theorem negativeStableClass_eq {m : ℕ} (hm : 0 < m) (a : C(B,Tube m m)) :
    negativeStableClass a = FiberFamily.classOf m (angularFamily a) := by
  exact (FiberFamily.classOf_equiv (m+1) (angularFamily_stabilize (V:=V) hm a)).symm.trans
    (FiberFamily.classOf_suspend m (angularFamily a))

include V in
theorem negativeStableClass_stabilize {m : ℕ} (a : C(B,Tube m m)) :
    negativeStableClass ((stabilize m).comp a) = negativeStableClass a :=
  negativeStableClass_eq (V:=V) (Nat.succ_pos m) _

include V in
theorem negativeStableClass_stabilizeFor {m : ℕ} (a : C(B,Tube m m)) (r : ℕ) :
    negativeStableClass ((stabilizeFor m r).comp a) = negativeStableClass a := by
  induction r with
  | zero => rfl
  | succ r ih => exact (negativeStableClass_stabilize (V:=V)
      ((stabilizeFor m r).comp a)).trans ih

include V in
theorem angularFamily_homotopic {k l : ℕ} (hdim : 0 < k+l)
    {a b : C(B,Tube k l)} (h : a.Homotopic b) :
    FiberFamily.Equiv (angularFamily a) (angularFamily b) := by
  let : NeZero (k+l) := ⟨by omega⟩
  let v : C(Tube k l, RegularHomogeneous (Euclidean (k+l))) :=
    ⟨Subtype.val,continuous_subtype_val⟩
  exact RegularHomogeneous.negative_equiv_of_homotopic (V:=V) (v.comp a) (v.comp b)
    ((Homotopic.refl v).comp h)

include V in
theorem negativeStableClass_homotopic {m : ℕ} {a b : C(B,Tube m m)}
    (h : a.Homotopic b) : negativeStableClass a = negativeStableClass b := by
  exact FiberFamily.classOf_equiv (m+1) (angularFamily_homotopic (V:=V)
    (by omega : 0 < (m+1)+(m+1)) ((Homotopic.refl (stabilize m)).comp h))

include V in

theorem negativeStableClass_eq_standard_iff {m : ℕ} (hm : 0 < m)
    (a : C(B,Tube m m)) : negativeStableClass a = standardSphericalClass B ↔
      StableNegativeTrivial a := by
  rw [negativeStableClass_eq (V:=V) hm,← round_family_class m,
    FiberFamily.classOf_sameGrade,stableNegativeTrivial_iff_finite_spherical (V:=V) hm]

end Tubes
end NearbyLagrangian

end

end OAI
