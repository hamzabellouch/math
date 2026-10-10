import Mathlib
import OAI.Geometry.NearbyLagrangian.StableFibers

namespace OAI

/-! Directed tube classes and their stable negative fiber classes. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.Tubes
open ContinuousMap

def stabilizeTo (m n : ℕ) (h : m ≤ n) : C(Tube m m,Tube n n) :=
  Nat.leRecOn (C := fun n => C(Tube m m,Tube n n)) h
    (fun {k} f => (stabilize k).comp f) (ContinuousMap.id _)

@[simp] theorem stabilizeTo_self (m : ℕ) :
    stabilizeTo m m le_rfl = ContinuousMap.id _ := Nat.leRecOn_self _

theorem stabilizeTo_succ (m n : ℕ) (h : m ≤ n) :
    stabilizeTo m (n+1) (Nat.le_succ_of_le h) =
      (stabilize n).comp (stabilizeTo m n h) := Nat.leRecOn_succ h _

theorem stabilizeTo_add (m r : ℕ) :
    stabilizeTo m (m+r) (Nat.le_add_right m r) = stabilizeFor m r := by
  induction r with
  | zero => exact stabilizeTo_self m
  | succ r ih =>
    change stabilizeTo m ((m+r)+1) _ = _
    rw [stabilizeTo_succ m (m+r) (Nat.le_add_right m r),ih]
    rfl

theorem stabilizeTo_comp (m n p : ℕ) (h : m ≤ n) (j : n ≤ p) :
    (stabilizeTo n p j).comp (stabilizeTo m n h) = stabilizeTo m p (h.trans j) := by
  induction p, j using Nat.le_induction with
  | base => simp
  | succ p j ih =>
    rw [stabilizeTo_succ n p j,stabilizeTo_succ m p (h.trans j)]
    rw [ContinuousMap.comp_assoc,ih]

@[simp] theorem stabilizeTo_standard (m n : ℕ) (h : m ≤ n) :
    stabilizeTo m n h (standardTube m m) = standardTube n n := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [stabilizeTo_add,stabilizeFor_standard]

variable (B : Type*) [TopologicalSpace B]

def tubeHomotopySetoid (m : ℕ) : Setoid C(B,Tube m m) where
  r := ContinuousMap.Homotopic
  iseqv := ContinuousMap.Homotopic.equivalence

abbrev TubeHomotopyClass (m : ℕ) := Quotient (tubeHomotopySetoid B m)

structure TubeClassMap (m n : ℕ) where
  toFun : TubeHomotopyClass B m → TubeHomotopyClass B n

instance (m n : ℕ) : FunLike (TubeClassMap B m n)
    (TubeHomotopyClass B m) (TubeHomotopyClass B n) where
  coe := TubeClassMap.toFun
  coe_injective := by intro ⟨f⟩ ⟨g⟩ h; cases h; rfl

def stabilizeClass (m n : ℕ) (h : m ≤ n) :
    TubeClassMap B m n :=
  ⟨Quotient.map (fun a => (stabilizeTo m n h).comp a)
    (fun _ _ H => (Homotopic.refl (stabilizeTo m n h)).comp H)⟩

instance : DirectedSystem (TubeHomotopyClass B)
    (fun {m n} h => (stabilizeClass B m n h : _ → _)) where
  map_self := by
    intro m a
    induction a using Quotient.inductionOn with
    | h a =>
      change (Quotient.mk'' ((stabilizeTo m m le_rfl).comp a) : TubeHomotopyClass B m) =
        Quotient.mk'' a
      simp
  map_map := by
    intro p n m h j a
    induction a using Quotient.inductionOn with
    | h a =>
      apply congrArg Quotient.mk''
      change (stabilizeTo n p j).comp ((stabilizeTo m n h).comp a) =
        (stabilizeTo m p (h.trans j)).comp a
      rw [← ContinuousMap.comp_assoc,stabilizeTo_comp]

abbrev StableTubeClass := DirectLimit (TubeHomotopyClass B) (stabilizeClass B)

def stableClass {m : ℕ} (a : C(B,Tube m m)) : StableTubeClass B :=
  Quotient.mk'' ⟨m,Quotient.mk'' a⟩

def standardStableClass : StableTubeClass B :=
  stableClass B (ContinuousMap.const B (standardTube 0 0))

@[simp] theorem stableClass_stabilizeTo {m n : ℕ} (h : m ≤ n) (a : C(B,Tube m m)) :
    stableClass B ((stabilizeTo m n h).comp a) = stableClass B a := by
  apply Quotient.sound
  refine ⟨n,le_rfl,h,?_⟩
  change (Quotient.mk'' ((stabilizeTo n n le_rfl).comp
    ((stabilizeTo m n h).comp a)) : TubeHomotopyClass B n) =
      Quotient.mk'' ((stabilizeTo m n h).comp a)
  simp

theorem stableClass_standard (m : ℕ) :
    stableClass B (ContinuousMap.const B (standardTube m m)) = standardStableClass B := by
  have h := stableClass_stabilizeTo B (Nat.zero_le m)
    (ContinuousMap.const B (standardTube 0 0))
  simpa [standardStableClass,ContinuousMap.comp_const] using h

theorem stableClass_eq_iff {m n : ℕ} (a : C(B,Tube m m)) (b : C(B,Tube n n)) :
    stableClass B a = stableClass B b ↔
    ∃ p : ℕ, ∃ h : m ≤ p, ∃ j : n ≤ p,
      ((stabilizeTo m p h).comp a).Homotopic ((stabilizeTo n p j).comp b) := by
  change (Quotient.mk'' ⟨m,Quotient.mk'' a⟩ : StableTubeClass B) =
    Quotient.mk'' ⟨n,Quotient.mk'' b⟩ ↔ _
  rw [Quotient.eq]
  change (∃ p h j, (Quotient.mk'' ((stabilizeTo m p h).comp a) : TubeHomotopyClass B p) =
    Quotient.mk'' ((stabilizeTo n p j).comp b)) ↔ _
  simp only [Quotient.eq]
  rfl

instance tubePathConnected (k l : ℕ) : PathConnectedSpace (Tube k l) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

theorem nullhomotopic_iff_standard {m : ℕ} (a : C(B,Tube m m)) :
    a.Nullhomotopic ↔ a.Homotopic (ContinuousMap.const B (standardTube m m)) := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨p⟩ := PathConnectedSpace.joined y (standardTube m m)
    exact hy.trans ⟨p.toHomotopyConst⟩
  · intro h
    exact ⟨standardTube m m,h⟩

theorem stablyNonNull_iff_class_ne {m : ℕ} (a : C(B,Tube m m)) :
    StablyNonNull a ↔ stableClass B a ≠ standardStableClass B := by
  rw [← stableClass_standard B m,ne_eq,stableClass_eq_iff]
  constructor
  · intro ha he
    obtain ⟨p,h,j,H⟩ := he
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
    apply ha r
    apply (nullhomotopic_iff_standard B _).mpr
    simpa only [stabilizeTo_add,ContinuousMap.comp_const,stabilizeFor_standard] using H
  · intro h r hr
    apply h
    refine ⟨m+r,Nat.le_add_right m r,Nat.le_add_right m r,?_⟩
    simpa only [stabilizeTo_add,ContinuousMap.comp_const,stabilizeFor_standard] using
      (nullhomotopic_iff_standard B _).mp hr

end NearbyLagrangian.Tubes

end

noncomputable section
universe u v w
open Set ContinuousMap
open scoped Topology Manifold ContDiff

namespace NearbyLagrangian.Tubes
variable {B V : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]

include V in
theorem negativeStableClass_stabilizeTo {m n : ℕ} (h : m ≤ n) (a : C(B,Tube m m)) :
    negativeStableClass ((stabilizeTo m n h).comp a) = negativeStableClass a := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [stabilizeTo_add]
  exact negativeStableClass_stabilizeFor (V:=V) a r

def negativeClassOnStage (m : ℕ) : TubeHomotopyClass B m → FiberFamily.StableClass B :=
  Quotient.lift (fun a => negativeStableClass a)
    (fun _ _ h => negativeStableClass_homotopic (V:=V) h)

include V in
theorem negativeClassOnStage_compatible {m n : ℕ} (h : m ≤ n)
    (a : TubeHomotopyClass B m) :
    negativeClassOnStage (V:=V) n (stabilizeClass B m n h a) = negativeClassOnStage (V:=V) m a := by
  induction a using Quotient.inductionOn with
  | h a => exact negativeStableClass_stabilizeTo (V:=V) h a

def stableNegativeClass : StableTubeClass B → FiberFamily.StableClass B :=
  Quotient.lift (fun a => negativeClassOnStage (V:=V) a.1 a.2) (by
    intro a b h
    obtain ⟨p,i,j,h⟩ := h
    calc
      negativeClassOnStage (V:=V) a.1 a.2 =
          negativeClassOnStage (V:=V) p (stabilizeClass B a.1 p i a.2) :=
        (negativeClassOnStage_compatible (V:=V) i a.2).symm
      _ = negativeClassOnStage (V:=V) p (stabilizeClass B b.1 p j b.2) := congrArg _ h
      _ = negativeClassOnStage (V:=V) b.1 b.2 := negativeClassOnStage_compatible (V:=V) j b.2)

@[simp] theorem stableNegativeClass_apply {m : ℕ} (a : C(B,Tube m m)) :
    stableNegativeClass (V:=V) (stableClass B a) = negativeStableClass a := rfl

theorem negativeStableClass_standard (m : ℕ) :
    negativeStableClass (ContinuousMap.const B (standardTube m m)) = standardSphericalClass B := by
  change FiberFamily.classOf (m+1)
    (angularFamily ((stabilize m).comp (ContinuousMap.const B (standardTube m m)))) = _
  rw [ContinuousMap.comp_const,stabilize_standard]
  have h : FiberFamily.Equiv
      (angularFamily (ContinuousMap.const B (standardTube (m+1) (m+1))))
      (roundFamily B (m+1)) :=
    (negativeTrivial_iff_sphere _).mp (negativeTrivial_standard B (m+1) (m+1))
  exact (FiberFamily.classOf_equiv (m+1) h).trans (round_family_class (m+1))

@[simp] theorem stableNegativeClass_standard :
    stableNegativeClass (V:=V) (standardStableClass B) = standardSphericalClass B :=
  negativeStableClass_standard 0

omit [CompactSpace B] [T2Space B] in

theorem stableClass_rep_above (x : StableTubeClass B) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∃ a : C(B,Tube m m), stableClass B a = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    obtain ⟨m,x⟩ := x
    induction x using Quotient.inductionOn with
    | h a =>
      refine ⟨m+N,by omega,(stabilizeFor m N).comp a,?_⟩
      change stableClass B ((stabilizeFor m N).comp a) = stableClass B a
      rw [← stabilizeTo_add]
      exact stableClass_stabilizeTo B (Nat.le_add_right m N) a

include V in

theorem exists_kernel_family_iff :
    (∃ m : ℕ, 20 ≤ m ∧ ∃ a : C(B,Tube m m), StablyNonNull a ∧ StableNegativeTrivial a) ↔
    ∃ x : StableTubeClass B, x ≠ standardStableClass B ∧
      stableNegativeClass (V:=V) x = standardSphericalClass B := by
  constructor
  · rintro ⟨m,hm,a,hn,ht⟩
    refine ⟨stableClass B a,(stablyNonNull_iff_class_ne B a).mp hn,?_⟩
    exact (negativeStableClass_eq_standard_iff (V:=V) (by omega) a).mpr ht
  · rintro ⟨x,hx,ht⟩
    obtain ⟨m,hm,a,ha⟩ := stableClass_rep_above x 20
    refine ⟨m,hm,a,(stablyNonNull_iff_class_ne B a).mpr ?_,?_⟩
    · simpa only [ha] using hx
    · apply (negativeStableClass_eq_standard_iff (V:=V) (by omega) a).mp
      simpa only [← ha,stableNegativeClass_apply] using ht

theorem kernelFamilyGoal_iff_actual_nontrivial_fiber : KernelFamilyGoal ↔
    ∃ x : StableTubeClass (Metric.sphere (0 : Euclidean 10) 1),
      x ≠ standardStableClass (Metric.sphere (0 : Euclidean 10) 1) ∧
      stableNegativeClass (V:=Euclidean 9) x =
        standardSphericalClass (Metric.sphere (0 : Euclidean 10) 1) :=
  exists_kernel_family_iff (V:=Euclidean 9)

end NearbyLagrangian.Tubes

end

end OAI
