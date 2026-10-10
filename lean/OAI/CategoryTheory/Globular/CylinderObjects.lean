import OAI.CategoryTheory.Globular.CylinderFramework

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularFrame
variable {K : Type u} [Category.{v} K] {L : Type w} [Category.{v} L]

noncomputable def map (D : GlobularFrame K) (F : K ⥤ L) [PreservesColimitsOfShape WalkingSpan F]
    [PreservesColimitsOfShape (Discrete PEmpty) F] : GlobularFrame L where
  obj j := F.obj (D.obj j)
  bd j := F.obj (D.bd j)
  inc j := F.map (D.inc j)
  left j := F.map (D.left j)
  right j := F.map (D.right j)
  square j := (D.square j).map F
  initial := D.initial.isInitialObj F _

end GlobularFrame

namespace GlobularTheory.Model

noncomputable def diskFrame (C : GlobularTheory.{v}) : GlobularFrame C.Model where
  obj := disk C
  bd := boundaryDisk C
  inc := I C
  left j := pushout.inl (I C j) (I C j)
  right j := pushout.inr (I C j) (I C j)
  square _j := IsPushout.of_hasPushout _ _
  initial := initialIsInitial

@[simp] theorem diskFrame_source (C : GlobularTheory.{v}) (j : ℕ) :
    (diskFrame C).diagram.source j = J C j := by
  change pushout.inl _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inl_desc _ _ _

@[simp] theorem diskFrame_target (C : GlobularTheory.{v}) (j : ℕ) :
    (diskFrame C).diagram.target j = targetDisk C j := by
  change pushout.inr _ _ ≫ pushout.desc _ _ _ = _
  exact pushout.inr_desc _ _ _

noncomputable def cutoffDiskFrame {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q : ℕ) :
    GlobularFrame (CutoffModels C q) := by
  let : (cutoffFunctor hC q).IsLeftAdjoint := (cutoffAdjunction hC q).isLeftAdjoint
  exact (diskFrame C).map (cutoffFunctor hC q)

@[simp] theorem cutoffDiskFrame_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q j : ℕ) : (cutoffDiskFrame hC q).diagram.source j = cutoffJ hC q j := by
  change (cutoffFunctor hC q).map _ ≫ (cutoffFunctor hC q).map _ = _
  rw [← Functor.map_comp]
  exact congrArg (cutoffFunctor hC q).map (diskFrame_source C j)

end GlobularTheory.Model

structure CylinderNode {K : Type u} [Category.{v} K] (D : GlobularFrame K) (j : ℕ) where
  bd : K
  obj : K
  inc : bd ⟶ obj
  bdEnd : Bool → (D.bd j ⟶ bd)
  endpoint : Bool → (D.obj j ⟶ obj)
  comm : ∀ ε, bdEnd ε ≫ inc = D.inc j ≫ endpoint ε

namespace CylinderNode
variable {K : Type u} [Category.{v} K] {D : GlobularFrame K} {j : ℕ}

noncomputable def critical (D : GlobularFrame K) (n : ℕ) : CylinderNode D n where
  bd := D.bd n
  obj := D.obj (n+1)
  inc := D.inc n ≫ D.diagram.source n
  bdEnd _ := 𝟙 _
  endpoint ε := if ε then D.diagram.target n else D.diagram.source n
  comm ε := by
    cases ε
    · simp
    · simp only [↓reduceIte, Category.id_comp]
      change D.inc n ≫ D.left n ≫ D.inc (n+1) = D.inc n ≫ D.right n ≫ D.inc (n+1)
      rw [← Category.assoc, (D.square n).w, Category.assoc]

variable [HasPushouts K]

noncomputable abbrev nextBoundary (Z : CylinderNode D j) : K := pushout Z.inc Z.inc

noncomputable def nextBdEnd (Z : CylinderNode D j) (ε : Bool) :
    D.bd (j+1) ⟶ Z.nextBoundary :=
  (D.square j).desc (Z.endpoint ε ≫ pushout.inl _ _) (Z.endpoint ε ≫ pushout.inr _ _)
    (by rw [← Category.assoc, ← Z.comm, Category.assoc, pushout.condition,
      ← Category.assoc, Z.comm, Category.assoc])

@[reassoc (attr := simp)] theorem nextBdEnd_left (Z : CylinderNode D j) (ε : Bool) :
    D.left j ≫ Z.nextBdEnd ε = Z.endpoint ε ≫ pushout.inl _ _ :=
  (D.square j).inl_desc _ _ _

@[reassoc (attr := simp)] theorem nextBdEnd_right (Z : CylinderNode D j) (ε : Bool) :
    D.right j ≫ Z.nextBdEnd ε = Z.endpoint ε ≫ pushout.inr _ _ :=
  (D.square j).inr_desc _ _ _

end CylinderNode

namespace TwoEndpoints
variable {K : Type u} [Category.{v} K] [HasPushouts K]
variable {Bd Disk B : K} (i : Bd ⟶ Disk) (e : Bool → (Bd ⟶ B))

noncomputable abbrev first : K := pushout (e false) i
noncomputable abbrev obj : K := pushout (e true ≫ pushout.inl (e false) i) i
noncomputable def base : B ⟶ obj i e := pushout.inl _ _ ≫ pushout.inl _ _
noncomputable def endpoint (ε : Bool) : Disk ⟶ obj i e :=
  if ε then pushout.inr _ _ else pushout.inr _ _ ≫ pushout.inl _ _

theorem condition (ε : Bool) : e ε ≫ base i e = i ≫ endpoint i e ε := by
  cases ε
  · simp only [base, endpoint, Bool.false_eq_true, ↓reduceIte, ← Category.assoc]
    rw [pushout.condition]
  · simp only [base, endpoint, ↓reduceIte, ← Category.assoc]
    exact pushout.condition

variable {Y : K}
noncomputable def desc (b : B ⟶ Y) (d : Bool → (Disk ⟶ Y))
    (h : ∀ ε, e ε ≫ b = i ≫ d ε) : obj i e ⟶ Y :=
  pushout.desc (pushout.desc b (d false) (h false)) (d true)
    (by rw [Category.assoc, pushout.inl_desc]; exact h true)

@[reassoc (attr := simp)] theorem base_desc (b : B ⟶ Y) (d : Bool → (Disk ⟶ Y))
    (h : ∀ ε, e ε ≫ b = i ≫ d ε) : base i e ≫ desc i e b d h = b := by
  simp only [base, desc, Category.assoc, pushout.inl_desc]

@[reassoc (attr := simp)] theorem endpoint_desc (b : B ⟶ Y) (d : Bool → (Disk ⟶ Y))
    (h : ∀ ε, e ε ≫ b = i ≫ d ε) (ε : Bool) : endpoint i e ε ≫ desc i e b d h = d ε := by
  cases ε <;> simp only [endpoint, desc, Bool.false_eq_true,
    ↓reduceIte, Category.assoc, pushout.inl_desc, pushout.inr_desc]

theorem hom_ext {f g : obj i e ⟶ Y} (hb : base i e ≫ f = base i e ≫ g)
    (hd : ∀ ε, endpoint i e ε ≫ f = endpoint i e ε ≫ g) : f = g := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · simpa only [base, Category.assoc] using hb
    · simpa only [endpoint, Bool.false_eq_true, ↓reduceIte, Category.assoc] using hd false
  · simpa only [endpoint, ↓reduceIte] using hd true

theorem oneSide_lifting {P X Y : K} (f : obj i e ⟶ P) (p : X ⟶ Y)
    (hi : HasLiftingProperty i p) (hf : HasLiftingProperty f p) (ε : Bool) :
    HasLiftingProperty (pushout.desc (base i e ≫ f) (endpoint i e ε ≫ f)
      (by rw [← Category.assoc, condition, Category.assoc])) p := by
  constructor
  intro a b sq
  let aB := pushout.inl (e ε) i ≫ a
  let aD := pushout.inr (e ε) i ≫ a
  have ha : e ε ≫ aB = i ≫ aD := by
    dsimp only [aB, aD]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  have hB : aB ≫ p = base i e ≫ f ≫ b := by
    have h := congrArg (pushout.inl (e ε) i ≫ ·) sq.w
    simpa only [aB, Category.assoc, pushout.inl_desc_assoc] using h
  have hD : aD ≫ p = endpoint i e ε ≫ f ≫ b := by
    have h := congrArg (pushout.inr (e ε) i ≫ ·) sq.w
    simpa only [aD, Category.assoc, pushout.inr_desc_assoc] using h
  have otherSq : CommSq (e (!ε) ≫ aB) i p (endpoint i e (!ε) ≫ f ≫ b) := by
    constructor
    rw [Category.assoc, hB, ← Category.assoc (e (!ε)), condition, Category.assoc]
  let : otherSq.HasLift := hi.sq_hasLift otherSq
  let ds : Bool → (Disk ⟶ X) := fun δ => if δ = ε then aD else otherSq.lift
  have dsε : ds ε = aD := by simp [ds]
  have dsother : ds (!ε) = otherSq.lift := by cases ε <;> simp [ds]
  have hds : ∀ δ, e δ ≫ aB = i ≫ ds δ := by
    intro δ
    by_cases h : δ = ε
    · subst δ; rw [dsε]; exact ha
    · have he : δ = !ε := by cases δ <;> cases ε <;> simp_all
      subst δ; rw [dsother]; exact otherSq.fac_left.symm
  let a' := desc i e aB ds hds
  have sq' : CommSq a' f p b := by
    constructor
    apply hom_ext i e
    · simp only [← Category.assoc, base_desc, a']
      simpa only [Category.assoc] using hB
    · intro δ
      simp only [← Category.assoc, endpoint_desc, a']
      by_cases h : δ = ε
      · subst δ; rw [dsε]; simpa only [Category.assoc] using hD
      · have he : δ = !ε := by cases δ <;> cases ε <;> simp_all
        subst δ; rw [dsother]; simpa only [Category.assoc] using otherSq.fac_right
  let : sq'.HasLift := hf.sq_hasLift sq'
  refine CommSq.HasLift.mk' ⟨sq'.lift, ?_, sq'.fac_right⟩
  apply pushout.hom_ext
  · rw [pushout.inl_desc_assoc, Category.assoc, sq'.fac_left]
    exact base_desc i e aB ds hds
  · rw [pushout.inr_desc_assoc, Category.assoc, sq'.fac_left]
    exact (endpoint_desc i e aB ds hds ε).trans dsε

end TwoEndpoints
open CategoryTheory CategoryTheory.Limits Opposite
namespace CylinderNode
variable {K : Type u} [Category.{v} K] {D : GlobularFrame K} {j : ℕ}

def stationary (D : GlobularFrame K) (j : ℕ) : CylinderNode D j where
  bd := D.bd j
  obj := D.obj j
  inc := D.inc j
  bdEnd _ := 𝟙 _
  endpoint _ := 𝟙 _
  comm _ := by simp

structure Step (Z : CylinderNode D j) (W : CylinderNode D (j+1)) where
  left : Z.obj ⟶ W.bd
  right : Z.obj ⟶ W.bd
  square : IsPushout Z.inc Z.inc left right
  end_left : ∀ ε, D.left j ≫ W.bdEnd ε = Z.endpoint ε ≫ left
  end_right : ∀ ε, D.right j ≫ W.bdEnd ε = Z.endpoint ε ≫ right

def stationaryStep (D : GlobularFrame K) (j : ℕ) :
    Step (stationary D j) (stationary D (j+1)) where
  left := D.left j
  right := D.right j
  square := D.square j
  end_left _ := by simp [stationary]
  end_right _ := by simp [stationary]

noncomputable def criticalStep (D : GlobularFrame K) (j : ℕ) :
    Step (stationary D j) (critical D (j+1)) where
  left := D.left j
  right := D.right j
  square := D.square j
  end_left _ := by simp [stationary, critical]
  end_right _ := by simp [stationary, critical]

end CylinderNode

namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)

noncomputable def cylinderFactor (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) := by
  let := cutoff_hasColimits hC q
  let := cutoff_hasLimits hC q
  let := boundaryClass_smallObject hC q (n+1)
  exact MorphismProperty.factorizationData (boundaryClass hC q (n+1)).rlp.llp
    (boundaryClass hC q (n+1)).rlp
    (terminal.from (TwoEndpoints.obj (cutoffI hC q j) e))

noncomputable def completedCylinder (j : ℕ) (B : CutoffModels C q)
    (e : Bool → (cutoffBoundary hC q j ⟶ B)) : CylinderNode (cutoffDiskFrame hC q) j := by
  let := cutoff_hasColimits hC q
  let F := cylinderFactor hC q n j B e
  exact
    { bd := B
      obj := F.Z
      inc := TwoEndpoints.base (cutoffI hC q j) e ≫ F.i
      bdEnd := e
      endpoint ε := TwoEndpoints.endpoint (cutoffI hC q j) e ε ≫ F.i
      comm ε := by erw [← Category.assoc, TwoEndpoints.condition, Category.assoc] }

noncomputable def cylinderNext {j : ℕ} (Z : CylinderNode (cutoffDiskFrame hC q) j) :
    CylinderNode (cutoffDiskFrame hC q) (j+1) := by
  let := cutoff_hasColimits hC q
  exact completedCylinder hC q n (j+1) Z.nextBoundary Z.nextBdEnd

noncomputable def cylinderNextStep {j : ℕ} (Z : CylinderNode (cutoffDiskFrame hC q) j) :
    CylinderNode.Step Z (cylinderNext hC q n Z) := by
  let := cutoff_hasColimits hC q
  exact
    { left := pushout.inl Z.inc Z.inc
      right := pushout.inr Z.inc Z.inc
      square := IsPushout.of_hasPushout _ _
      end_left := Z.nextBdEnd_left
      end_right := Z.nextBdEnd_right }

noncomputable def cylinderNode : (j : ℕ) → CylinderNode (cutoffDiskFrame hC q) j
  | 0 => if 0 < n then CylinderNode.stationary (cutoffDiskFrame hC q) 0
      else CylinderNode.critical (cutoffDiskFrame hC q) 0
  | j+1 => if j+1 < n then CylinderNode.stationary (cutoffDiskFrame hC q) (j+1)
      else if j+1 = n then CylinderNode.critical (cutoffDiskFrame hC q) (j+1)
      else cylinderNext hC q n (cylinderNode j)

theorem cylinderNode_low {j : ℕ} (h : j < n) :
    cylinderNode hC q n j = CylinderNode.stationary (cutoffDiskFrame hC q) j := by
  cases j <;> simp only [cylinderNode, ite_eq_left h]

theorem cylinderNode_critical : cylinderNode hC q n n =
    CylinderNode.critical (cutoffDiskFrame hC q) n := by
  cases n <;> simp only [cylinderNode, Nat.lt_irrefl, ite_false, ite_true]

theorem cylinderNode_high {j : ℕ} (h : n ≤ j) :
    cylinderNode hC q n (j+1) = cylinderNext hC q n (cylinderNode hC q n j) := by
  simp only [cylinderNode, ite_eq_right (show ¬ j+1 < n by omega),
    ite_eq_right (show ¬ j+1 = n by omega)]

noncomputable def cylinderStep (j : ℕ) :
    CylinderNode.Step (cylinderNode hC q n j) (cylinderNode hC q n (j+1)) := by
  by_cases h : j < n
  · by_cases h' : j+1 < n
    · rw [cylinderNode_low hC q n h, cylinderNode_low hC q n h']
      exact CylinderNode.stationaryStep _ _
    · have e : j+1 = n := by omega
      rw [cylinderNode_low hC q n h]
      have hc : cylinderNode hC q n (j+1) = CylinderNode.critical (cutoffDiskFrame hC q) (j+1) := by
        subst n; exact cylinderNode_critical hC q (j+1)
      rw [hc]
      exact CylinderNode.criticalStep _ _
  · rw [cylinderNode_high hC q n (by omega)]
    exact cylinderNextStep hC q n _

noncomputable def cylinderFrame : GlobularFrame (CutoffModels C q) where
  obj j := (cylinderNode hC q n j).obj
  bd j := (cylinderNode hC q n j).bd
  inc j := (cylinderNode hC q n j).inc
  left j := (cylinderStep hC q n j).left
  right j := (cylinderStep hC q n j).right
  square j := (cylinderStep hC q n j).square
  initial := by
    by_cases h : n = 0
    · subst n; rw [cylinderNode_critical]
      exact (cutoffDiskFrame hC q).initial
    · rw [cylinderNode_low hC q n (by omega)]
      exact (cutoffDiskFrame hC q).initial

noncomputable def cylinderEndpoint (ε : Bool) :
    GlobularFrame.Hom (cutoffDiskFrame hC q) (cylinderFrame hC q n) where
  obj j := (cylinderNode hC q n j).endpoint ε
  bd j := (cylinderNode hC q n j).bdEnd ε
  inc j := (cylinderNode hC q n j).comm ε
  left j := (cylinderStep hC q n j).end_left ε
  right j := (cylinderStep hC q n j).end_right ε

end GlobularTheory.Model
end Grothendieck

end OAI
