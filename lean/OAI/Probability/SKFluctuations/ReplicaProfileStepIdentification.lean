import Mathlib
import OAI.Probability.SKFluctuations.ReplicaProfilePairRecursion

namespace OAI

/-! Replica Profile Step Identification. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem profileCovarianceRate_step_eq {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {bs : List PositiveMass} (b : PositiveMass)
    (E : ClockExpr S bs) {a : ℝ} (ho : MassOrdered a (b::bs)) (q d : ℕ → Fin (n+1) → ℝ)
    (T : ReplicaTree (Fin (n+1)) S (clockSteps bs (fun j i => Real.toNNReal (q (j+1) i))))
    (P : T.Assignment → ℝ)
    (he : E.eval w φ (fun j => q (j+1)) = T.expect w φ P)
    (hr : ∀ y, ReplicaTree.profileCovarianceRate w φ T b.val P
      (ReplicaTree.coordinateProfile φ (fun j => d (j+1))) y =
        2*(E.covariance φ (fun j => d (j+1))).eval w φ (fun j => q (j+1)) y)
    (x : Fin (n+1) → ℝ) :
    ReplicaTree.profileCovarianceRate w φ (T.step (b.val,fun i => Real.toNNReal (q 0 i))) a P
      (ReplicaTree.coordinateProfile φ d) x = 2*((E.step b).covariance φ d).eval w φ q x := by
  let D : ClockExpr S bs := ClockExpr.pressureCov φ bs (fun j => d (j+1))
  let C : ClockExpr S bs := E.covariance φ (fun j => d (j+1))
  let R : ClockExpr S bs := ClockExpr.coordSum fun i => (E.testedInsert φ b.val i).scale (d 0 i)
  have hp (y : Fin (n+1) → ℝ) :
      ReplicaTree.profilePressure w φ (clockSteps bs (fun j i => Real.toNNReal (q (j+1) i)))
        (fun j => ReplicaTree.coordinateProfile φ d (j+1)) y =
      2*D.eval w φ (fun j => q (j+1)) y :=
    profilePressure_eq_eval hw φ bs ho.2.2 _ _ y
  have hE : (T.step (b.val,fun i => Real.toNNReal (q 0 i))).expect w φ P x =
      (E.step b).eval w φ q x := by
    rw [ReplicaTree.expect_step hw φ T _ _ (clockSteps_ordered ho.2.2 _)]
    change varianceTest _ _ _ _ _ = _
    rw [← he]
    rfl
  have hrow (y : Fin (n+1) → ℝ) :
      T.markedPairExpectation w φ b.val P (ReplicaTree.coordinateProfile φ d 0) y+
        b.val*T.expect w φ P y*ReplicaTree.profilePressure w φ
          (clockSteps bs (fun j i => Real.toNNReal (q (j+1) i)))
          (fun j => ReplicaTree.coordinateProfile φ d (j+1)) y+
        ReplicaTree.profileCovarianceRate w φ T b.val P
          (fun j => ReplicaTree.coordinateProfile φ d (j+1)) y =
      ((R.add ((E.mul D).scale (2*b.val))).add (C.scale 2)).eval w φ (fun j => q (j+1)) y := by
    rw [hp]
    change _+ReplicaTree.profileCovarianceRate w φ T b.val P
      (ReplicaTree.coordinateProfile φ (fun j => d (j+1))) y = _
    have ht := profilePair_const_eq_testedInsert hw φ E ho.2.2 _ T P he (d 0) y
    change T.markedPairExpectation w φ b.val P (ReplicaTree.coordinateProfile φ d 0) y = _ at ht
    rw [hr,ht]
    simp only [R,C,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho.2.2,he]
    ring
  change shiftedMean _ b.val _ _ x-b.val*(T.step (b.val,fun i => Real.toNNReal (q 0 i))).expect w φ P x*
    ReplicaTree.profilePressure w φ (clockSteps (b::bs) (fun j i => Real.toNNReal (q j i)))
      (ReplicaTree.coordinateProfile φ d) x = _
  simp_rw [hrow]
  rw [hE,profilePressure_eq_eval hw φ (b::bs) ho]
  change (((R.add ((E.mul D).scale (2*b.val))).add (C.scale 2)).step b).eval w φ q x-
    b.val*(E.step b).eval w φ q x*(2*(ClockExpr.pressureCov φ (b::bs) d).eval w φ q x) = _
  rw [ClockExpr.eval_step_add hw φ b ho.2.2,ClockExpr.eval_step_add hw φ b ho.2.2]
  simp_rw [ClockExpr.eval_step_scale]
  rw [show R = ClockExpr.coordSum (fun i => (E.testedInsert φ b.val i).scale (d 0 i)) from rfl,
    ClockExpr.eval_step_coordSum hw φ b ho.2.2]
  simp_rw [ClockExpr.eval_step_scale]
  simp only [ClockExpr.covariance,ClockExpr.eval,ClockExpr.eval_sub,
    ClockExpr.eval_coordSum hw φ ho,ClockExpr.pressureCov]
  have hpot (i : Fin (n+1)) :
      ((ClockExpr.potentialInsert φ b.val i bs).step b).eval w φ q x =
      b.val*((((ClockExpr.grad φ i bs).source φ (Pi.single i 1)).step b).eval w φ q x)+
      b.val^2*((((ClockExpr.grad φ i bs).mul (ClockExpr.grad φ i bs)).step b).eval w φ q x) := by
    simp only [ClockExpr.potentialInsert,ClockExpr.eval_step_add hw φ b ho.2.2,ClockExpr.eval_step_scale]
  change _ = 2*((∑ i, d 0 i/2*
      (((E.testedInsert φ b.val i).step b).eval w φ q x-
        (E.step b).eval w φ q x*((ClockExpr.potentialInsert φ b.val i bs).step b).eval w φ q x))+
    (C.step b).eval w φ q x+
    b.val*(((E.mul D).step b).eval w φ q x-(E.step b).eval w φ q x*(D.step b).eval w φ q x))
  simp_rw [hpot]
  simp only [D,ClockExpr.eval,mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  ring_nf

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy.ClockTree
open scoped NNReal
variable {S ι : Type*}

def single : (as : List PositiveMass) → ClockTree S as
  | [] => .leaf
  | a::as => .step a (single as)

def singleEquiv : (as : List PositiveMass) → (single (S:=S) as).Assignment ≃ S
  | [] => Equiv.refl _
  | _::as => singleEquiv as

def singleSlot : (as : List PositiveMass) → (single (S:=S) as).Slot
  | [] => ()
  | _::as => singleSlot as

theorem single_atSlot (as : List PositiveMass) (σ : (single (S:=S) as).Assignment) :
    (single as).atSlot σ (singleSlot as) = singleEquiv (S:=S) as σ := by
  induction as with
  | nil => rfl
  | cons a as ih => exact ih σ

def slotEquiv : {as : List PositiveMass} → (T : ClockTree S as) →
    (q : ℕ → ι → ℝ≥0) → T.Slot ≃ (T.realize q).Slot
  | _, .leaf, _ => Equiv.refl _
  | _, .step _ T, q => T.slotEquiv (fun j => q (j+1))
  | _, .fork T U, q => Equiv.sumCongr (T.slotEquiv q) (U.slotEquiv q)

theorem realize_atSlot {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → ι → ℝ≥0) (σ : T.Assignment) (s : T.Slot) :
    (T.realize q).atSlot (T.assignmentEquiv q σ) (T.slotEquiv q s) = T.atSlot σ s := by
  induction T generalizing q with
  | leaf => rfl
  | step a T ih => exact ih _ σ s
  | fork T U ihT ihU => cases s <;> first | exact ihT q _ _ | exact ihU q _ _

theorem realize_splitIndex {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → ι → ℝ≥0) (s t : T.Slot) :
    (T.realize q).splitIndex (T.slotEquiv q s) (T.slotEquiv q t) = T.splitIndex s t := by
  induction T generalizing q with
  | leaf => rfl
  | step a T ih => exact congrArg (1+·) (ih _ s t)
  | fork T U ihT ihU => cases s <;> cases t <;> first | rfl | exact ihT q _ _ | exact ihU q _ _

structure MarkedPlacement {as : List PositiveMass} (T : ClockTree S as) where
  tree : ClockTree S as
  coeff : ℝ
  restrict : tree.Assignment → T.Assignment
  spin : tree.Assignment → S
  embed : T.Slot → tree.Slot
  mark : tree.Slot
  restrict_at : ∀ σ s, T.atSlot (restrict σ) s = tree.atSlot σ (embed s)
  spin_at : ∀ σ, spin σ = tree.atSlot σ mark

namespace MarkedPlacement

def fresh {as : List PositiveMass} (T : ClockTree S as) (c : ℝ) : MarkedPlacement T where
  tree := T.fork (single as)
  coeff := c
  restrict := Prod.fst
  spin := fun σ => singleEquiv (S:=S) as σ.2
  embed := Sum.inl
  mark := Sum.inr (singleSlot as)
  restrict_at := fun _ _ => rfl
  spin_at := fun σ => (single_atSlot as σ.2).symm

def coincide : MarkedPlacement (ClockTree.leaf (S:=S)) where
  tree := .leaf
  coeff := 1
  restrict := id
  spin := id
  embed := id
  mark := ()
  restrict_at := fun _ _ => rfl
  spin_at := fun _ => rfl

def step (a : PositiveMass) {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) : MarkedPlacement (T.step a) where
  tree := p.tree.step a
  coeff := p.coeff
  restrict := p.restrict
  spin := p.spin
  embed := p.embed
  mark := p.mark
  restrict_at := p.restrict_at
  spin_at := p.spin_at

def left {as : List PositiveMass} {T : ClockTree S as}
    (U : ClockTree S as) (p : MarkedPlacement T) : MarkedPlacement (T.fork U) where
  tree := p.tree.fork U
  coeff := p.coeff
  restrict := fun σ => (p.restrict σ.1,σ.2)
  spin := fun σ => p.spin σ.1
  embed := Sum.map p.embed id
  mark := Sum.inl p.mark
  restrict_at := by intro σ s; cases s with
    | inl s => exact p.restrict_at σ.1 s
    | inr s => rfl
  spin_at := fun σ => p.spin_at σ.1

def right {as : List PositiveMass} (T : ClockTree S as)
    {U : ClockTree S as} (p : MarkedPlacement U) : MarkedPlacement (T.fork U) where
  tree := T.fork p.tree
  coeff := p.coeff
  restrict := fun σ => (σ.1,p.restrict σ.2)
  spin := fun σ => p.spin σ.2
  embed := Sum.map id p.embed
  mark := Sum.inr p.mark
  restrict_at := by intro σ s; cases s with
    | inl s => rfl
    | inr s => exact p.restrict_at σ.2 s
  spin_at := fun σ => p.spin_at σ.2

 

def realize {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (q : ℕ → ι → ℝ≥0) : ReplicaTree.MarkedPlacement (T.realize q) where
  tree := p.tree.realize q
  coeff := p.coeff
  restrict := fun σ => T.assignmentEquiv q (p.restrict ((p.tree.assignmentEquiv q).symm σ))
  spin := fun σ => p.spin ((p.tree.assignmentEquiv q).symm σ)
  embed := fun s => p.tree.slotEquiv q (p.embed ((T.slotEquiv q).symm s))
  mark := p.tree.slotEquiv q p.mark
  restrict_at := by
    intro σ s
    obtain ⟨τ,rfl⟩ := (p.tree.assignmentEquiv q).surjective σ
    obtain ⟨t,rfl⟩ := (T.slotEquiv q).surjective s
    simp only [Equiv.symm_apply_apply,realize_atSlot,p.restrict_at]
  spin_at := by
    intro σ
    obtain ⟨τ,rfl⟩ := (p.tree.assignmentEquiv q).surjective σ
    simp only [Equiv.symm_apply_apply,realize_atSlot,p.spin_at]
end MarkedPlacement

def markedAttach : {as : List PositiveMass} → (T : ClockTree S as) → ℝ → List (MarkedPlacement T)
  | _, .leaf, a => [MarkedPlacement.coincide,MarkedPlacement.fresh .leaf (a-1)]
  | _, .step b T, a => MarkedPlacement.fresh (T.step b) (a-b.val) ::
      (T.markedAttach b.val).map (MarkedPlacement.step b)
  | _, .fork T U, a => MarkedPlacement.fresh (T.fork U) (-a) ::
      ((T.markedAttach a).map (MarkedPlacement.left U) ++
        (U.markedAttach a).map (MarkedPlacement.right T))

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy
open scoped NNReal
variable {S ι : Type*}

namespace ReplicaTree
 

structure SingleBranch (steps : List (GaussianStep ι)) where
  tree : ReplicaTree ι S steps
  spin : tree.Assignment → S
  mark : tree.Slot
  spin_at : ∀ σ, spin σ = tree.atSlot σ mark

namespace SingleBranch

def canonical (steps : List (GaussianStep ι)) : SingleBranch (S:=S) steps where
  tree := ReplicaTree.single (S:=S) steps
  spin := ReplicaTree.singleEquiv (S:=S) steps
  mark := ReplicaTree.singleSlot (S:=S) steps
  spin_at := fun σ => (ReplicaTree.atSlot_single (S:=S) steps σ).symm

def step {tail : List (GaussianStep ι)} (b : SingleBranch (S:=S) tail)
    (st : GaussianStep ι) : SingleBranch (S:=S) (st::tail) where
  tree := b.tree.step st
  spin := b.spin
  mark := b.mark
  spin_at := b.spin_at

def fromClock (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) :
    SingleBranch (S:=S) (clockSteps as q) where
  tree := (ClockTree.single (S:=S) as).realize q
  spin := fun σ => ClockTree.singleEquiv (S:=S) as (((ClockTree.single (S:=S) as).assignmentEquiv q).symm σ)
  mark := (ClockTree.single (S:=S) as).slotEquiv q (ClockTree.singleSlot (S:=S) as)
  spin_at := by
    intro σ
    obtain ⟨τ,rfl⟩ := ((ClockTree.single (S:=S) as).assignmentEquiv q).surjective σ
    simp only [Equiv.symm_apply_apply,ClockTree.realize_atSlot,ClockTree.single_atSlot]

theorem fromClock_canonical (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) :
    fromClock (S:=S) as q = canonical (clockSteps as q) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih =>
    change (fromClock as (fun j => q (j+1))).step ((a:ℝ),q 0) =
      (canonical (clockSteps as (fun j => q (j+1)))).step ((a:ℝ),q 0)
    rw [ih]

end SingleBranch

def MarkedPlacement.freshFrom {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) (c : ℝ) (b : SingleBranch (S:=S) steps) :
    MarkedPlacement T where
  tree := T.fork b.tree
  coeff := c
  restrict := Prod.fst
  spin := fun σ => b.spin σ.2
  embed := Sum.inl
  mark := Sum.inr b.mark
  restrict_at := fun _ _ => rfl
  spin_at := fun σ => b.spin_at σ.2

end ReplicaTree
end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open scoped NNReal
variable {S ι : Type*}

namespace ClockTree.MarkedPlacement

theorem realize_step (a : PositiveMass) {as : List PositiveMass}
    {T : ClockTree S as} (p : ClockTree.MarkedPlacement T) (q : ℕ → ι → ℝ≥0) :
    (p.step a).realize q = (p.realize (fun j => q (j+1))).step ((a:ℝ),q 0) := rfl

theorem realize_coincide (q : ℕ → ι → ℝ≥0) :
    (coincide (S:=S)).realize q = ReplicaTree.MarkedPlacement.coincide := rfl

theorem realize_left {as : List PositiveMass} {T : ClockTree S as}
    (U : ClockTree S as) (p : ClockTree.MarkedPlacement T) (q : ℕ → ι → ℝ≥0) :
    (p.left U).realize q = (p.realize q).left (U.realize q) := by
  unfold realize left ReplicaTree.MarkedPlacement.left ReplicaTree.Placement.left
  dsimp only [ClockTree.realize,ClockTree.assignmentEquiv,ClockTree.slotEquiv]
  simp only [Equiv.prodCongr_symm,Equiv.sumCongr_symm]
  congr 1
  · congr 1
    funext σ
    change ((T.assignmentEquiv q) (p.restrict ((p.tree.assignmentEquiv q).symm σ.1)),
      (U.assignmentEquiv q) ((U.assignmentEquiv q).symm σ.2)) = _
    exact congrArg (fun z => ((T.assignmentEquiv q) (p.restrict ((p.tree.assignmentEquiv q).symm σ.1)),z))
      ((U.assignmentEquiv q).apply_symm_apply σ.2)
  · funext s
    cases s with
    | inl s => rfl
    | inr s => exact congrArg Sum.inr ((U.slotEquiv q).apply_symm_apply s)
  · apply proof_irrel_heq

theorem realize_right {as : List PositiveMass} (T : ClockTree S as)
    {U : ClockTree S as} (p : ClockTree.MarkedPlacement U) (q : ℕ → ι → ℝ≥0) :
    (p.right T).realize q = (p.realize q).right (T.realize q) := by
  unfold realize right ReplicaTree.MarkedPlacement.right ReplicaTree.Placement.right
  dsimp only [ClockTree.realize,ClockTree.assignmentEquiv,ClockTree.slotEquiv]
  simp only [Equiv.prodCongr_symm,Equiv.sumCongr_symm]
  congr 1
  · congr 1
    funext σ
    change ((T.assignmentEquiv q) ((T.assignmentEquiv q).symm σ.1),
      (U.assignmentEquiv q) (p.restrict ((p.tree.assignmentEquiv q).symm σ.2))) = _
    exact congrArg (fun z => (z,(U.assignmentEquiv q) (p.restrict ((p.tree.assignmentEquiv q).symm σ.2))))
      ((T.assignmentEquiv q).apply_symm_apply σ.1)
  · funext s
    cases s with
    | inl s => exact congrArg Sum.inl ((T.slotEquiv q).apply_symm_apply s)
    | inr s => rfl
  · apply proof_irrel_heq

theorem realize_fresh {as : List PositiveMass} (T : ClockTree S as) (c : ℝ)
    (q : ℕ → ι → ℝ≥0) : (fresh T c).realize q =
    ReplicaTree.MarkedPlacement.fresh (T.realize q) c := by
  have h : (fresh T c).realize q = ReplicaTree.MarkedPlacement.freshFrom
      (T.realize q) c (ReplicaTree.SingleBranch.fromClock as q) := by
    unfold realize fresh ReplicaTree.MarkedPlacement.freshFrom
    dsimp only [ClockTree.realize,ClockTree.assignmentEquiv,ClockTree.slotEquiv,
      ReplicaTree.SingleBranch.fromClock]
    congr 1
    · congr 1
      funext σ
      exact (T.assignmentEquiv q).apply_symm_apply σ.1
    · funext s
      exact congrArg Sum.inl ((T.slotEquiv q).apply_symm_apply s)
    · apply proof_irrel_heq
  rw [h,ReplicaTree.SingleBranch.fromClock_canonical]
  rfl

end ClockTree.MarkedPlacement
end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy.ClockTree
open scoped NNReal
variable {S ι : Type*}

theorem markedAttach_realize {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (q : ℕ → ι → ℝ≥0) :
    (T.markedAttach a).map (fun p => p.realize q) = (T.realize q).markedAttach a := by
  induction T generalizing a q with
  | leaf =>
    change [(MarkedPlacement.coincide (S:=S)).realize q,
      (MarkedPlacement.fresh leaf (a-1)).realize q] = _
    rw [MarkedPlacement.realize_fresh]
    rfl
  | step b T ih =>
    change (MarkedPlacement.fresh (T.step b) (a-b.val)).realize q ::
        ((T.markedAttach b.val).map (MarkedPlacement.step b)).map (fun p => p.realize q) = _
    rw [List.map_map,MarkedPlacement.realize_fresh]
    change _ :: _ = _ :: _
    congr 1
    rw [← ih b.val (fun j => q (j+1)),List.map_map]
    rfl
  | fork T U ihT ihU =>
    change (MarkedPlacement.fresh (T.fork U) (-a)).realize q ::
      (((T.markedAttach a).map (MarkedPlacement.left U) ++
        (U.markedAttach a).map (MarkedPlacement.right T)).map (fun p => p.realize q)) = _
    rw [List.map_append,List.map_map,List.map_map,MarkedPlacement.realize_fresh]
    change _ :: _ = _ :: _
    congr 1
    rw [← ihT a q,← ihU a q,List.map_map,List.map_map]
    congr 1
    · apply List.map_congr_left
      intro p _
      exact MarkedPlacement.realize_left U p q
    · apply List.map_congr_left
      intro p _
      exact MarkedPlacement.realize_right T p q

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S]

 
def integratedKernel (d : ℕ → S → S → ℝ) (j : ℕ) (σ τ : S) : ℝ :=
  ∑ k ∈ Finset.range j, d k σ τ

omit [Fintype S] in
 theorem kernelIncrement_integratedKernel (d : ℕ → S → S → ℝ) :
    kernelIncrement (integratedKernel d) = d := by
  funext j σ τ
  simp [kernelIncrement,integratedKernel,Finset.sum_range_succ]

 theorem profilePair_test_finsetSum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    {κ : Type*} (is : Finset κ) (P : κ → T.Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a (fun σ => ∑ i ∈ is, P i σ) K x =
      ∑ i ∈ is, T.profilePairExpectation w φ a (P i) K x := by
  simp only [profilePairExpectation,Finset.sum_mul,expect_finsetSum]
  simp_rw [Finset.mul_sum,list_sum_finset_sum,Finset.mul_sum,list_sum_finset_sum]

 theorem profilePair_test_smul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a c : ℝ)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a (fun σ => c*P σ) K x =
      c*T.profilePairExpectation w φ a P K x := by
  simp only [profilePairExpectation,mul_assoc,expect_const_mul]
  simp only [mul_left_comm _ c,← List.sum_map_mul_left]

variable [Nonempty S]

 

theorem profileCovarianceRate_eq_pair {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (d : ℕ → S → S → ℝ) (x : ι → ℝ) :
    profileCovarianceRate w φ T a P d x =
      T.profilePairExpectation w φ a P (integratedKernel d) x-
      a*T.expect w φ P x*profilePressure w φ steps d x := by
  have h := profilePair_eq_covarianceRate hw φ T ha P (integratedKernel d) x
  rw [kernelIncrement_integratedKernel] at h
  have hz : integratedKernel d 0 = fun _ _ => 0 := by funext σ τ; simp [integratedKernel]
  rw [hz,← profilePairExpectation_const,profilePair_zero] at h
  linarith

 theorem profileCovarianceRate_test_finsetSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    {κ : Type*} (is : Finset κ) (P : κ → T.Assignment → ℝ)
    (d : ℕ → S → S → ℝ) (x : ι → ℝ) :
    profileCovarianceRate w φ T a (fun σ => ∑ i ∈ is, P i σ) d x =
      ∑ i ∈ is, profileCovarianceRate w φ T a (P i) d x := by
  simp_rw [profileCovarianceRate_eq_pair hw φ T ha]
  rw [profilePair_test_finsetSum,expect_finsetSum]
  simp only [Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib]

 theorem profileCovarianceRate_test_smul {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ)
    (P : T.Assignment → ℝ) (d : ℕ → S → S → ℝ) (x : ι → ℝ) :
    profileCovarianceRate w φ T a (fun σ => c*P σ) d x =
      c*profileCovarianceRate w φ T a P d x := by
  simp_rw [profileCovarianceRate_eq_pair hw φ T ha]
  rw [profilePair_test_smul,expect_const_mul]
  ring

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
attribute [local instance] Classical.propDecidable

omit [Fintype S] [Nonempty S] in
 theorem pair_indicator {A B : Type*} (a : A) (b : B) :
    (fun z : A × B => @ite ℝ (z=(a,b)) (Classical.propDecidable _) 1 0) =
    (fun z => (if z.1=a then (1:ℝ) else 0)*(if z.2=b then (1:ℝ) else 0)) := by
  funext z
  rcases z with ⟨x,y⟩
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

 theorem profileCovarianceRate_fork_product {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (E F : ClockExpr S as) {a : ℝ} (ho : MassOrdered a as) (q d : ℕ → Fin (n+1) → ℝ)
    (T U : ReplicaTree (Fin (n+1)) S (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (P : T.Assignment → ℝ) (Q : U.Assignment → ℝ)
    (he : E.eval w φ q = T.expect w φ P) (hf : F.eval w φ q = U.expect w φ Q)
    (hr : ∀ y, ReplicaTree.profileCovarianceRate w φ T a P (ReplicaTree.coordinateProfile φ d) y =
      2*(E.covariance φ d).eval w φ q y)
    (hs : ∀ y, ReplicaTree.profileCovarianceRate w φ U a Q (ReplicaTree.coordinateProfile φ d) y =
      2*(F.covariance φ d).eval w φ q y) (x : Fin (n+1) → ℝ) :
    ReplicaTree.profileCovarianceRate w φ (T.fork U) a (fun σ => P σ.1*Q σ.2)
      (ReplicaTree.coordinateProfile φ d) x = 2*((E.mul F).covariance φ d).eval w φ q x := by
  have h₁ (τ : U.Assignment) :
      ReplicaTree.profileCovarianceRate w φ T a (fun σ => P σ*Q τ) (ReplicaTree.coordinateProfile φ d) x =
      Q τ*(2*(E.covariance φ d).eval w φ q x) := by
    rw [show (fun σ => P σ*Q τ) = (fun σ => Q τ*P σ) from funext fun _ => mul_comm _ _]
    rw [ReplicaTree.profileCovarianceRate_test_smul hw φ T (clockSteps_ordered ho _),hr]
  simp only [ReplicaTree.profileCovarianceRate]
  simp_rw [h₁,ReplicaTree.profileCovarianceRate_test_smul hw φ U (clockSteps_ordered ho _),hs,
    ReplicaTree.expect_mul_const]
  simp only [ClockExpr.covariance,ClockExpr.eval,he,hf]
  ring

 omit [Nonempty S] in
 theorem ClockTree.eval_weightExpr_expect (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (σ : T.Assignment) (q : ℕ → Fin (n+1) → ℝ) :
    (T.weightExpr σ).eval w φ q = (T.realize (fun j i => Real.toNNReal (q j i))).expect w φ
      (fun τ => if τ = T.assignmentEquiv (fun j i => Real.toNNReal (q j i)) σ then 1 else 0) := by
  classical
  funext x
  rw [ReplicaTree.expect_indicator,ClockTree.eval_weightExpr]
  rfl

 
theorem ClockTree.profileCovarianceRate_weight {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (σ : T.Assignment)
    (q d : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ReplicaTree.profileCovarianceRate w φ (T.realize (fun j i => Real.toNNReal (q j i))) a
      (fun τ => if τ = T.assignmentEquiv (fun j i => Real.toNNReal (q j i)) σ then 1 else 0)
      (ReplicaTree.coordinateProfile φ d) x =
      2*((T.weightExpr σ).covariance φ d).eval w φ q x := by
  classical
  induction T generalizing a q d x with
  | leaf => simp [ClockTree.realize,ClockTree.weightExpr,ReplicaTree.profileCovarianceRate,
      ClockExpr.covariance,ClockExpr.eval,gaussianHierarchyMean]
  | @step b bs T ih =>
    exact profileCovarianceRate_step_eq hw φ b (T.weightExpr σ) ho q d _ _
      (T.eval_weightExpr_expect w φ σ _) (ih ho.2.2 σ _ _) x
  | @fork bs T U ihT ihU =>
    have hp : (fun τ : ((T.fork U).realize (fun j i => Real.toNNReal (q j i))).Assignment =>
        if τ = (T.fork U).assignmentEquiv (fun j i => Real.toNNReal (q j i)) σ then (1:ℝ) else 0) =
        (fun τ => (if τ.1 = T.assignmentEquiv (fun j i => Real.toNNReal (q j i)) σ.1 then (1:ℝ) else 0)*
          (if τ.2 = U.assignmentEquiv (fun j i => Real.toNNReal (q j i)) σ.2 then (1:ℝ) else 0)) := by
      rcases σ with ⟨σ,ζ⟩
      exact pair_indicator (T.assignmentEquiv (fun j i => Real.toNNReal (q j i)) σ)
        (U.assignmentEquiv (fun j i => Real.toNNReal (q j i)) ζ)
    rw [hp]
    exact profileCovarianceRate_fork_product hw φ (T.weightExpr σ.1) (U.weightExpr σ.2) ho q d _ _ _ _
      (T.eval_weightExpr_expect w φ σ.1 _) (U.eval_weightExpr_expect w φ σ.2 _)
      (ihT ho σ.1 q d) (ihU ho σ.2 q d) x

end SKFluctuations.Hierarchy

end

end OAI
