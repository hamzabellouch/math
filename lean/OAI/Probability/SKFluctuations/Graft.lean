import Mathlib
import OAI.Probability.SKFluctuations.BoundaryCostCongr

namespace OAI

/-! Graft. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uB vB wB
variable {ι : Type uB} {β : Type vB} {S : Type wB}

 
def BoundaryTree.graft {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps) :
    {front : List (GaussianStep ι)} → (T : BoundaryTree ι β front) → ReplicaTree ι S (front++steps)
  | _,.leaf b => R b
  | _,.step c T => (T.graft R).step c
  | _,.fork T U => (T.graft R).fork (U.graft R)

noncomputable def BoundaryTree.graftAssignmentEquiv {steps : List (GaussianStep ι)}
    (R : β → ReplicaTree ι S steps) : {front : List (GaussianStep ι)} → (T : BoundaryTree ι β front) →
    T.Assignment (fun b => (R b).Assignment) ≃ (T.graft R).Assignment
  | _,.leaf _ => Equiv.refl _
  | _,.step _ T => T.graftAssignmentEquiv R
  | _,.fork T U => Equiv.prodCongr (T.graftAssignmentEquiv R) (U.graftAssignmentEquiv R)

variable [Fintype ι] [Fintype S]

 theorem BoundaryTree.graft_weight (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (σ : T.Assignment (fun b => (R b).Assignment)) (x : ι → ℝ) :
    (T.graft R).weight w φ (T.graftAssignmentEquiv R σ) x =
      T.weight (fun _ => gaussianHierarchy w φ steps) (fun b τ _ => (R b).weight w φ τ) σ 0 x := by
  induction T generalizing x with
  | leaf b => rfl
  | @step c tail T ih =>
    rcases c with ⟨a,q⟩
    change shiftedMean _ a (gaussianHierarchy w φ (tail++steps))
      (fun y => (T.graft R).weight w φ (T.graftAssignmentEquiv R σ) y) x = _
    rw [gaussianHierarchy_prefix]
    have he := funext fun y => ih σ y
    rw [he]
    rfl
  | fork T U ihT ihU =>
    change (T.graft R).weight w φ (T.graftAssignmentEquiv R σ.1) x*
      (U.graft R).weight w φ (U.graftAssignmentEquiv R σ.2) x = _
    rw [ihT,ihU]
    rfl

omit [Fintype ι] [Fintype S] in
 theorem BoundaryTree.graft_leaves {steps : List (GaussianStep ι)}
    (R : β → ReplicaTree ι S steps) {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) :
    ((T.graft R).leaves:ℝ) = T.budget (fun b => ((R b).leaves:ℝ)) := by
  induction T with
  | leaf b => rfl
  | step c T ih => exact ih
  | fork T U ihT ihU =>
    change (((T.graft R).leaves+(U.graft R).leaves:ℕ):ℝ) = _
    rw [Nat.cast_add,ihT,ihU]
    rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S β : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 

theorem BoundaryTree.clock_crossing_variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    {a b Q : ℝ} (hG : OrderedSteps a (front++steps)) (hF : OrderedSteps b steps)
    (hb : 0 < b) (hO : PrefixOrdered 0 b front)
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    ∑ σ, |(T.graft R).atomicClock w φ L a (T.graftAssignmentEquiv R σ) t x-
      T.weight (linearClockContinuation L b (gaussianHierarchy w φ steps))
        (fun c => (R c).atomicClock w φ L b) σ t x| ≤
      ((4*((T.graft R).leaves:ℝ)*((T.graft R).leaves+1:ℝ)*∑ i, (D i)^2)+
       T.budget (fun c => 4*((R c).leaves:ℝ)*((R c).leaves+1:ℝ)*(∑ i, (D i)^2)+b*Q))*t := by
  classical
  let Z := fun σ => (T.graft R).weight w φ (T.graftAssignmentEquiv R σ) x
  have hz (σ : T.Assignment (fun c => (R c).Assignment)) :
      T.weight (linearClockContinuation L b (gaussianHierarchy w φ steps))
        (fun c => (R c).atomicClock w φ L b) σ 0 x = Z σ := by
    rw [show Z σ = T.weight (fun _ => gaussianHierarchy w φ steps)
      (fun c τ _ => (R c).weight w φ τ) σ 0 x from T.graft_weight w φ R σ x]
    apply congrFun (T.weight_congr_at (t := 0) (s := 0) ?_ ?_ σ) x
    · exact funext fun y => linearClockContinuation_zero
        (gaussianHierarchy_regular hw φ steps hF 0).1.choose_spec.continuous L hb.ne' y
    · exact fun c τ => funext fun y => (R c).atomicClock_zero hw φ L hF b τ y
  have hc := (T.graft R).atomic_clock_variation hw φ L hG D hD hB ht (by norm_num : (0:ℝ) ≤ 0) x
  simp only [(T.graft R).atomicClock_zero hw φ L hG,sub_zero,abs_of_nonneg ht] at hc
  have he : (∑ σ, |(T.graft R).atomicClock w φ L a (T.graftAssignmentEquiv R σ) t x-Z σ|) =
      ∑ τ, |(T.graft R).atomicClock w φ L a τ t x-(T.graft R).weight w φ τ x| :=
    Fintype.sum_equiv (T.graftAssignmentEquiv R) _ _ (fun _ => rfl)
  rw [← he] at hc
  have hi := T.actual_clock_variation hw φ L R hF hb hQ D hD hB hO ht (by norm_num : (0:ℝ) ≤ 0) x
  simp only [hz,sub_zero,abs_of_nonneg ht] at hi
  calc
    _ ≤ (∑ σ, |(T.graft R).atomicClock w φ L a (T.graftAssignmentEquiv R σ) t x-Z σ|)+
      ∑ σ, |T.weight (linearClockContinuation L b (gaussianHierarchy w φ steps))
        (fun c => (R c).atomicClock w φ L b) σ t x-Z σ| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro σ _
      exact (abs_sub_le _ (Z σ) _).trans_eq (by rw [abs_sub_comm (Z σ)])
    _ ≤ _ := by nlinarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

def addHeadClock (q : ℕ → ι → ℝ≥0) (v : ι → ℝ≥0) : ℕ → ι → ℝ≥0
  | 0 => fun i => q 0 i+v i
  | j+1 => q (j+1)

 theorem gaussianHierarchy_addHeadClock {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {b : PositiveMass} {bs : List PositiveMass}
    (ho : MassOrdered b.val bs) (q : ℕ → ι → ℝ≥0) (v : ι → ℝ≥0) :
    gaussianHierarchy w φ (clockSteps (b::bs) (addHeadClock q v)) =
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) b.val
      (gaussianHierarchy w φ (clockSteps (b::bs) q)) := by
  have hF := (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ho (fun j => q (j+1))) 0).1.choose_spec
  funext x
  change shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q 0 i+v i)) b.val
    (gaussianHierarchy w φ (clockSteps bs (fun j => q (j+1)))) x = _
  symm
  simpa only [add_comm,clockSteps,gaussianHierarchy] using shiftedContinuation_productGaussian_add hF b.property.ne' v (q 0) x

omit [Fintype S] [Nonempty S] in
 theorem ClockTree.cut_zero_weight (F : ℝ → (ι → ℝ) → ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (A : (U : ClockTree S as) → U.Assignment → ℝ → (ι → ℝ) → ℝ)
    (σ : T.Assignment) (t : ℝ) (x : ι → ℝ) :
    (T.cut 0 q).weight F A (T.cutAssignmentEquiv 0 q σ) t x = A T σ t x := by
  cases T <;> rfl

 

 theorem ClockTree.addHeadClock_cut_weight {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → ι → ℝ≥0) (v : ι → ℝ≥0) {b : PositiveMass} {bs : List PositiveMass}
    (he : as = b::bs) (ho : MassOrdered b.val bs)
    (σ : T.Assignment) (x : ι → ℝ) :
    T.weight w φ (addHeadClock q v) σ x = (T.cut 1 q).weight
      (fun _ => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) b.val
        (gaussianHierarchy w φ (clockSteps (as.drop 1) (fun j => q (j+1)))))
      (fun U τ _ => shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) b.val
        (gaussianHierarchy w φ (clockSteps (as.drop 1) (fun j => q (j+1))))
        (U.weight w φ (fun j => q (j+1)) τ)) (T.cutAssignmentEquiv 1 q σ) 0 x := by
  induction T generalizing b bs x with
  | leaf => cases he
  | @step a cs T ih =>
    cases he
    have hF := (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ho (fun j => q (j+1))) 0).1.choose_spec
    have hzero := T.cut_zero_weight
      (fun _ => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a.val
        (gaussianHierarchy w φ (clockSteps cs (fun j => q (j+1)))))
      (fun k => q (k+1))
      (fun U τ _ => shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) a.val
        (gaussianHierarchy w φ (clockSteps cs (fun j => q (j+1))))
        (U.weight w φ (fun j => q (j+1)) τ)) σ 0
    change shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i+v i)) a.val
      (gaussianHierarchy w φ (clockSteps cs (fun j => q (j+1))))
      (T.weight w φ (fun j => q (j+1)) σ) x = _
    refine (shiftedMean_productGaussian_add hF
      (T.weight_smooth hw φ ho (fun j => q (j+1)) σ 0) a.property.ne' (q 0) v x).symm.trans ?_
    apply congrArg (fun f => shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) a.val
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a.val
        (gaussianHierarchy w φ (clockSteps cs (fun j => q (j+1))))) f x)
    exact (funext hzero).symm
  | fork T U ihT ihU =>
    change T.weight w φ (addHeadClock q v) σ.1 x*U.weight w φ (addHeadClock q v) σ.2 x = _
    rw [ihT he ho,ihU he ho]
    rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem finite_probability_product_distance {α β : Type*} [Fintype α] [Fintype β]
    {p q : α → ℝ} {r s : β → ℝ} (hq : ∀ a, 0 ≤ q a) (hr : ∀ b, 0 ≤ r b)
    (hqs : ∑ a, q a = 1) (hrs : ∑ b, r b = 1) :
    (∑ z : α × β, |p z.1*r z.2-q z.1*s z.2|) ≤
      (∑ a, |p a-q a|)+∑ b, |r b-s b| := by
  classical
  calc
    _ ≤ ∑ z : α × β, (|p z.1-q z.1| *r z.2+q z.1*|r z.2-s z.2|) := by
      apply Finset.sum_le_sum
      intro z _
      calc
        _ = |(p z.1-q z.1)*r z.2+q z.1*(r z.2-s z.2)| := by congr 1; ring
        _ ≤ _ := by simpa only [abs_mul,abs_of_nonneg (hr z.2), abs_of_nonneg (hq z.1)] using
          abs_add_le ((p z.1-q z.1)*r z.2) (q z.1*(r z.2-s z.2))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum,← Finset.sum_mul,Finset.sum_add_distrib,hqs,hrs,mul_one,one_mul]

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockTree.step_addHead_atomic {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {b : PositiveMass} {bs : List PositiveMass}
    (T : ClockTree S bs) (ho : MassOrdered b.val bs)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0)
    (σ : (T.step b).Assignment) (x : Fin (n+1) → ℝ) :
    ((T.step b).realize q).atomicClock w φ (diagonalDriver v) b.val
      ((T.step b).assignmentEquiv q σ) 1 x = (T.step b).weight w φ (addHeadClock q v) σ x := by
  classical
  simp only [ReplicaTree.atomicClock,linearClockTest,Real.toNNReal_one,linearGaussian_diagonal]
  have he : (((T.step b).realize q).expect w φ
      (fun τ => if τ = (T.step b).assignmentEquiv q σ then 1 else 0)) =
      (T.step b).weight w φ q σ := funext fun y => ((T.step b).realize q).expect_indicator w φ _ y
  rw [he]
  have hF := (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ho (fun j => q (j+1))) 0).1.choose_spec
  have hh := shiftedMean_productGaussian_add hF (T.weight_smooth hw φ ho (fun j => q (j+1)) σ 0)
    b.property.ne' v (q 0) x
  change shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) b.val
    (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ (clockSteps bs (fun j => q (j+1)))))
    (shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ (clockSteps bs (fun j => q (j+1))))
      (T.weight w φ (fun j => q (j+1)) σ)) x = shiftedMean
    (Measure.pi fun i => gaussianReal 0 (q 0 i+v i)) b.val
    (gaussianHierarchy w φ (clockSteps bs (fun j => q (j+1))))
    (T.weight w φ (fun j => q (j+1)) σ) x
  simpa only [add_comm] using hh

 

 theorem ClockTree.addHead_variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {b : PositiveMass} {bs : List PositiveMass} (he : as = b::bs) (ho : MassOrdered b.val bs)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℕ → Fin (n+1) → ℝ≥0) (v : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ, |T.weight w φ (addHeadClock q v) σ x-T.weight w φ q σ x| ≤
      4*(T.leaves:ℝ)*(T.leaves+1:ℝ)*∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  induction T generalizing b bs with
  | leaf => cases he
  | @step a cs T ih =>
    cases he
    have hO : MassOrdered a.val (a::cs) := ⟨a.property.le,le_rfl,ho⟩
    have hd (i : Fin (n+1)) (σ : S) : |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
      rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
    have hh := ((T.step a).realize q).atomic_clock_variation hw φ (diagonalDriver v)
      (clockSteps_ordered hO q) (fun i => Real.sqrt (v i)*D i)
      (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd
      (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 0) x
    simp only [sub_zero,abs_one,mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg,
      ((T.step a).realize q).atomicClock_zero hw φ (diagonalDriver v) (clockSteps_ordered hO q),
      ClockTree.realize_leaves] at hh
    have heq : (∑ σ, |(T.step a).weight w φ (addHeadClock q v) σ x-(T.step a).weight w φ q σ x|) =
        ∑ τ, |((T.step a).realize q).atomicClock w φ (diagonalDriver v) a.val τ 1 x-
          ((T.step a).realize q).weight w φ τ x| := by
      apply Fintype.sum_equiv ((T.step a).assignmentEquiv q)
      intro σ
      rw [T.step_addHead_atomic hw φ ho q v σ x]
      rfl
    rw [heq]
    exact hh
  | @fork cs T U ihT ihU =>
    have hO : MassOrdered b.val cs := he ▸ ⟨b.property.le,le_rfl,ho⟩
    have hpT := T.weight_probability hw φ hO q x
    have hpU := U.weight_probability hw φ hO (addHeadClock q v) x
    have hp := finite_probability_product_distance hpT.1 hpU.1 hpT.2 hpU.2
      (p := fun σ => T.weight w φ (addHeadClock q v) σ x) (s := fun σ => U.weight w φ q σ x)
    change (∑ σ : T.Assignment × U.Assignment, |T.weight w φ (addHeadClock q v) σ.1 x*
      U.weight w φ (addHeadClock q v) σ.2 x-T.weight w φ q σ.1 x*U.weight w φ q σ.2 x|) ≤ _
    apply hp.trans
    apply (add_le_add (ihT he ho) (ihU he ho)).trans
    simp only [ClockTree.leaves,Nat.cast_add]
    have hV : 0 ≤ ∑ i, (v i:ℝ)*(D i)^2 := Finset.sum_nonneg fun i _ => mul_nonneg (v i).coe_nonneg (sq_nonneg _)
    nlinarith [Nat.cast_nonneg (α := ℝ) T.leaves,Nat.cast_nonneg (α := ℝ) U.leaves,
      mul_nonneg (show (0:ℝ) ≤ T.leaves by positivity) (show (0:ℝ) ≤ U.leaves by positivity),
      mul_nonneg hV (mul_nonneg (show (0:ℝ) ≤ T.leaves by positivity) (show (0:ℝ) ≤ U.leaves by positivity))]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 
structure HeatClock where
  mass : ℝ
  positive : 0 < mass
  time : ℝ≥0

 def HeatJet.schedule {n : ℕ} (J : HeatJet n) : List HeatClock → HeatJet n
  | [] => J
  | c::cs => (J.schedule cs).evolve c.positive c.time

 theorem HeatJet.schedule_gradient_bound {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (cs : List HeatClock) :
    ∀ i x, |(J.schedule cs).G i x| ≤ D i := by
  induction cs with
  | nil => exact hD
  | cons c cs ih =>
    intro i x
    exact clockTest_abs_le (J.schedule cs).lipschitz ((J.schedule cs).smoothG i) (ih i) c.mass c.time x

 theorem HeatJet.schedule_nonexpansive {n : ℕ} (J K : HeatJet n) {C : ℝ}
    (h : ∀ x, |J.F x-K.F x| ≤ C) (cs : List HeatClock) :
    ∀ x, |(J.schedule cs).F x-(K.schedule cs).F x| ≤ C := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
    exact clockContinuation_abs_sub_le (J.schedule cs).lipschitz (K.schedule cs).lipschitz c.positive ih c.time

 

structure CoupledHeatClock where
  first : ℝ
  second : ℝ
  first_pos : 0 < first
  second_pos : 0 < second
  time : ℝ≥0

 def CoupledHeatClock.left (c : CoupledHeatClock) : HeatClock := ⟨c.first,c.first_pos,c.time⟩
 def CoupledHeatClock.right (c : CoupledHeatClock) : HeatClock := ⟨c.second,c.second_pos,c.time⟩
 def CoupledHeatClock.cost (c : CoupledHeatClock) : ℝ := |c.first-c.second| *c.time

 

theorem HeatJet.schedule_mass_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (cs : List CoupledHeatClock) (x : Fin (n+1) → ℝ) :
    |(J.schedule (cs.map CoupledHeatClock.left)).F x-
      (J.schedule (cs.map CoupledHeatClock.right)).F x| ≤
      (∑ i, (D i)^2)/2*(cs.map CoupledHeatClock.cost).sum := by
  induction cs generalizing x with
  | nil => simp [HeatJet.schedule]
  | cons c cs ih =>
    let J₀ := J.schedule (cs.map CoupledHeatClock.left)
    let J₁ := J.schedule (cs.map CoupledHeatClock.right)
    change |clockContinuation c.first J₀.F c.time x-clockContinuation c.second J₁.F c.time x| ≤ _
    have hs := clockContinuation_abs_sub_le J₀.lipschitz J₁.lipschitz c.first_pos (fun y => ih y) c.time x
    have hm := J₁.potential_mass_difference D (J.schedule_gradient_bound D hD _)
      c.first_pos c.second_pos c.time.coe_nonneg x
    have ht := (abs_sub_le (clockContinuation c.first J₀.F c.time x)
      (clockContinuation c.first J₁.F c.time x) (clockContinuation c.second J₁.F c.time x)).trans (add_le_add hs hm)
    apply ht.trans_eq
    simp only [List.map_cons,List.sum_cons,CoupledHeatClock.cost]
    ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

structure PositiveMassProfile where
  mass : ℝ → ℝ
  positive : ∀ t, 0 < mass t
  monotone : Monotone mass

 def PositiveMassProfile.grid (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) : ℕ → List HeatClock
  | 0 => [⟨α.mass l,α.positive l,t⟩]
  | k+1 => α.grid l (t/2) k ++ α.grid (l+(t:ℝ)/2) (t/2) k

 def HeatClock.halves (c : HeatClock) : List HeatClock :=
  [⟨c.mass,c.positive,c.time/2⟩,⟨c.mass,c.positive,c.time/2⟩]

 theorem HeatJet.schedule_append {n : ℕ} (J : HeatJet n) (cs ds : List HeatClock) :
    (J.schedule (cs++ds)).F = ((J.schedule ds).schedule cs).F := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change clockContinuation c.mass (J.schedule (cs++ds)).F c.time =
      clockContinuation c.mass ((J.schedule ds).schedule cs).F c.time
    rw [ih]

 theorem HeatJet.schedule_congr_terminal {n : ℕ} (J K : HeatJet n) (h : J.F = K.F)
    (cs : List HeatClock) : (J.schedule cs).F = (K.schedule cs).F := by
  induction cs with
  | nil => exact h
  | cons c cs ih =>
    change clockContinuation c.mass (J.schedule cs).F c.time = clockContinuation c.mass (K.schedule cs).F c.time
    rw [ih]

 theorem HeatJet.schedule_halves {n : ℕ} (J : HeatJet n) (cs : List HeatClock) :
    (J.schedule (cs.flatMap HeatClock.halves)).F = (J.schedule cs).F := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons,J.schedule_append]
    change clockContinuation c.mass (clockContinuation c.mass (J.schedule (cs.flatMap HeatClock.halves)).F
      ((c.time/2:ℝ≥0):ℝ)) ((c.time/2:ℝ≥0):ℝ) = clockContinuation c.mass (J.schedule cs).F c.time
    rw [ih]
    funext x
    rw [clockContinuation_add (J.schedule cs).lipschitz c.positive.ne' (by positivity) (by positivity)]
    congr 1
    simp only [NNReal.coe_div,NNReal.coe_ofNat]
    ring

 def PositiveMassProfile.coupledGrid (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) : ℕ → List CoupledHeatClock
  | 0 => [⟨α.mass l,α.mass l,α.positive l,α.positive l,t/2⟩,
           ⟨α.mass l,α.mass (l+(t:ℝ)/2),α.positive l,α.positive _,t/2⟩]
  | k+1 => α.coupledGrid l (t/2) k ++ α.coupledGrid (l+(t:ℝ)/2) (t/2) k

 theorem PositiveMassProfile.coupledGrid_left (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    (α.coupledGrid l t k).map CoupledHeatClock.left = (α.grid l t k).flatMap HeatClock.halves := by
  induction k generalizing l t with
  | zero => rfl
  | succ k ih => simp only [PositiveMassProfile.coupledGrid,PositiveMassProfile.grid,List.map_append,List.flatMap_append,ih]

 theorem PositiveMassProfile.coupledGrid_right (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    (α.coupledGrid l t k).map CoupledHeatClock.right = α.grid l t (k+1) := by
  induction k generalizing l t with
  | zero => rfl
  | succ k ih => simp only [PositiveMassProfile.coupledGrid,PositiveMassProfile.grid,List.map_append,ih]

 theorem PositiveMassProfile.coupledGrid_cost (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    ((α.coupledGrid l t k).map CoupledHeatClock.cost).sum ≤
      (t:ℝ)/(2:ℝ)^(k+1)*(α.mass (l+t)-α.mass l) := by
  induction k generalizing l t with
  | zero =>
    have hm := α.monotone (show l ≤ l+(t:ℝ)/2 by linarith [t.coe_nonneg])
    have he := α.monotone (show l+(t:ℝ)/2 ≤ l+t by linarith [t.coe_nonneg])
    simp only [PositiveMassProfile.coupledGrid,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      CoupledHeatClock.cost,sub_self,abs_zero,zero_mul,zero_add,add_zero,NNReal.coe_div,NNReal.coe_ofNat,pow_one]
    rw [abs_of_nonpos (sub_nonpos.mpr hm)]
    nlinarith [t.coe_nonneg]
  | succ k ih =>
    simp only [PositiveMassProfile.coupledGrid,List.map_append,List.sum_append]
    have h := add_le_add (ih l (t/2)) (ih (l+(t:ℝ)/2) (t/2))
    apply h.trans_eq
    simp only [NNReal.coe_div,NNReal.coe_ofNat,pow_succ]
    have he : l+(t:ℝ)/2+(t:ℝ)/2 = l+t := by ring
    rw [he]
    ring

 

theorem HeatJet.grid_successive {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0)
    (k : ℕ) (x : Fin (n+1) → ℝ) :
    |(J.schedule (α.grid l t k)).F x-(J.schedule (α.grid l t (k+1))).F x| ≤
      (∑ i, (D i)^2)/2*((t:ℝ)/(2:ℝ)^(k+1)*(α.mass (l+t)-α.mass l)) := by
  have h := J.schedule_mass_comparison D hD (α.coupledGrid l t k) x
  rw [α.coupledGrid_left,α.coupledGrid_right,J.schedule_halves] at h
  exact h.trans (mul_le_mul_of_nonneg_left (α.coupledGrid_cost l t k) (by positivity))

 

theorem HeatJet.grid_cauchy {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0)
    (x : Fin (n+1) → ℝ) :
    CauchySeq (fun k => (J.schedule (α.grid l t k)).F x) := by
  apply cauchySeq_of_le_geometric (1/2) ((∑ i, (D i)^2)/4*t*(α.mass (l+t)-α.mass l)) (by norm_num)
  intro k
  rw [Real.dist_eq]
  apply (J.grid_successive D hD α l t k x).trans_eq
  rw [pow_succ,div_pow]
  simp only [one_pow]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def PositiveMassProfile.pairedGrid (α β : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) : ℕ → List CoupledHeatClock
  | 0 => [⟨α.mass l,β.mass l,α.positive l,β.positive l,t⟩]
  | k+1 => α.pairedGrid β l (t/2) k ++ α.pairedGrid β (l+(t:ℝ)/2) (t/2) k

 theorem PositiveMassProfile.pairedGrid_left (α β : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    (α.pairedGrid β l t k).map CoupledHeatClock.left = α.grid l t k := by
  induction k generalizing l t with
  | zero => rfl
  | succ k ih => simp only [PositiveMassProfile.pairedGrid,PositiveMassProfile.grid,List.map_append,ih]

 theorem PositiveMassProfile.pairedGrid_right (α β : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    (α.pairedGrid β l t k).map CoupledHeatClock.right = β.grid l t k := by
  induction k generalizing l t with
  | zero => rfl
  | succ k ih => simp only [PositiveMassProfile.pairedGrid,PositiveMassProfile.grid,List.map_append,ih]

 theorem PositiveMassProfile.pairedGrid_cost (α β : PositiveMassProfile) {E : ℝ}
    (h : ∀ s, |α.mass s-β.mass s| ≤ E) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    ((α.pairedGrid β l t k).map CoupledHeatClock.cost).sum ≤ E*t := by
  induction k generalizing l t with
  | zero =>
    simp only [PositiveMassProfile.pairedGrid,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      CoupledHeatClock.cost,add_zero]
    exact mul_le_mul_of_nonneg_right (h l) t.coe_nonneg
  | succ k ih =>
    simp only [PositiveMassProfile.pairedGrid,List.map_append,List.sum_append]
    apply (add_le_add (ih l (t/2)) (ih (l+(t:ℝ)/2) (t/2))).trans_eq
    simp only [NNReal.coe_div,NNReal.coe_ofNat]
    ring

 theorem HeatJet.grid_profile_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α β : PositiveMassProfile) {E : ℝ}
    (h : ∀ s, |α.mass s-β.mass s| ≤ E) (l : ℝ) (t : ℝ≥0) (k : ℕ) (x : Fin (n+1) → ℝ) :
    |(J.schedule (α.grid l t k)).F x-(J.schedule (β.grid l t k)).F x| ≤
      (∑ i, (D i)^2)/2*(E*t) := by
  have hh := J.schedule_mass_comparison D hD (α.pairedGrid β l t k) x
  rw [α.pairedGrid_left,α.pairedGrid_right] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (α.pairedGrid_cost β h l t k) (by positivity))

noncomputable def HeatJet.profileValue {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) : ℝ :=
  limUnder atTop (fun k => (J.schedule (α.grid l t k)).F x)

 theorem HeatJet.grid_tendsto {n : ℕ} (J : HeatJet n) (α : PositiveMassProfile)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    Tendsto (fun k => (J.schedule (α.grid l t k)).F x) atTop (𝓝 (J.profileValue α l t x)) := by
  choose D _ hD using fun i => (J.smoothG i).bound
  exact (J.grid_cauchy D hD α l t x).tendsto_limUnder

 theorem HeatJet.profileValue_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α β : PositiveMassProfile) {E : ℝ}
    (h : ∀ s, |α.mass s-β.mass s| ≤ E) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |J.profileValue α l t x-J.profileValue β l t x| ≤ (∑ i, (D i)^2)/2*(E*t) := by
  exact le_of_tendsto ((J.grid_tendsto α l t x).sub (J.grid_tendsto β l t x)).abs
    (Filter.Eventually.of_forall fun k => J.grid_profile_comparison D hD α β h l t k x)

 theorem HeatJet.profileValue_nonexpansive {n : ℕ} (J K : HeatJet n) {C : ℝ}
    (h : ∀ x, |J.F x-K.F x| ≤ C) (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |J.profileValue α l t x-K.profileValue α l t x| ≤ C := by
  exact le_of_tendsto ((J.grid_tendsto α l t x).sub (K.grid_tendsto α l t x)).abs
    (Filter.Eventually.of_forall fun k => J.schedule_nonexpansive K h _ x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

structure NonnegativeMassProfile where
  mass : ℝ → ℝ
  nonneg : ∀ t, 0 ≤ mass t
  monotone : Monotone mass

 def NonnegativeMassProfile.positiveApprox (α : NonnegativeMassProfile) (k : ℕ) : PositiveMassProfile where
  mass s := α.mass s+(1/2:ℝ)^k
  positive s := add_pos_of_nonneg_of_pos (α.nonneg s) (by positivity)
  monotone := α.monotone.add_const _

 theorem NonnegativeMassProfile.approx_step (α : NonnegativeMassProfile) (k : ℕ) (s : ℝ) :
    |(α.positiveApprox k).mass s-(α.positiveApprox (k+1)).mass s| ≤ (1/2:ℝ)^k := by
  simp only [NonnegativeMassProfile.positiveApprox,pow_succ]
  rw [abs_of_nonneg (by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k])]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k]

 theorem HeatJet.regularized_cauchy {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0)
    (x : Fin (n+1) → ℝ) :
    CauchySeq (fun k => J.profileValue (α.positiveApprox k) l t x) := by
  apply cauchySeq_of_le_geometric (1/2) ((∑ i, (D i)^2)/2*t) (by norm_num)
  intro k
  rw [Real.dist_eq]
  apply (J.profileValue_comparison D hD _ _ (α.approx_step k) l t x).trans_eq
  ring

noncomputable def HeatJet.nonnegativeProfileValue {n : ℕ} (J : HeatJet n)
    (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) : ℝ :=
  limUnder atTop (fun k => J.profileValue (α.positiveApprox k) l t x)

 theorem HeatJet.regularized_tendsto {n : ℕ} (J : HeatJet n) (α : NonnegativeMassProfile)
    (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    Tendsto (fun k => J.profileValue (α.positiveApprox k) l t x) atTop (𝓝 (J.nonnegativeProfileValue α l t x)) := by
  choose D _ hD using fun i => (J.smoothG i).bound
  exact (J.regularized_cauchy D hD α l t x).tendsto_limUnder

 theorem HeatJet.nonnegativeProfile_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α β : NonnegativeMassProfile) {E : ℝ}
    (h : ∀ s, |α.mass s-β.mass s| ≤ E) (l : ℝ) (t : ℝ≥0) (x : Fin (n+1) → ℝ) :
    |J.nonnegativeProfileValue α l t x-J.nonnegativeProfileValue β l t x| ≤
      (∑ i, (D i)^2)/2*(E*t) := by
  apply le_of_tendsto ((J.regularized_tendsto α l t x).sub (J.regularized_tendsto β l t x)).abs
  apply Filter.Eventually.of_forall
  intro k
  apply J.profileValue_comparison D hD
  intro s
  simpa only [NonnegativeMassProfile.positiveApprox,add_sub_add_right_eq_sub] using h s

 theorem HeatJet.regularized_error {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (l : ℝ) (t : ℝ≥0)
    (x : Fin (n+1) → ℝ) (k : ℕ) :
    |J.profileValue (α.positiveApprox k) l t x-J.nonnegativeProfileValue α l t x| ≤
      (∑ i, (D i)^2)/2*t*(1/2:ℝ)^k := by
  have hb (j : ℕ) := J.profileValue_comparison D hD (α.positiveApprox k) (α.positiveApprox j)
    (E := |(1/2:ℝ)^k-(1/2:ℝ)^j|)
    (fun s => by simp only [NonnegativeMassProfile.positiveApprox,add_sub_add_left_eq_sub]; exact le_rfl)
    l t x
  have hp : Tendsto (fun j : ℕ => (1/2:ℝ)^j) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh := le_of_tendsto_of_tendsto
    (tendsto_const_nhds.sub (J.regularized_tendsto α l t x)).abs
    ((tendsto_const_nhds.sub hp).abs.mul_const (t:ℝ) |>.const_mul ((∑ i, (D i)^2)/2))
    (Filter.Eventually.of_forall hb)
  simpa only [sub_zero,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) k),mul_assoc,mul_comm (t:ℝ)] using hh

 theorem HeatJet.grid_error {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0)
    (x : Fin (n+1) → ℝ) (k : ℕ) :
    |(J.schedule (α.grid l t k)).F x-J.profileValue α l t x| ≤
      (∑ i, (D i)^2)/2*t*(α.mass (l+t)-α.mass l)*(1/2:ℝ)^k := by
  have hh := dist_le_of_le_geometric_of_tendsto (r := (1/2:ℝ))
    (C := (∑ i, (D i)^2)/4*t*(α.mass (l+t)-α.mass l)) (by norm_num)
    (f := fun k => (J.schedule (α.grid l t k)).F x)
    (fun j => by
      rw [Real.dist_eq]
      apply (J.grid_successive D hD α l t j x).trans_eq
      rw [pow_succ,div_pow]
      simp only [one_pow]
      ring)
    (J.grid_tendsto α l t x) k
  rw [Real.dist_eq] at hh
  apply hh.trans_eq
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem PositiveMassProfile.pairedGrid_cost_continuous {X : Type*} [TopologicalSpace X]
    (α : X → PositiveMassProfile) (hc : ∀ s, Continuous (fun z => (α z).mass s))
    (β : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    Continuous (fun z => (((α z).pairedGrid β l t k).map CoupledHeatClock.cost).sum) := by
  induction k generalizing l t with
  | zero =>
    simpa only [PositiveMassProfile.pairedGrid,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      CoupledHeatClock.cost,add_zero,Pi.sub_apply] using ((hc l).sub continuous_const).abs.mul_const (t:ℝ)
  | succ k ih =>
    exact ((ih l (t/2)).add (ih (l+(t:ℝ)/2) (t/2))).congr
      (fun z => by simp only [PositiveMassProfile.pairedGrid,List.map_append,List.sum_append]; rfl)

 theorem PositiveMassProfile.pairedGrid_self_cost (α : PositiveMassProfile) (l : ℝ) (t : ℝ≥0) (k : ℕ) :
    ((α.pairedGrid α l t k).map CoupledHeatClock.cost).sum = 0 := by
  induction k generalizing l t with
  | zero => simp [PositiveMassProfile.pairedGrid,CoupledHeatClock.cost]
  | succ k ih => simp only [PositiveMassProfile.pairedGrid,List.map_append,List.sum_append,ih,add_zero]

 theorem HeatJet.continuous_grid {X : Type*} [TopologicalSpace X] {n : ℕ} (J : HeatJet n)
    (D : Fin (n+1) → ℝ) (hD : ∀ i x, |J.G i x| ≤ D i)
    (α : X → PositiveMassProfile) (hc : ∀ s, Continuous (fun z => (α z).mass s))
    (l : ℝ) (t : ℝ≥0) (k : ℕ) (x : Fin (n+1) → ℝ) :
    Continuous (fun z => (J.schedule ((α z).grid l t k)).F x) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hh := ((PositiveMassProfile.pairedGrid_cost_continuous α hc (α z) l t k).continuousAt (x := z) |>.const_mul
    ((∑ i, (D i)^2)/2)).tendsto
  rw [(α z).pairedGrid_self_cost,mul_zero] at hh
  apply squeeze_zero (fun _ => dist_nonneg) _ hh
  intro y
  rw [Real.dist_eq]
  have hb := J.schedule_mass_comparison D hD ((α y).pairedGrid (α z) l t k) x
  rw [(α y).pairedGrid_left,(α y).pairedGrid_right] at hb
  exact hb

 

theorem HeatJet.double_grid_error {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (α : NonnegativeMassProfile) (B : ℝ)
    (l : ℝ) (t : ℝ≥0) (hB : α.mass (l+t)-α.mass l ≤ B)
    (x : Fin (n+1) → ℝ) (k : ℕ) :
    |(J.schedule ((α.positiveApprox k).grid l t k)).F x-J.nonnegativeProfileValue α l t x| ≤
      ((∑ i, (D i)^2)/2*t*(B+1))*(1/2:ℝ)^k := by
  have hg := J.grid_error D hD (α.positiveApprox k) l t x k
  simp only [NonnegativeMassProfile.positiveApprox,add_sub_add_right_eq_sub] at hg
  have hr := J.regularized_error D hD α l t x k
  have ht := (abs_sub_le ((J.schedule ((α.positiveApprox k).grid l t k)).F x)
    (J.profileValue (α.positiveApprox k) l t x) (J.nonnegativeProfileValue α l t x))
  apply (ht.trans (add_le_add hg hr)).trans
  have he := mul_le_mul_of_nonneg_left hB (show 0 ≤ (∑ i, (D i)^2)/2*t*(1/2:ℝ)^k by positivity)
  nlinarith

end SKFluctuations.Hierarchy

end

end OAI
