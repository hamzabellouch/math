import Mathlib
import OAI.Probability.SKFluctuations.MapCLM

namespace OAI

/-! Bounds. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 omit [Fintype ι] in
 theorem OrderedSteps.bounds {a : ℝ} {steps : List (GaussianStep ι)}
    (ha : OrderedSteps a steps) : 0 ≤ a ∧ a ≤ 1 := by
  induction steps generalizing a with
  | nil => exact ha
  | cons st tail ih => exact ⟨ha.1, ha.2.1.trans (ih ha.2.2.2).2⟩

 theorem shiftedMean_abs_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {F A B : E → ℝ} {m : ℝ} (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (hb : ∀ y, |A y| ≤ B y) {x : E}
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    |shiftedMean ν m F A x| ≤ shiftedMean ν m F B x := by
  apply abs_le.mpr
  constructor
  · have h := shiftedMean_mono (hA.const_mul (-1)) hB
      (fun y => by simpa only [neg_one_mul] using (neg_le_abs (A y)).trans (hb y)) hi
    rw [shiftedMean_const_mul] at h
    linarith
  · exact shiftedMean_mono hA hB (fun y => (le_abs_self _).trans (hb y)) hi

 theorem gaussianHierarchyMean_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {A B : S → ℝ} (hAB : ∀ σ, A σ ≤ B σ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    gaussianHierarchyMean w φ A steps x ≤ gaussianHierarchyMean w φ B steps x := by
  induction steps generalizing a x with
  | nil => exact Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hAB σ)
      (spinWeight_nonneg hw φ x σ))
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact shiftedMean_mono (gaussianHierarchyMean_smooth hw φ A tail ha.2.2.2 0)
      (gaussianHierarchyMean_smooth hw φ B tail ha.2.2.2 0)
      (fun y => ih ha.2.2.2 y) (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)

 theorem gaussianHierarchyMean_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {A : S → ℝ} (hA : ∀ σ, 0 ≤ A σ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    0 ≤ gaussianHierarchyMean w φ A steps x := by
  have h := gaussianHierarchyMean_mono hw φ hA steps ha x
  rwa [gaussianHierarchyMean_const hw φ steps ha 0 x] at h

 theorem gaussianHierarchyMean_abs_mono {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {A B : S → ℝ} (hAB : ∀ σ, |A σ| ≤ B σ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    |gaussianHierarchyMean w φ A steps x| ≤ gaussianHierarchyMean w φ B steps x := by
  induction steps generalizing a x with
  | nil =>
    calc
      |∑ σ, spinWeight w φ x σ*A σ| ≤ ∑ σ, |spinWeight w φ x σ*A σ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ, spinWeight w φ x σ*B σ := by
        apply Finset.sum_le_sum
        intro σ _
        rw [abs_mul,abs_of_nonneg (spinWeight_nonneg hw φ x σ)]
        exact mul_le_mul_of_nonneg_left (hAB σ) (spinWeight_nonneg hw φ x σ)
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    exact shiftedMean_abs_mono (gaussianHierarchyMean_smooth hw φ A tail ha.2.2.2 0)
      (gaussianHierarchyMean_smooth hw φ B tail ha.2.2.2 0)
      (fun y => ih ha.2.2.2 y) (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)

 theorem gaussianHierarchyMean_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {A : S → ℝ} {C : ℝ} (hA : ∀ σ, |A σ| ≤ C)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    |gaussianHierarchyMean w φ A steps x| ≤ C := by
  have h := gaussianHierarchyMean_abs_mono hw φ hA steps ha x
  rwa [gaussianHierarchyMean_const hw φ steps ha C x] at h

 def ProductTree.abs : {steps : List (GaussianStep ι)} → ProductTree ι S steps → ProductTree ι S steps
  | _, .leaf A => .leaf (fun σ => |A σ|)
  | _, .node st k child => .node st k (fun i => (child i).abs)

 theorem ProductTree.abs_mean_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ProductTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    0 ≤ T.abs.mean w φ x := by
  induction T generalizing a x with
  | leaf A => exact gaussianHierarchyMean_nonneg hw φ (fun _ => abs_nonneg _) [] ha x
  | @node st tail k child ih =>
    rcases st with ⟨m,q⟩
    exact Finset.prod_nonneg (fun i _ => shiftedMean_nonneg (fun y => ih i ha.2.2.2 y)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x))

 theorem ProductTree.mean_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ProductTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    |T.mean w φ x| ≤ T.abs.mean w φ x := by
  induction T generalizing a x with
  | leaf A => exact gaussianHierarchyMean_abs_mono hw φ (fun _ => le_rfl) [] ha x
  | @node st tail k child ih =>
    rcases st with ⟨m,q⟩
    change |∏ i, _| ≤ ∏ i, _
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    intro i _
    exact shiftedMean_abs_mono ((child i).mean_smooth hw φ ha.2.2.2 0)
      ((child i).abs.mean_smooth hw φ ha.2.2.2 0) (fun y => ih i ha.2.2.2 y)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uR vR

 

inductive ReplicaTree (ι : Type uR) (S : Type vR) : List (GaussianStep ι) → Type (max uR vR) where
  | leaf : ReplicaTree ι S []
  | step (st : GaussianStep ι) {tail : List (GaussianStep ι)}
      (T : ReplicaTree ι S tail) : ReplicaTree ι S (st::tail)
  | fork {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps) : ReplicaTree ι S steps

variable {ι : Type uR} {S : Type vR}

@[reducible] def ReplicaTree.Assignment : {steps : List (GaussianStep ι)} → ReplicaTree ι S steps → Type vR
  | _, .leaf => S
  | _, .step _ T => T.Assignment
  | _, .fork T U => T.Assignment × U.Assignment

@[instance_reducible] noncomputable def ReplicaTree.assignmentFintype [Fintype S] :
    {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) → Fintype T.Assignment
  | _, .leaf => inferInstanceAs (Fintype S)
  | _, .step _ T => T.assignmentFintype
  | _, .fork T U => @instFintypeProd _ _ T.assignmentFintype U.assignmentFintype
attribute [instance] ReplicaTree.assignmentFintype

def ReplicaTree.leaves : {steps : List (GaussianStep ι)} → ReplicaTree ι S steps → ℕ
  | _, .leaf => 1
  | _, .step _ T => T.leaves
  | _, .fork T U => T.leaves+U.leaves

 theorem ReplicaTree.leaves_pos {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) :
    0 < T.leaves := by
  induction T with
  | leaf => exact Nat.zero_lt_one
  | step _ _ ih => exact ih
  | fork _ _ ih _ => exact Nat.add_pos_left ih _

variable [Fintype ι] [Fintype S] [Nonempty S]

 

noncomputable def ReplicaTree.weight (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) → T.Assignment → (ι → ℝ) → ℝ
  | _, .leaf, σ => fun x => spinWeight w φ x σ
  | _, @ReplicaTree.step _ _ (m,q) tail T, σ =>
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
        (gaussianHierarchy w φ tail) (T.weight w φ σ)
  | _, .fork T U, σ => fun x => T.weight w φ σ.1 x*U.weight w φ σ.2 x

noncomputable def ReplicaTree.expect (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (P : T.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ σ, T.weight w φ σ x*P σ

 theorem ReplicaTree.weight_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (r : ℕ) (σ : T.Assignment) :
    BddSmooth r (T.weight w φ σ) := by
  induction T generalizing a with
  | leaf => exact bddSmooth_spinWeight hw φ r σ
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    exact (ih ha.2.2.2 σ).shiftedMean (gaussianHierarchy_regular hw φ tail ha.2.2.2 r)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q)
  | fork T U ihT ihU => exact (ihT ha σ.1).mul (ihU ha σ.2)

 theorem BddSmooth.mul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℕ} {A : E → ℝ} (hA : BddSmooth r A) (c : ℝ) :
    BddSmooth r (fun x => A x*c) := by
  simpa only [mul_comm] using hA.const_mul c

 theorem ReplicaTree.expect_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (r : ℕ) :
    BddSmooth r (T.expect w φ P) := by
  exact BddSmooth.sum Finset.univ (fun σ _ => (T.weight_smooth hw φ ha r σ).mul_const (P σ))

 theorem shiftedMean_finsetSum {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {F : E → ℝ} {m : ℝ} (s : Finset κ) {A : κ → E → ℝ}
    (hA : ∀ i ∈ s, BddSmooth 0 (A i)) {x : E}
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    shiftedMean ν m F (fun y => ∑ i ∈ s, A i y) x = ∑ i ∈ s, shiftedMean ν m F (A i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [shiftedMean,tiltedMean]
  | @insert i s hi' ih =>
    simp only [Finset.sum_insert hi']
    rw [shiftedMean_add (hA i (Finset.mem_insert_self _ _))
      (BddSmooth.sum s fun j hj => hA j (Finset.mem_insert_of_mem hj)) hi,
      ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))]

 theorem shiftedMean_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {F : E → ℝ} {m : ℝ} (c : ℝ) {x : E}
    (hi : Integrable (fun z => Real.exp (m*F (x+z))) ν) :
    shiftedMean ν m F (fun _ => c) x = c := by
  simp only [shiftedMean,tiltedMean,integral_const_mul]
  exact mul_div_cancel_right₀ c (partition_pos m hi).ne'

 theorem ReplicaTree.expect_step {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} (T : ReplicaTree ι S tail)
    (m : ℝ) (q : ι → ℝ≥0) (ha : OrderedSteps m tail) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    (ReplicaTree.step (m,q) T).expect w φ P x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
        (gaussianHierarchy w φ tail) (T.expect w φ P) x := by
  unfold ReplicaTree.expect
  rw [shiftedMean_finsetSum Finset.univ
    (fun σ _ => (T.weight_smooth hw φ ha 0 σ).mul_const (P σ))
    (gaussianHierarchy_integrable hw φ tail ha m q x)]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [ReplicaTree.weight]
  rw [show (fun y => T.weight w φ σ y*P σ) = fun y => P σ*T.weight w φ σ y by funext y; ring,
    shiftedMean_const_mul,mul_comm]

 theorem ReplicaTree.weight_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (σ : T.Assignment) (x : ι → ℝ) : 0 ≤ T.weight w φ σ x := by
  induction T generalizing a x with
  | leaf => exact spinWeight_nonneg hw φ x σ
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    exact shiftedMean_nonneg (fun y => ih ha.2.2.2 σ y)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)
  | fork T U ihT ihU => exact mul_nonneg (ihT ha σ.1 x) (ihU ha σ.2 x)

 theorem ReplicaTree.weight_sum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) : ∑ σ, T.weight w φ σ x = 1 := by
  induction T generalizing a x with
  | leaf => exact sum_spinWeight hw φ x
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    have hi := gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x
    change (∑ σ, shiftedMean _ _ _ _ x) = _
    rw [← shiftedMean_finsetSum Finset.univ (fun σ _ => T.weight_smooth hw φ ha.2.2.2 0 σ) hi]
    simp_rw [ih ha.2.2.2]
    exact shiftedMean_const 1 hi
  | fork T U ihT ihU =>
    change (∑ σ : T.Assignment × U.Assignment, T.weight w φ σ.1 x*U.weight w φ σ.2 x) = 1
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,ihU ha x,mul_one,ihT ha x]

 theorem ReplicaTree.expect_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) {P : T.Assignment → ℝ} {C : ℝ}
    (hP : ∀ σ, |P σ| ≤ C) (x : ι → ℝ) : |T.expect w φ P x| ≤ C := by
  calc
    |∑ σ, T.weight w φ σ x*P σ| ≤ ∑ σ, |T.weight w φ σ x*P σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ, T.weight w φ σ x*C := by
      apply Finset.sum_le_sum
      intro σ _
      rw [abs_mul,abs_of_nonneg (T.weight_nonneg hw φ ha σ x)]
      exact mul_le_mul_of_nonneg_left (hP σ) (T.weight_nonneg hw φ ha σ x)
    _ = C := by rw [← Finset.sum_mul,T.weight_sum hw φ ha x,one_mul]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem ReplicaTree.expect_add (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (P Q : T.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ (fun σ => P σ+Q σ) x = T.expect w φ P x+T.expect w φ Q x := by
  simp only [ReplicaTree.expect,mul_add,Finset.sum_add_distrib]

 theorem ReplicaTree.expect_const_mul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (P : T.Assignment → ℝ)
    (c : ℝ) (x : ι → ℝ) : T.expect w φ (fun σ => c*P σ) x = c*T.expect w φ P x := by
  simp only [ReplicaTree.expect,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

 theorem ReplicaTree.expect_finsetSum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {κ : Type*}
    (s : Finset κ) (P : κ → T.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ (fun σ => ∑ i ∈ s, P i σ) x = ∑ i ∈ s, T.expect w φ (P i) x := by
  simp only [ReplicaTree.expect,Finset.mul_sum]
  exact Finset.sum_comm

 theorem ReplicaTree.expect_fork (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps)
    (P : (T.fork U).Assignment → ℝ) (x : ι → ℝ) :
    (T.fork U).expect w φ P x = T.expect w φ (fun σ => U.expect w φ (fun τ => P (σ,τ)) x) x := by
  simp only [ReplicaTree.expect,ReplicaTree.weight,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

 theorem ReplicaTree.expect_fork_product (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps)
    (P : T.Assignment → ℝ) (Q : U.Assignment → ℝ) (x : ι → ℝ) :
    (T.fork U).expect w φ (fun σ => P σ.1*Q σ.2) x = T.expect w φ P x*U.expect w φ Q x := by
  rw [T.expect_fork]
  simp_rw [U.expect_const_mul,ReplicaTree.expect]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  ring

 theorem ReplicaTree.expect_indicator (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) [DecidableEq T.Assignment]
    (σ : T.Assignment) (x : ι → ℝ) :
    T.expect w φ (fun τ => if τ = σ then 1 else 0) x = T.weight w φ σ x := by
  simp [ReplicaTree.expect]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*}

def single : (steps : List (GaussianStep ι)) → ReplicaTree ι S steps
  | [] => .leaf
  | st::tail => .step st (single tail)

def singleEquiv : (steps : List (GaussianStep ι)) → (single (S := S) steps).Assignment ≃ S
  | [] => Equiv.refl S
  | _::tail => singleEquiv tail

 theorem single_leaves (steps : List (GaussianStep ι)) : (single (S := S) steps).leaves = 1 := by
  induction steps with
  | nil => rfl
  | cons st tail ih => exact ih

 

structure Placement {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) where
  coeff : ℝ
  tree : ReplicaTree ι S steps
  restrict : tree.Assignment → T.Assignment
  spin : tree.Assignment → S

def Placement.fresh {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (c : ℝ) : Placement T where
  coeff := c
  tree := T.fork (single steps)
  restrict := Prod.fst
  spin := fun σ => singleEquiv (S := S) steps σ.2

def Placement.coincide : Placement (ReplicaTree.leaf (ι := ι) (S := S)) where
  coeff := 1
  tree := .leaf
  restrict := id
  spin := id

def Placement.step (st : GaussianStep ι) {tail : List (GaussianStep ι)} {T : ReplicaTree ι S tail}
    (p : Placement T) : Placement (T.step st) where
  coeff := p.coeff
  tree := p.tree.step st
  restrict := p.restrict
  spin := p.spin

def Placement.left {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (U : ReplicaTree ι S steps) (p : Placement T) : Placement (T.fork U) where
  coeff := p.coeff
  tree := p.tree.fork U
  restrict := fun σ => (p.restrict σ.1,σ.2)
  spin := fun σ => p.spin σ.1

def Placement.right {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {U : ReplicaTree ι S steps} (p : Placement U) : Placement (T.fork U) where
  coeff := p.coeff
  tree := T.fork p.tree
  restrict := fun σ => (σ.1,p.restrict σ.2)
  spin := fun σ => p.spin σ.2

 

def attach : {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) → ℝ → List (Placement T)
  | _, .leaf, a => [Placement.coincide,Placement.fresh .leaf (a-1)]
  | _, @ReplicaTree.step _ _ st tail T, a =>
      Placement.fresh (.step st T) (a-st.1) :: (T.attach st.1).map (Placement.step st)
  | _, .fork T U, a => Placement.fresh (T.fork U) (-a) ::
      ((T.attach a).map (Placement.left U) ++ (U.attach a).map (Placement.right T))

def variation {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (Placement T)) : ℝ :=
  (ps.map fun p => |p.coeff|).sum

def mass {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (Placement T)) : ℝ :=
  (ps.map fun p => p.coeff).sum

 theorem attach_mass {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ) :
    mass (T.attach a) = a := by
  induction T generalizing a with
  | leaf => simp [mass,attach,Placement.coincide,Placement.fresh]
  | step st T ih =>
    simp only [mass,attach,List.map_cons,List.sum_cons,List.map_map,Placement.fresh,Placement.step,Function.comp_def]
    change a-st.1+mass (T.attach st.1) = a
    rw [ih]
    ring
  | fork T U ihT ihU =>
    simp only [mass,attach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map,
      Placement.fresh,Placement.left,Placement.right,Function.comp_def]
    change -a+(mass (T.attach a)+mass (U.attach a)) = a
    rw [ihT,ihU]
    ring

 theorem attach_variation {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) : variation (T.attach a) = 2*(T.leaves:ℝ)-a := by
  induction T generalizing a with
  | leaf =>
    simp only [variation,attach,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      Placement.coincide,Placement.fresh,abs_one,ReplicaTree.leaves,Nat.cast_one]
    rw [abs_of_nonpos (sub_nonpos.mpr ha.2)]
    ring
  | step st T ih =>
    simp only [variation,attach,List.map_cons,List.sum_cons,List.map_map,Placement.fresh,Placement.step,Function.comp_def]
    change |a-st.1|+variation (T.attach st.1) = _
    rw [abs_of_nonpos (sub_nonpos.mpr ha.2.1),ih ha.2.2.2]
    change _ = 2*(T.leaves:ℝ)-a
    ring
  | fork T U ihT ihU =>
    simp only [variation,attach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map,
      Placement.fresh,Placement.left,Placement.right,Function.comp_def]
    change |-a|+(variation (T.attach a)+variation (U.attach a)) = _
    rw [abs_neg,abs_of_nonneg ha.bounds.1,ihT ha,ihU ha]
    simp only [ReplicaTree.leaves,Nat.cast_add]
    ring

 theorem attach_leaves {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (p : Placement T) (hp : p ∈ T.attach a) : p.tree.leaves ≤ T.leaves+1 := by
  induction T generalizing a with
  | leaf =>
    simp [attach] at hp
    rcases hp with rfl|rfl
    · change 1 ≤ 1+1
      omega
    · simp [Placement.fresh,ReplicaTree.leaves,single_leaves]
  | step st T ih =>
    simp only [attach,List.mem_cons,List.mem_map] at hp
    rcases hp with rfl|⟨q,hq,rfl⟩
    · simp only [Placement.fresh,ReplicaTree.leaves,single_leaves,le_refl]
    · exact ih st.1 q hq
  | fork T U ihT ihU =>
    simp only [attach,List.mem_cons,List.mem_append,List.mem_map] at hp
    rcases hp with rfl|(⟨q,hq,rfl⟩|⟨q,hq,rfl⟩)
    · simp only [Placement.fresh,ReplicaTree.leaves,single_leaves,le_refl]
    · have h := ihT a q hq
      change q.tree.leaves+U.leaves ≤ (T.leaves+U.leaves)+1
      omega
    · have h := ihU a q hq
      change T.leaves+q.tree.leaves ≤ (T.leaves+U.leaves)+1
      omega

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

noncomputable def Placement.eval (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (p : Placement T)
    (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) : ℝ :=
  p.tree.expect w φ (fun σ => P (p.restrict σ)*B (p.spin σ)) x

noncomputable def rowList (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (Placement T))
    (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) : ℝ :=
  (ps.map fun p => p.coeff*p.eval w φ P B x).sum

noncomputable def row (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) : ℝ := rowList w φ (T.attach a) P B x

 theorem rowList_add (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (Placement T))
    (P Q : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    rowList w φ ps (fun σ => P σ+Q σ) B x = rowList w φ ps P B x+rowList w φ ps Q B x := by
  induction ps with
  | nil => simp [rowList]
  | cons p ps ih =>
    change p.coeff*p.eval w φ (fun σ => P σ+Q σ) B x + rowList w φ ps (fun σ => P σ+Q σ) B x =
      (p.coeff*p.eval w φ P B x+rowList w φ ps P B x)+(p.coeff*p.eval w φ Q B x+rowList w φ ps Q B x)
    rw [ih]
    have he := p.tree.expect_add w φ (fun σ => P (p.restrict σ)*B (p.spin σ))
      (fun σ => Q (p.restrict σ)*B (p.spin σ)) x
    have he' : p.eval w φ (fun σ => P σ+Q σ) B x = p.eval w φ P B x+p.eval w φ Q B x := by
      simpa only [Placement.eval,add_mul] using he
    rw [he']
    ring

 theorem rowList_const_mul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (Placement T))
    (P : T.Assignment → ℝ) (B : S → ℝ) (c : ℝ) (x : ι → ℝ) :
    rowList w φ ps (fun σ => c*P σ) B x = c*rowList w φ ps P B x := by
  induction ps with
  | nil => simp [rowList]
  | cons p ps ih =>
    change p.coeff*p.eval w φ (fun σ => c*P σ) B x + rowList w φ ps (fun σ => c*P σ) B x =
      c*(p.coeff*p.eval w φ P B x+rowList w φ ps P B x)
    rw [ih]
    have he : p.eval w φ (fun σ => c*P σ) B x = c*p.eval w φ P B x := by
      simp only [Placement.eval,mul_assoc,p.tree.expect_const_mul]
    rw [he]
    ring

 theorem rowList_finsetSum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (Placement T))
    {κ : Type*} (s : Finset κ) (P : κ → T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    rowList w φ ps (fun σ => ∑ i ∈ s, P i σ) B x = ∑ i ∈ s, rowList w φ ps (P i) B x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rowList,Placement.eval,ReplicaTree.expect]
  | @insert i s hi ih => simp only [Finset.sum_insert hi,rowList_add,ih]

 theorem rowList_indicator_expand (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (Placement T))
    [DecidableEq T.Assignment] (P : T.Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    ∑ σ, rowList w φ ps (fun τ => if τ = σ then 1 else 0) B x*P σ = rowList w φ ps P B x := by
  have he : P = fun τ => ∑ σ, P σ*(if τ = σ then 1 else 0) := by funext τ; simp
  conv_rhs => rw [he,rowList_finsetSum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [rowList_const_mul,mul_comm]

 theorem Placement.eval_left (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (p : Placement T)
    (U : ReplicaTree ι S steps) (P : (T.fork U).Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    (p.left U).eval w φ P B x = U.expect w φ (fun τ => p.eval w φ (fun σ => P (σ,τ)) B x) x := by
  change (p.tree.fork U).expect w φ (fun σ => P (p.restrict σ.1,σ.2)*B (p.spin σ.1)) x = _
  rw [expect_fork]
  simp only [Placement.eval,ReplicaTree.expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ring

 theorem Placement.eval_right (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {U : ReplicaTree ι S steps}
    (p : Placement U) (P : (T.fork U).Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    (p.right T).eval w φ P B x = T.expect w φ (fun σ => p.eval w φ (fun τ => P (σ,τ)) B x) x := by
  change (T.fork p.tree).expect w φ (fun σ => P (σ.1,p.restrict σ.2)*B (p.spin σ.2)) x = _
  exact expect_fork w φ T p.tree _ x

 theorem rowList_map_left (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (U : ReplicaTree ι S steps)
    (ps : List (Placement T)) (P : (T.fork U).Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    rowList w φ (ps.map (Placement.left U)) P B x =
      U.expect w φ (fun τ => rowList w φ ps (fun σ => P (σ,τ)) B x) x := by
  induction ps with
  | nil => simp [rowList,ReplicaTree.expect]
  | cons p ps ih =>
    change p.coeff*(p.left U).eval w φ P B x + rowList w φ (ps.map (Placement.left U)) P B x =
      U.expect w φ (fun τ => p.coeff*p.eval w φ (fun σ => P (σ,τ)) B x+rowList w φ ps (fun σ => P (σ,τ)) B x) x
    rw [Placement.eval_left,ih,U.expect_add,U.expect_const_mul]

 theorem rowList_map_right (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {U : ReplicaTree ι S steps}
    (ps : List (Placement U)) (P : (T.fork U).Assignment → ℝ) (B : S → ℝ) (x : ι → ℝ) :
    rowList w φ (ps.map (Placement.right T)) P B x =
      T.expect w φ (fun σ => rowList w φ ps (fun τ => P (σ,τ)) B x) x := by
  induction ps with
  | nil => simp [rowList,ReplicaTree.expect]
  | cons p ps ih =>
    change p.coeff*(p.right T).eval w φ P B x + rowList w φ (ps.map (Placement.right T)) P B x =
      T.expect w φ (fun σ => p.coeff*p.eval w φ (fun τ => P (σ,τ)) B x+rowList w φ ps (fun τ => P (σ,τ)) B x) x
    rw [Placement.eval_right,ih,T.expect_add,T.expect_const_mul]

variable [Nonempty S]

 theorem rowList_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (Placement T)) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (B : S → ℝ) (r : ℕ) : BddSmooth r (rowList w φ ps P B) := by
  induction ps with
  | nil => exact BddSmooth.const r 0
  | cons p ps ih => exact ((p.tree.expect_smooth hw φ ha _ r).const_mul p.coeff).add ih

 theorem rowList_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (Placement T)) {a : ℝ} (ha : OrderedSteps a steps)
    {P : T.Assignment → ℝ} {B : S → ℝ} {C D : ℝ} (hC : 0 ≤ C)
    (hP : ∀ σ, |P σ| ≤ C) (hB : ∀ σ, |B σ| ≤ D) (x : ι → ℝ) :
    |rowList w φ ps P B x| ≤ variation ps*C*D := by
  induction ps with
  | nil => simp [rowList,variation]
  | cons p ps ih =>
    have hp := p.tree.expect_abs_le hw φ ha
      (show ∀ σ, |P (p.restrict σ)*B (p.spin σ)| ≤ C*D from fun σ => by
        rw [abs_mul]; exact mul_le_mul (hP _) (hB _) (abs_nonneg _) hC) x
    change |p.coeff*p.eval w φ P B x+rowList w φ ps P B x| ≤ _
    calc
      _ ≤ |p.coeff*p.eval w φ P B x|+|rowList w φ ps P B x| := abs_add_le _ _
      _ ≤ |p.coeff| *(C*D)+variation ps*C*D := by
        apply add_le_add _ ih
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = _ := by simp only [variation,List.map_cons,List.sum_cons]; ring

 theorem row_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) {P : T.Assignment → ℝ} {B : S → ℝ} {C D : ℝ}
    (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C) (hB : ∀ σ, |B σ| ≤ D) (x : ι → ℝ) :
    |T.row w φ a P B x| ≤ (2*(T.leaves:ℝ)-a)*C*D := by
  simpa only [row,attach_variation T ha] using rowList_abs_le hw φ (T.attach a) ha hC hP hB x

 theorem single_expect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (B : S → ℝ) (x : ι → ℝ) :
    (single steps).expect w φ (fun σ => B (singleEquiv (S := S) steps σ)) x =
      gaussianHierarchyMean w φ B steps x := by
  induction steps generalizing a x with
  | nil => rfl
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    change (ReplicaTree.step (m,q) (single tail)).expect w φ
      (fun σ => B (singleEquiv (S := S) tail σ)) x = _
    rw [expect_step hw φ _ m q ha.2.2.2]
    have he : (single tail).expect w φ (fun σ => B (singleEquiv (S := S) tail σ)) =
        gaussianHierarchyMean w φ B tail := by funext y; exact ih ha.2.2.2 y
    rw [he]
    rfl

 theorem Placement.eval_fresh {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (B : S → ℝ) (c : ℝ) (x : ι → ℝ) :
    (Placement.fresh T c).eval w φ P B x =
      T.expect w φ P x*gaussianHierarchyMean w φ B steps x := by
  change (T.fork (single steps)).expect w φ (fun σ => P σ.1*B (singleEquiv (S := S) steps σ.2)) x = _
  rw [expect_fork_product w φ T (single steps) P (fun σ => B (singleEquiv (S := S) steps σ)) x,
    single_expect hw φ steps ha]

end SKFluctuations.Hierarchy.ReplicaTree

end

end OAI
