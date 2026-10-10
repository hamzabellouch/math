import Mathlib
import OAI.Probability.SKFluctuations.PositiveMass

namespace OAI

/-! Boundary Cost Congr. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

theorem boundaryCost_congr (as : List PositiveMass) {q r q' r' : ℕ → ℝ}
    (hq : ∀ j, j+1 < as.length → q j = q' j) (hr : ∀ j, j+1 < as.length → r j = r' j) :
    boundaryCost as q r = boundaryCost as q' r' := by
  induction as generalizing q r q' r' with
  | nil => rfl
  | cons a as ih =>
    cases as with
    | nil => rfl
    | cons b as =>
      simp only [boundaryCost]
      rw [hq 0 (by simp),hr 0 (by simp)]
      congr 1
      apply ih
      · intro j hj
        exact hq (j+1) (by simpa only [List.length_cons] using Nat.add_lt_add_right hj 1)
      · intro j hj
        exact hr (j+1) (by simpa only [List.length_cons] using Nat.add_lt_add_right hj 1)

theorem rootBoundaryCost_congr (as : List PositiveMass) {q r q' r' : ℕ → ℝ}
    (hq : ∀ j, j < as.length → q j = q' j) (hr : ∀ j, j < as.length → r j = r' j) :
    rootBoundaryCost as q r = rootBoundaryCost as q' r' := by
  cases as with
  | nil => rfl
  | cons a as =>
    simp only [rootBoundaryCost]
    rw [hq 0 (by simp),hr 0 (by simp)]
    congr 1
    exact boundaryCost_congr (a::as) (fun j hj => hq (j+1) hj) (fun j hj => hr (j+1) hj)

theorem rootBoundaryCost_uniform {as : List PositiveMass} {q r : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ a ∈ as, a.val ≤ 1) (hm : ∀ j, j ≤ as.length → |q j-r j| ≤ M) :
    rootBoundaryCost as q r ≤ M := by
  cases as with
  | nil => exact hM
  | cons a as =>
    have hb := boundaryCost_le hM ho hu (q := fun j => q (j+1)) (r := fun j => r (j+1))
      (fun j hj => hm (j+1) (by omega))
    have h0 := mul_le_mul_of_nonneg_left (hm 0 (by simp)) a.property.le
    change a.val*|q 0-r 0|+_ ≤ M
    nlinarith

 
noncomputable def correctedDiagonalRoot {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
    (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (C : Fin (n+1) → ℝ)
    (as : List PositiveMass) (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  diagonalRootBoundary w φ as l q x-(1/2:ℝ)*∑ i, (q as.length i-l i)*C i

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem correctedDiagonalRoot_comparison {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (C D : Fin (n+1) → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    {l : Fin (n+1) → ℝ} {q r : ℕ → Fin (n+1) → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i) (x : Fin (n+1) → ℝ) :
    |correctedDiagonalRoot w φ C as l q x-correctedDiagonalRoot w φ C as l r x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*rootBoundaryCost (as++[⟨1,by norm_num⟩])
        (fun j => q j i) (fun j => r j i) := by
  let t : Fin (n+1) → ℝ := fun i => max (q as.length i) (r as.length i)
  let aq := extendBoundary q as.length t
  let ar := extendBoundary r as.length t
  let one : PositiveMass := ⟨1,by norm_num⟩
  have htq : ∀ i, q as.length i ≤ t i := fun i => le_max_left _ _
  have htr : ∀ i, r as.length i ≤ t i := fun i => le_max_right _ _
  have ho' : (as++[one]).Pairwise (fun a b => a.val ≤ b.val) := by
    apply List.pairwise_append.mpr
    refine ⟨ho,by simp,?_⟩
    intro a ha b hb
    have he : b = one := List.mem_singleton.mp hb
    subst b
    exact hu a ha
  have hu' : ∀ a ∈ as++[one], a.val ≤ 1 := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hu a ha
    · have he := List.mem_singleton.mp ha
      subst a
      exact le_rfl
  have hq' : ∀ i, Monotone (fun j => aq j i) := extendBoundary_monotone hq htq
  have hr' : ∀ i, Monotone (fun j => ar j i) := extendBoundary_monotone hr htr
  have hq0 : aq 0 = q 0 := extendBoundary_le q as.length t (Nat.zero_le _)
  have hr0 : ar 0 = r 0 := extendBoundary_le r as.length t (Nat.zero_le _)
  have hend : aq (as++[one]).length = ar (as++[one]).length := by
    simp only [aq,ar,List.length_append,List.length_singleton,extendBoundary_gt _ _ _ (Nat.lt_add_one _)]
  have hb := diagonalRoot_comparison hw φ D hB (as++[one]) ho' hu' hq' hr'
    (by simpa only [hq0] using hql) (by simpa only [hr0] using hrl) hend x
  have heq := diagonalRoot_append_one hw φ C hC as ho hu l q t htq x
  have her := diagonalRoot_append_one hw φ C hC as ho hu l r t htr x
  change |diagonalRootBoundary w φ (as++[one]) l aq x-diagonalRootBoundary w φ (as++[one]) l ar x| ≤ _ at hb
  rw [heq,her] at hb
  have hc (i) : rootBoundaryCost (as++[one]) (fun j => aq j i) (fun j => ar j i) =
      rootBoundaryCost (as++[one]) (fun j => q j i) (fun j => r j i) := by
    apply rootBoundaryCost_congr
    · intro j hj
      rw [show aq j = q j from extendBoundary_le q as.length t (by simpa only [List.length_append,List.length_singleton,Nat.lt_add_one_iff] using hj)]
    · intro j hj
      rw [show ar j = r j from extendBoundary_le r as.length t (by simpa only [List.length_append,List.length_singleton,Nat.lt_add_one_iff] using hj)]
  simp_rw [hc] at hb
  convert hb using 1
  congr 1
  simp only [correctedDiagonalRoot,sub_mul,Finset.sum_sub_distrib]
  ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uC vC

 

inductive ClockTree (S : Type vC) : List PositiveMass → Type vC where
  | leaf : ClockTree S []
  | step (a : PositiveMass) {as : List PositiveMass} (T : ClockTree S as) : ClockTree S (a::as)
  | fork {as : List PositiveMass} (T U : ClockTree S as) : ClockTree S as

variable {S : Type vC} {ι : Type uC}

@[reducible] def ClockTree.Assignment : {as : List PositiveMass} → ClockTree S as → Type vC
  | _, .leaf => S
  | _, .step _ T => T.Assignment
  | _, .fork T U => T.Assignment × U.Assignment

@[instance_reducible] noncomputable def ClockTree.assignmentFintype [Fintype S] :
    {as : List PositiveMass} → (T : ClockTree S as) → Fintype T.Assignment
  | _, .leaf => inferInstanceAs (Fintype S)
  | _, .step _ T => T.assignmentFintype
  | _, .fork T U => @instFintypeProd _ _ T.assignmentFintype U.assignmentFintype
attribute [instance] ClockTree.assignmentFintype

def MassOrdered (a : ℝ) : List PositiveMass → Prop
  | [] => 0 ≤ a ∧ a ≤ 1
  | b::as => 0 ≤ a ∧ a ≤ b.val ∧ MassOrdered b.val as

def clockSteps : List PositiveMass → (ℕ → ι → ℝ≥0) → List (GaussianStep ι)
  | [], _ => []
  | a::as, q => ((a:ℝ),q 0)::clockSteps as (fun j => q (j+1))

def ClockTree.realize : {as : List PositiveMass} → (T : ClockTree S as) →
    (q : ℕ → ι → ℝ≥0) → ReplicaTree ι S (clockSteps as q)
  | _, .leaf, _ => .leaf
  | _, .step a T, q => .step ((a:ℝ),q 0) (T.realize (fun j => q (j+1)))
  | _, .fork T U, q => .fork (T.realize q) (U.realize q)

noncomputable def ClockTree.assignmentEquiv : {as : List PositiveMass} →
    (T : ClockTree S as) → (q : ℕ → ι → ℝ≥0) → T.Assignment ≃ (T.realize q).Assignment
  | _, .leaf, _ => Equiv.refl _
  | _, .step _ T, q => T.assignmentEquiv (fun j => q (j+1))
  | _, .fork T U, q => Equiv.prodCongr (T.assignmentEquiv q) (U.assignmentEquiv q)

def ClockTree.leaves : {as : List PositiveMass} → ClockTree S as → ℕ
  | _, .leaf => 1
  | _, .step _ T => T.leaves
  | _, .fork T U => T.leaves+U.leaves

 theorem ClockTree.realize_leaves {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0) :
    (T.realize q).leaves = T.leaves := by
  induction T generalizing q with
  | leaf => rfl
  | step a T ih => exact ih _
  | fork T U ihT ihU => exact congrArg₂ (·+·) (ihT q) (ihU q)

variable [Fintype ι] [Fintype S]

noncomputable def ClockTree.weight (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (σ : T.Assignment) (x : ι → ℝ) : ℝ :=
  (T.realize q).weight w φ (T.assignmentEquiv q σ) x

noncomputable def ClockTree.expect (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (x : ι → ℝ) : ℝ := ∑ σ, T.weight w φ q σ x*P σ

 theorem ClockTree.expect_realize (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    T.expect w φ q P x = (T.realize q).expect w φ (fun σ => P ((T.assignmentEquiv q).symm σ)) x := by
  unfold ClockTree.expect ReplicaTree.expect ClockTree.weight
  exact Fintype.sum_equiv (T.assignmentEquiv q) _ _ (fun σ => by simp)

 theorem ClockTree.weight_leaf (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℕ → ι → ℝ≥0) (σ : S) (x : ι → ℝ) :
    (ClockTree.leaf : ClockTree S []).weight w φ q σ x = spinWeight w φ x σ := rfl

 theorem ClockTree.weight_step (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (a : PositiveMass) (T : ClockTree S as)
    (q : ℕ → ι → ℝ≥0) (σ : T.Assignment) (x : ι → ℝ) :
    (T.step a).weight w φ q σ x = shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) (a:ℝ)
      (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
      (T.weight w φ (fun j => q (j+1)) σ) x := rfl

 theorem ClockTree.weight_fork (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T U : ClockTree S as) (q : ℕ → ι → ℝ≥0)
    (σ : (T.fork U).Assignment) (x : ι → ℝ) :
    (T.fork U).weight w φ q σ x = T.weight w φ q σ.1 x*U.weight w φ q σ.2 x := rfl

omit [Fintype ι] in
 theorem clockSteps_ordered {as : List PositiveMass} {a : ℝ}
    (ha : MassOrdered a as) (q : ℕ → ι → ℝ≥0) : OrderedSteps a (clockSteps as q) := by
  induction as generalizing a q with
  | nil => exact ha
  | cons b as ih => exact ⟨ha.1, ha.2.1, b.property, ih ha.2.2 _⟩

variable [Nonempty S]

 theorem ClockTree.weight_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (σ : T.Assignment) (r : ℕ) :
    BddSmooth r (T.weight w φ q σ) := (T.realize q).weight_smooth hw φ (clockSteps_ordered ha q) r _

 theorem ClockTree.weight_probability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (x : ι → ℝ) :
    (∀ σ, 0 ≤ T.weight w φ q σ x) ∧ ∑ σ, T.weight w φ q σ x = 1 := by
  constructor
  · intro σ
    exact (T.realize q).weight_nonneg hw φ (clockSteps_ordered ha q) _ x
  · calc
      _ = ∑ σ, (T.realize q).weight w φ σ x :=
        Fintype.sum_equiv (T.assignmentEquiv q) _ _ (fun _ => rfl)
      _ = 1 := (T.realize q).weight_sum hw φ (clockSteps_ordered ha q) x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uC vC
variable {S : Type vC} {ι : Type uC}

def ClockTree.cut : {as : List PositiveMass} → (T : ClockTree S as) → (j : ℕ) →
    (q : ℕ → ι → ℝ≥0) → BoundaryTree ι (ClockTree S (as.drop j)) (clockSteps (as.take j) q)
  | _,T,0,_ => .leaf T
  | _,.leaf,_+1,_ => .leaf .leaf
  | _,.step a T,j+1,q => .step ((a:ℝ),q 0) (T.cut j (fun k => q (k+1)))
  | _,.fork T U,j+1,q => .fork (T.cut (j+1) q) (U.cut (j+1) q)

noncomputable def ClockTree.cutAssignmentEquiv : {as : List PositiveMass} → (T : ClockTree S as) →
    (j : ℕ) → (q : ℕ → ι → ℝ≥0) →
    T.Assignment ≃ (T.cut j q).Assignment (fun U => U.Assignment)
  | _,.leaf,0,_ => Equiv.refl S
  | _,.step _ T,0,_ => Equiv.refl T.Assignment
  | _,.fork T U,0,_ => Equiv.refl (T.Assignment × U.Assignment)
  | _,.leaf,_+1,_ => Equiv.refl S
  | _,.step _ T,j+1,q => T.cutAssignmentEquiv j (fun k => q (k+1))
  | _,.fork T U,j+1,q => Equiv.prodCongr (T.cutAssignmentEquiv (j+1) q) (U.cutAssignmentEquiv (j+1) q)

 theorem clockSteps_append (as bs : List PositiveMass) (q : ℕ → ι → ℝ≥0) :
    clockSteps (as++bs) q = clockSteps as q ++ clockSteps bs (fun j => q (as.length+j)) := by
  induction as generalizing q with
  | nil => simp [clockSteps]
  | cons a as ih =>
    simp only [List.cons_append,clockSteps,ih,List.length_cons]
    congr 2
    congr 1
    funext j
    congr 1
    omega

 theorem clockSteps_take_drop (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) (j : ℕ) (hj : j ≤ as.length) :
    clockSteps as q = clockSteps (as.take j) q ++ clockSteps (as.drop j) (fun k => q (j+k)) := by
  conv_lhs => rw [← List.take_append_drop j as,clockSteps_append]
  rw [List.length_take,Nat.min_eq_left hj]

 theorem gaussianHierarchy_prefix {S : Type*} [Fintype ι] [Fintype S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (cs ds : List (GaussianStep ι)) :
    gaussianHierarchy w φ (cs++ds) = prefixContinuation cs (gaussianHierarchy w φ ds) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨a,q⟩
    change shiftedContinuation _ a (gaussianHierarchy w φ (cs++ds)) = _
    rw [ih]
    rfl

variable [Fintype ι] [Fintype S]

 theorem ClockTree.cut_weight (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (j : ℕ) (q : ℕ → ι → ℝ≥0)
    (hj : j ≤ as.length) (σ : T.Assignment) (x : ι → ℝ) :
    T.weight w φ q σ x = (T.cut j q).weight
      (fun _ => gaussianHierarchy w φ (clockSteps (as.drop j) (fun k => q (j+k))))
      (fun U τ _ => U.weight w φ (fun k => q (j+k)) τ)
      (T.cutAssignmentEquiv j q σ) 0 x := by
  induction T generalizing j q x with
  | leaf =>
    have hj0 : j = 0 := by simpa only [List.length_nil,Nat.le_zero] using hj
    subst j
    simp [ClockTree.cut,ClockTree.cutAssignmentEquiv,BoundaryTree.weight]
    rfl
  | @step a as T ih =>
    cases j with
    | zero =>
      simp [ClockTree.cut,ClockTree.cutAssignmentEquiv,BoundaryTree.weight]
      rfl
    | succ j =>
      have hj' : j ≤ as.length := by simpa using hj
      change shiftedMean _ a.val (gaussianHierarchy w φ (clockSteps as (fun k => q (k+1))))
        (T.weight w φ (fun k => q (k+1)) σ) x = _
      have he := clockSteps_take_drop as (fun k => q (k+1)) j hj'
      rw [he,gaussianHierarchy_prefix]
      have hq : (fun k => q (j+k+1)) = (fun k => q (j+1+k)) := by
        funext k
        congr 1
        omega
      have hw : T.weight w φ (fun k => q (k+1)) σ = fun y => (T.cut j (fun k => q (k+1))).weight
          (fun _ => gaussianHierarchy w φ (clockSteps (as.drop j) (fun k => q (j+k+1))))
          (fun U τ _ => U.weight w φ (fun k => q (j+k+1)) τ)
          (T.cutAssignmentEquiv j (fun k => q (k+1)) σ) 0 y := by
        funext y
        exact ih j _ hj' σ y
      rw [hw]
      dsimp only [ClockTree.cut,ClockTree.cutAssignmentEquiv,BoundaryTree.weight,List.drop_succ_cons,List.take_succ_cons,clockSteps]
      rw [hq]
      simp only [List.drop_succ_cons]
      rfl
  | @fork as T U ihT ihU =>
    cases j with
    | zero =>
      simp [ClockTree.cut,ClockTree.cutAssignmentEquiv,BoundaryTree.weight]
      rfl
    | succ j =>
      change T.weight w φ q σ.1 x*U.weight w φ q σ.2 x = _
      rw [ihT (j+1) q hj σ.1 x,ihU (j+1) q hj σ.2 x]
      rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*}

 
def mixClocks (j : ℕ) (q r : ℕ → ι → ℝ≥0) (i : ℕ) : ι → ℝ≥0 :=
  if i < j then q i else r (i-j)

 theorem mixClocks_zero (q r : ℕ → ι → ℝ≥0) : mixClocks 0 q r = r := by
  funext i
  simp [mixClocks]

 theorem mixClocks_succ_zero (j : ℕ) (q r : ℕ → ι → ℝ≥0) : mixClocks (j+1) q r 0 = q 0 := by
  simp [mixClocks]

 theorem mixClocks_succ_shift (j : ℕ) (q r : ℕ → ι → ℝ≥0) :
    (fun i => mixClocks (j+1) q r (i+1)) = mixClocks j (fun i => q (i+1)) r := by
  funext i
  simp [mixClocks]

 theorem clockSteps_mix (as : List PositiveMass) (j : ℕ) (q r : ℕ → ι → ℝ≥0)
    (hj : j ≤ as.length) :
    clockSteps as (mixClocks j q r) = clockSteps (as.take j) q ++ clockSteps (as.drop j) r := by
  induction as generalizing j q with
  | nil =>
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | cons a as ih =>
    cases j with
    | zero => simp [mixClocks_zero,clockSteps]
    | succ j =>
      have hj' : j ≤ as.length := by simpa using hj
      simp only [clockSteps,mixClocks_succ_zero,mixClocks_succ_shift,List.take_succ_cons,
        List.drop_succ_cons,List.cons_append,ih _ _ hj']

variable [Fintype ι] [Fintype S]

 

 theorem ClockTree.cut_mix_weight (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (j : ℕ) (q r : ℕ → ι → ℝ≥0)
    (hj : j ≤ as.length) (σ : T.Assignment) (x : ι → ℝ) :
    T.weight w φ (mixClocks j q r) σ x = (T.cut j q).weight
      (fun _ => gaussianHierarchy w φ (clockSteps (as.drop j) r))
      (fun U τ _ => U.weight w φ r τ)
      (T.cutAssignmentEquiv j q σ) 0 x := by
  induction T generalizing j q x with
  | leaf =>
    have hj0 : j = 0 := by simpa only [List.length_nil,Nat.le_zero] using hj
    subst j
    simp [ClockTree.cut,ClockTree.cutAssignmentEquiv,BoundaryTree.weight,mixClocks_zero]
    rfl
  | @step a as T ih =>
    cases j with
    | zero =>
      simp [ClockTree.cut,ClockTree.cutAssignmentEquiv,BoundaryTree.weight,mixClocks_zero]
      rfl
    | succ j =>
      have hj' : j ≤ as.length := by simpa using hj
      rw [ClockTree.weight_step,mixClocks_succ_zero,mixClocks_succ_shift,
        clockSteps_mix as j _ r hj',gaussianHierarchy_prefix]
      have hw : T.weight w φ (mixClocks j (fun k => q (k+1)) r) σ = fun y =>
          (T.cut j (fun k => q (k+1))).weight
          (fun _ => gaussianHierarchy w φ (clockSteps (as.drop j) r))
          (fun U τ _ => U.weight w φ r τ)
          (T.cutAssignmentEquiv j (fun k => q (k+1)) σ) 0 y := by
        funext y
        exact ih j _ hj' σ y
      rw [hw]
      rfl
  | @fork as T U ihT ihU =>
    cases j with
    | zero =>
      simp [ClockTree.cut,ClockTree.cutAssignmentEquiv,BoundaryTree.weight,mixClocks_zero]
      rfl
    | succ j =>
      rw [ClockTree.weight_fork,ihT (j+1) q hj σ.1 x,ihU (j+1) q hj σ.2 x]
      rfl

 theorem ClockTree.cut_mix_distance (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (j : ℕ) (q r s : ℕ → ι → ℝ≥0)
    (hj : j ≤ as.length) (x : ι → ℝ) :
    ∑ σ, |T.weight w φ (mixClocks j q r) σ x-T.weight w φ (mixClocks j q s) σ x| =
    ∑ σ, |(T.cut j q).weight (fun _ => gaussianHierarchy w φ (clockSteps (as.drop j) r))
      (fun U τ _ => U.weight w φ r τ) σ 0 x-
      (T.cut j q).weight (fun _ => gaussianHierarchy w φ (clockSteps (as.drop j) s))
      (fun U τ _ => U.weight w φ s τ) σ 0 x| := by
  apply Fintype.sum_equiv (T.cutAssignmentEquiv j q)
  intro σ
  rw [T.cut_mix_weight w φ j q r hj σ x,T.cut_mix_weight w φ j q s hj σ x]

variable [Nonempty S]

 

 theorem ClockTree.cut_mix_stability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (j : ℕ) (q r s : ℕ → ι → ℝ≥0) (hj : j ≤ as.length)
    {a m K : ℝ} (ha : MassOrdered a (as.drop j)) (hK : 0 ≤ K)
    (hF : ∀ y, |gaussianHierarchy w φ (clockSteps (as.drop j) r) y-
      gaussianHierarchy w φ (clockSteps (as.drop j) s) y| ≤ K)
    (E : ClockTree S (as.drop j) → ℝ)
    (hE : ∀ U y, ∑ σ, |U.weight w φ r σ y-U.weight w φ s σ y| ≤ E U)
    (hO : PrefixOrdered 0 m (clockSteps (as.take j) q)) (x : ι → ℝ) :
    ∑ σ, |T.weight w φ (mixClocks j q r) σ x-T.weight w φ (mixClocks j q s) σ x| ≤
      (T.cut j q).budget (fun U => E U+2*m*K) := by
  rw [T.cut_mix_distance w φ j q r s hj x]
  exact (T.cut j q).finite_stability
    (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ha s) 0).1.choose_spec
    (gaussianHierarchy_regular hw φ _ (clockSteps_ordered ha r) 0).1.choose_spec hK hF
    (fun U σ => (U.weight_smooth hw φ ha s σ 0).continuous)
    (fun U σ => (U.weight_smooth hw φ ha r σ 0).continuous)
    (fun U y => U.weight_probability hw φ ha s y)
    (fun U y => U.weight_probability hw φ ha r y) E hE hO x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem ReplicaTree.diagonal_covariance_transfer {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep (Fin (n+1)))}
    (R : ReplicaTree (Fin (n+1)) S steps) {a b : ℝ} (ho : OrderedSteps b steps)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb1 : b ≤ 1)
    (u v z : Fin (n+1) → ℝ≥0) (x : Fin (n+1) → ℝ) :
    ∑ σ : R.Assignment,
      |((R.step (b,z)).step (a,fun i => u i+v i)).weight w φ σ x-
        ((R.step (b,fun i => v i+z i)).step (a,u)).weight w φ σ x| ≤
      (|a-b| *(2*(R.leaves:ℝ)+3)+a*|a-b|)*∑ i, (v i:ℝ)*(D i)^2 := by
  classical
  let F := gaussianHierarchy w φ steps
  let G := gaussianHierarchy w φ ((b,z)::steps)
  let Q : BoundaryTree (Fin (n+1)) Unit [(a,u)] := (BoundaryTree.leaf () : BoundaryTree (Fin (n+1)) Unit []).step (a,u)
  let W : Unit → ReplicaTree (Fin (n+1)) S ((b,z)::steps) := fun _ => R.step (b,z)
  have hF := (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec
  have hGA : OrderedSteps a ((b,z)::steps) := ⟨ha.le,hab,hb,ho⟩
  have hGB : OrderedSteps b ((b,z)::steps) := ⟨hb.le,le_rfl,hb,ho⟩
  have hG := (gaussianHierarchy_regular hw φ ((b,z)::steps) hGB 0).1.choose_spec
  have hd (i : Fin (n+1)) (σ : S) :
      |φ σ (diagonalDriver v (Pi.single i 1))| ≤ Real.sqrt (v i)*D i := by
    rw [diagonalDriver_single,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hB i σ) (Real.sqrt_nonneg _)
  have hQ : PrefixOrdered 0 a [(a,u)] := ⟨le_rfl,ha.le,ha,ha.le,le_rfl⟩
  have hh := Q.actual_mass_change hw φ (diagonalDriver v) W hGA hGB ha hb (hab.trans hb1) hb1
    (fun i => Real.sqrt (v i)*D i) (fun i => mul_nonneg (Real.sqrt_nonneg _) (hD i)) hd
    hQ (by norm_num : (0:ℝ) ≤ 1) x
  dsimp only [Q,W,BoundaryTree.weight,BoundaryTree.budget,prefixContinuation] at hh
  simp only [linearClockContinuation,ReplicaTree.atomicClock,linearClockTest,
    Real.toNNReal_one,linearGaussian_diagonal,mul_one,mul_pow,Real.sq_sqrt (v _).coe_nonneg] at hh
  have hei (σ : R.Assignment) : (R.step (b,z)).expect w φ (fun τ => if τ = σ then 1 else 0) =
      (R.step (b,z)).weight w φ σ := funext fun y => (R.step (b,z)).expect_indicator w φ σ y
  simp_rw [hei] at hh
  change (∑ σ : R.Assignment,
    |shiftedMean (Measure.pi fun i => gaussianReal 0 (u i)) a
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a G)
      (shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) a G ((R.step (b,z)).weight w φ σ)) x-
    shiftedMean (Measure.pi fun i => gaussianReal 0 (u i)) a
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) b G)
      (shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) b G ((R.step (b,z)).weight w φ σ)) x|)
      ≤ |a-b| *(2*((R.step (b,z)).leaves:ℝ)+3)*(∑ i, (v i:ℝ)*(D i)^2)+
        2*a*(|a-b|/2*(∑ i, (v i:ℝ)*(D i)^2)) at hh
  have hp : shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) b G =
      gaussianHierarchy w φ ((b,fun i => v i+z i)::steps) := by
    funext y
    exact shiftedContinuation_productGaussian_add hF hb.ne' v z y
  have hm (σ : R.Assignment) : shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) b G
      ((R.step (b,z)).weight w φ σ) = (R.step (b,fun i => v i+z i)).weight w φ σ := by
    funext y
    exact shiftedMean_productGaussian_add hF (R.weight_smooth hw φ ho 0 σ) hb.ne' v z y
  have hl (σ : R.Assignment) : shiftedMean (Measure.pi fun i => gaussianReal 0 (u i)) a
      (shiftedContinuation (Measure.pi fun i => gaussianReal 0 (v i)) a G)
      (shiftedMean (Measure.pi fun i => gaussianReal 0 (v i)) a G ((R.step (b,z)).weight w φ σ)) x =
      ((R.step (b,z)).step (a,fun i => u i+v i)).weight w φ σ x :=
    shiftedMean_productGaussian_add hG ((R.step (b,z)).weight_smooth hw φ hGB 0 σ) ha.ne' u v x
  simp_rw [hl,hp,hm] at hh
  simp only [ReplicaTree.leaves] at hh
  convert hh using 1 <;> first | rfl | ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
universe uB vB wB
variable {ι : Type uB} {β : Type vB} {κ : β → Type wB} [Fintype ι]

 theorem ParametricContinuous.mulTest {U : Set ℝ} {C : ℝ≥0} {K J : ℝ}
    {F A B : ℝ → (ι → ℝ) → ℝ} (hA : ParametricContinuous U C K F A)
    (hB : ParametricContinuous U C J F B) :
    ParametricContinuous U C (K*J) F (fun t x => A t x*B t x) := by
  refine ⟨mul_nonneg hA.nonneg hB.nonneg,hA.spatial,?_,?_,hA.potential,?_⟩
  · exact fun t ht => (hA.test_spatial t ht).mul (hB.test_spatial t ht)
  · intro t ht x
    rw [abs_mul]
    exact mul_le_mul (hA.bounded t ht x) (hB.bounded t ht x) (abs_nonneg _) hA.nonneg
  · exact fun x => (hA.tested x).mul (hB.tested x)

 

theorem BoundaryTree.parametricContinuous {U : Set ℝ} {C : ℝ≥0}
    {F : ℝ → (ι → ℝ) → ℝ} {W : ∀ b, κ b → ℝ → (ι → ℝ) → ℝ}
    (hW : ∀ b σ, ∃ K, ParametricContinuous U C K F (W b σ))
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front)
    (hm : ∀ st ∈ front, 0 < st.1) (σ : T.Assignment κ) :
    ∃ K, ParametricContinuous U C K (fun t => prefixContinuation front (F t))
      (T.weight F W σ) := by
  induction T with
  | leaf b => exact hW b σ
  | @step st tail T ih =>
    obtain ⟨K,hK⟩ := ih (fun c hc => hm c (List.mem_cons_of_mem _ hc)) σ
    exact ⟨K,hK.step (hm st List.mem_cons_self) st.2⟩
  | fork T V ihT ihV =>
    obtain ⟨K,hK⟩ := ihT hm σ.1
    obtain ⟨J,hJ⟩ := ihV hm σ.2
    exact ⟨K*J,hK.mulTest hJ⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 
theorem abs_sub_le_mul_of_deriv_interior {f g : ℝ → ℝ} {K : ℝ}
    (hc : ContinuousOn f (Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt f (g t) t)
    (hb : ∀ t, 0 < t → |g t| ≤ K) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |f t-f s| ≤ K*|t-s| := by
  have hcase {s t : ℝ} (hs : 0 ≤ s) (h : s < t) : |f t-f s| ≤ K*(t-s) := by
    obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope f g h
      (hc.mono (fun _ hy => hs.trans hy.1)) (fun u hu => hd u (hs.trans_lt hu.1))
    have hh := hb u (hs.trans_lt hu.1)
    rw [he,abs_div,abs_of_pos (sub_pos.mpr h)] at hh
    exact (div_le_iff₀ (sub_pos.mpr h)).mp hh
  rcases lt_trichotomy s t with h | h | h
  · rw [abs_of_pos (sub_pos.mpr h)]
    exact hcase hs h
  · subst t
    simp
  · rw [abs_sub_comm (f t),abs_sub_comm t,abs_of_pos (sub_pos.mpr h)]
    exact hcase ht h

variable {ι S β : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 

theorem BoundaryTree.actual_clock_variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : β → ReplicaTree ι S steps)
    {m Q : ℝ} (ha : OrderedSteps m steps) (hm : 0 < m)
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {front : List (GaussianStep ι)} (T : BoundaryTree ι β front) (hO : PrefixOrdered 0 m front)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : ι → ℝ) :
    ∑ σ, |T.weight (linearClockContinuation L m (gaussianHierarchy w φ steps))
      (fun b => (R b).atomicClock w φ L m) σ t x-
      T.weight (linearClockContinuation L m (gaussianHierarchy w φ steps))
      (fun b => (R b).atomicClock w φ L m) σ s x| ≤
      T.budget (fun b => 4*((R b).leaves:ℝ)*((R b).leaves+1:ℝ)*(∑ i, (D i)^2)+m*Q)*|t-s| := by
  classical
  let F := linearClockContinuation L m (gaussianHierarchy w φ steps)
  let J := featureClockResponse w φ L steps m
  let W := fun b => (R b).atomicClock w φ L m
  let B := fun b => (R b).atomicResponse w φ L m
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  have hcW : ∀ b σ, ∃ K, ParametricContinuous (Ici 0) C K F (W b σ) := by
    intro b σ
    exact parametric_continuous_linear_clock L hC
      ((R b).expect_smooth hw φ ha (fun τ => if τ = σ then 1 else 0) 0) hm
  have hW (r : ℝ) : ∀ b σ, ∃ K, ParametricTest 0 r K (W b σ) (B b σ) := by
    intro b σ
    exact ⟨_,(R b).parametric_clockTest hw φ L ha D
      (by norm_num : (0:ℝ) ≤ 1) hD (fun _ => by split_ifs <;> norm_num) hB r⟩
  have hF (r : ℝ) : ParametricRegular 0 r (Q/2) F J := parametric_featureClock hw φ L hQ steps ha hm r
  apply finite_law_variation_dual
  intro P hP
  have hc : ContinuousOn (fun u => ∑ σ, P σ*T.weight F W σ u x) (Ici 0) :=
    continuousOn_finsetSum Finset.univ fun σ _ =>
      ((T.parametricContinuous hcW hO.positive σ).choose_spec.tested x).const_mul (P σ)
  have hd (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun z => ∑ σ, P σ*T.weight F W σ z x)
        (∑ σ, P σ*T.response F J W B σ u x) u :=
    T.expect_hasDerivAt (hF (u+1)) (hW (u+1)) hO.positive P ⟨hu,by linarith⟩ x
  have hb (u : ℝ) (hu : 0 < u) :
      |∑ σ, P σ*T.response F J W B σ u x| ≤
      T.budget (fun b => 4*((R b).leaves:ℝ)*((R b).leaves+1:ℝ)*(∑ i, (D i)^2)+m*Q) := by
    have hh := T.tested_response_bound (P := P) (by norm_num : (0:ℝ) ≤ 1) hP
      (T.actual_inserted_response_variation hw φ L R ha hm hQ D hD hB hO hu x)
    simpa only [one_mul] using hh
  have hh := abs_sub_le_mul_of_deriv_interior hc hd hb hs ht
  simpa only [mul_sub,Finset.sum_sub_distrib] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

 theorem linearClockContinuation_zero {F : (ι → ℝ) → ℝ}
    (hF : Continuous F) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {m : ℝ} (hm : m ≠ 0) (x : ι → ℝ) :
    linearClockContinuation L m F 0 x = F x := by
  rw [linearClockContinuation_eq L hF,clockContinuation_zero hm]
  simp

 theorem linearClockTest_zero {F A : (ι → ℝ) → ℝ}
    (hF : Continuous F) (hA : Continuous A) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (m : ℝ) (x : ι → ℝ) :
    linearClockTest L m F A 0 x = A x := by
  rw [linearClockTest_eq L hF hA,clockTest_zero]
  simp

 theorem ReplicaTree.atomicClock_zero {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {c : ℝ} (ho : OrderedSteps c steps)
    (m : ℝ) (σ : R.Assignment) (x : ι → ℝ) : R.atomicClock w φ L m σ 0 x = R.weight w φ σ x := by
  classical
  rw [atomicClock,linearClockTest_zero (gaussianHierarchy_regular hw φ steps ho 0).1.choose_spec.continuous
    (R.expect_smooth hw φ ho _ 0).continuous, R.expect_indicator]

 theorem ReplicaTree.atomic_clock_variation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps) {m : ℝ} (ho : OrderedSteps m steps)
    (D : Fin (n+1) → ℝ) (hD : ∀ i, 0 ≤ D i)
    (hB : ∀ i σ, |φ σ (L (Pi.single i 1))| ≤ D i)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : ι → ℝ) :
    ∑ σ, |R.atomicClock w φ L m σ t x-R.atomicClock w φ L m σ s x| ≤
      (4*(R.leaves:ℝ)*(R.leaves+1:ℝ)*∑ i, (D i)^2)*|t-s| := by
  classical
  apply finite_law_variation_dual
  intro P hP
  have hh := R.clock_lipschitz hw φ L ho D (by norm_num : (0:ℝ) ≤ 1) hD hP hB ht hs x
  rw [R.clockTest_atomic hw φ L ho P t x,R.clockTest_atomic hw φ L ho P s x] at hh
  simpa only [atomicClock,mul_sub,Finset.sum_sub_distrib,mul_one] using hh

end SKFluctuations.Hierarchy

end

end OAI
