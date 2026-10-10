import Mathlib
import OAI.Probability.SKFluctuations.CavityGraphParity

namespace OAI

/-! Replica Profile Pair Recursion. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
 theorem profileRow_test_const_mul (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (c : ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profileRow w φ a s (fun σ => c*P σ) K x = c*T.profileRow w φ a s P K x := by
  simp only [profileRow,profileRowList,MarkedPlacement.profileTerm,mul_assoc,
    expect_const_mul,mul_left_comm _ c,List.sum_map_mul_left]

def singleProfileRow (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (a : ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  (single steps).profileRow w φ a (singleSlot steps) (fun _ => 1) K x

omit [Nonempty S] in
 theorem profileRow_fresh_mark_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a c : ℝ)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (MarkedPlacement.fresh T c).tree.profileRow w φ a (MarkedPlacement.fresh T c).mark
      (fun σ => P ((MarkedPlacement.fresh T c).restrict σ)) K x =
      T.expect w φ P x*singleProfileRow w φ steps a K x := by
  change (T.fork (single steps)).profileRow w φ a (.inr (singleSlot steps))
    (fun σ => P σ.1) K x = _
  rw [profileRow_fork_right_zero w φ T (single steps) a _ _ K hK]
  have hc (σ : T.Assignment) : (single steps).profileRow w φ a (singleSlot steps)
      (fun _ => P σ) K x = P σ*singleProfileRow w φ steps a K x := by
    simpa only [mul_one,singleProfileRow] using profileRow_test_const_mul w φ (single steps) a
      (singleSlot steps) (fun _ => 1) (P σ) K x
  simp_rw [hc]
  simp only [expect,Finset.sum_mul,mul_assoc]

 
def profilePairList {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (MarkedPlacement T)) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (a : ℝ) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  (ps.map fun p => p.coeff*p.tree.profileRow w φ a p.mark (fun σ => P (p.restrict σ)) K x).sum

 theorem profilePairList_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps}
    (ps : List (MarkedPlacement T)) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (k : ℕ) :
    BddSmooth k (profilePairList ps w φ a P K) := by
  induction ps with
  | nil => exact BddSmooth.const k 0
  | cons p ps ih =>
    exact ((profileRowList_smooth hw φ (p.tree.markedAttach a) ha p.mark _ K k).const_mul p.coeff).add ih

 theorem profilePairList_map_step_zero {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} {T : ReplicaTree ι S tail}
    (ps : List (MarkedPlacement T)) (m : ℝ) (q : ι → ℝ≥0) {a : ℝ}
    (ha : OrderedSteps a ((m,q)::tail)) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    profilePairList (ps.map (MarkedPlacement.step (m,q))) w φ a P K x = shiftedMean
      (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
      (profilePairList ps w φ m P (fun j => K (j+1))) x := by
  induction ps with
  | nil => simp [profilePairList,shiftedMean,tiltedMean]
  | cons p ps ih =>
    change p.coeff*(p.tree.step (m,q)).profileRow w φ a p.mark (fun σ => P (p.restrict σ)) K x+
      profilePairList (ps.map (MarkedPlacement.step (m,q))) w φ a P K x = _
    rw [profileRow_step_zero hw φ p.tree m q ha _ _ K hK,ih]
    have he : BddSmooth 0 (p.tree.profileRow w φ m p.mark (fun σ => P (p.restrict σ))
        (fun j => K (j+1))) :=
      profileRowList_smooth hw φ (p.tree.markedAttach m) ha.2.2.2 p.mark _ _ 0
    change p.coeff*shiftedMean _ m _ (p.tree.profileRow w φ m p.mark _ (fun j => K (j+1))) x+
      shiftedMean _ m _ (profilePairList ps w φ m P (fun j => K (j+1))) x =
      shiftedMean _ m _ (fun y => p.coeff*p.tree.profileRow w φ m p.mark _ (fun j => K (j+1)) y+
        profilePairList ps w φ m P (fun j => K (j+1)) y) x
    rw [shiftedMean_add (he.const_mul p.coeff)
      (profilePairList_smooth hw φ ps ha.2.2.2 P _ 0)
      (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x),shiftedMean_const_mul]

 theorem profilePair_step_zero {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {tail : List (GaussianStep ι)} (T : ReplicaTree ι S tail)
    (m : ℝ) (q : ι → ℝ≥0) {a : ℝ} (ha : OrderedSteps a ((m,q)::tail))
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (T.step (m,q)).profilePairExpectation w φ a P K x =
      (a-m)*(T.step (m,q)).expect w φ P x*singleProfileRow w φ ((m,q)::tail) a K x+
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
        (fun y => T.profilePairExpectation w φ m P (fun j => K (j+1)) y) x := by
  rw [profilePair_eq_rows]
  change (a-m)*(MarkedPlacement.fresh (T.step (m,q)) (a-m)).tree.profileRow w φ a
    (MarkedPlacement.fresh (T.step (m,q)) (a-m)).mark
    (fun σ => P ((MarkedPlacement.fresh (T.step (m,q)) (a-m)).restrict σ)) K x+
    profilePairList ((T.markedAttach m).map (MarkedPlacement.step (m,q))) w φ a P K x = _
  rw [profileRow_fresh_mark_zero w φ (T.step (m,q)) a (a-m) P K hK,profilePairList_map_step_zero hw φ _ m q ha P K hK]
  simp_rw [profilePair_eq_rows w φ T m P]
  simp only [mul_assoc]
  rfl

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem profilePairList_map_left_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} {T : ReplicaTree ι S steps} (ps : List (MarkedPlacement T))
    (U : ReplicaTree ι S steps) (a : ℝ) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    profilePairList (ps.map (MarkedPlacement.left U)) w φ a P K x =
      U.expect w φ (fun τ => profilePairList ps w φ a (fun σ => P (σ,τ)) K x) x := by
  induction ps with
  | nil => simp [profilePairList,expect]
  | cons p ps ih =>
    change p.coeff*(p.tree.fork U).profileRow w φ a (.inl p.mark)
      (fun σ => P (p.restrict σ.1,σ.2)) K x+
      profilePairList (ps.map (MarkedPlacement.left U)) w φ a P K x = _
    rw [profileRow_fork_left_zero w φ p.tree U a p.mark _ K hK,ih]
    simp only [profilePairList,List.map_cons,List.sum_cons,expect_add,expect_const_mul]

 theorem profilePairList_map_right_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) {U : ReplicaTree ι S steps}
    (ps : List (MarkedPlacement U)) (a : ℝ) (P : (T.fork U).Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    profilePairList (ps.map (MarkedPlacement.right T)) w φ a P K x =
      T.expect w φ (fun σ => profilePairList ps w φ a (fun τ => P (σ,τ)) K x) x := by
  induction ps with
  | nil => simp [profilePairList,expect]
  | cons p ps ih =>
    change p.coeff*(T.fork p.tree).profileRow w φ a (.inr p.mark)
      (fun σ => P (σ.1,p.restrict σ.2)) K x+
      profilePairList (ps.map (MarkedPlacement.right T)) w φ a P K x = _
    rw [profileRow_fork_right_zero w φ T p.tree a p.mark _ K hK,ih]
    simp only [profilePairList,List.map_cons,List.sum_cons,expect_add,expect_const_mul]

 theorem profilePair_fork_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps) (a : ℝ)
    (P : (T.fork U).Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    (T.fork U).profilePairExpectation w φ a P K x =
      -a*(T.fork U).expect w φ P x*singleProfileRow w φ steps a K x+
      (U.expect w φ (fun τ => T.profilePairExpectation w φ a (fun σ => P (σ,τ)) K x) x+
       T.expect w φ (fun σ => U.profilePairExpectation w φ a (fun τ => P (σ,τ)) K x) x) := by
  rw [profilePair_eq_rows]
  change -a*(MarkedPlacement.fresh (T.fork U) (-a)).tree.profileRow w φ a
    (MarkedPlacement.fresh (T.fork U) (-a)).mark
    (fun σ => P ((MarkedPlacement.fresh (T.fork U) (-a)).restrict σ)) K x+
    profilePairList (((T.markedAttach a).map (MarkedPlacement.left U))++
      ((U.markedAttach a).map (MarkedPlacement.right T))) w φ a P K x = _
  rw [profileRow_fresh_mark_zero w φ (T.fork U) a (-a) P K hK]
  have he : profilePairList (((T.markedAttach a).map (MarkedPlacement.left U))++
       ((U.markedAttach a).map (MarkedPlacement.right T))) w φ a P K x =
      profilePairList ((T.markedAttach a).map (MarkedPlacement.left U)) w φ a P K x+
      profilePairList ((U.markedAttach a).map (MarkedPlacement.right T)) w φ a P K x := by
    simp only [profilePairList,List.map_append,List.sum_append]
  rw [he,profilePairList_map_left_zero w φ _ U a P K hK,
    profilePairList_map_right_zero w φ T _ a P K hK]
  simp_rw [profilePair_eq_rows]
  simp only [mul_assoc]
  rfl

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S]

 
def kernelIncrement (K : ℕ → S → S → ℝ) (j : ℕ) (σ τ : S) : ℝ := K (j+1) σ τ-K j σ τ

 
def profilePressure (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    List (GaussianStep ι) → (ℕ → S → S → ℝ) → (ι → ℝ) → ℝ
  | [], _, _ => 0
  | (m,q)::tail, d, x => shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
      (gaussianHierarchy w φ tail) (fun y =>
        singleProfileRow w φ tail m (fun _ => d 0) y+
        profilePressure w φ tail (fun j => d (j+1)) y) x

 theorem profileRow_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    T.profileRow w φ a s P (fun _ _ _ => 0) x = 0 := by
  simp [profileRow,profileRowList,MarkedPlacement.profileTerm,expect]

 theorem profilePair_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P (fun _ _ _ => 0) x = 0 := by
  simp [profilePairExpectation,expect]

 theorem singleProfileRow_leaf_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (a : ℝ) (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    singleProfileRow w φ [] a K x = 0 := by
  simp [singleProfileRow,profileRow,profileRowList,markedAttach,MarkedPlacement.profileTerm,
    MarkedPlacement.coincide,MarkedPlacement.fresh,Placement.coincide,Placement.fresh,splitIndex,single,atSlot,hK,expect]

 theorem singleProfileRow_add (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) (a : ℝ) (K L : ℕ → S → S → ℝ) (x : ι → ℝ) :
    singleProfileRow w φ steps a (fun j σ τ => K j σ τ+L j σ τ) x =
      singleProfileRow w φ steps a K x+singleProfileRow w φ steps a L x :=
  profileRow_add w φ (single steps) a (singleSlot steps) (fun _ => 1) K L x

variable [Nonempty S]

 

theorem singleProfileRow_eq_pressure {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    singleProfileRow w φ steps a K x =
      singleProfileRow w φ steps a (fun _ => K 0) x+
      profilePressure w φ steps (kernelIncrement K) x := by
  induction steps generalizing a K x with
  | nil =>
    have hd : K = fun j σ τ => K 0 σ τ+(K j σ τ-K 0 σ τ) := by funext j σ τ; ring
    have hr : singleProfileRow w φ [] a K x =
        singleProfileRow w φ [] a (fun _ => K 0) x+
        singleProfileRow w φ [] a (fun j σ τ => K j σ τ-K 0 σ τ) x := by
      conv_lhs => rw [hd]
      exact singleProfileRow_add w φ [] a _ _ x
    rw [hr,singleProfileRow_leaf_zero w φ a (fun j σ τ => K j σ τ-K 0 σ τ) (by intros; ring)]
    rfl
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    let L : ℕ → S → S → ℝ := fun j σ τ => K j σ τ-K 0 σ τ
    have hd : K = fun j σ τ => K 0 σ τ+L j σ τ := by funext j σ τ; dsimp [L]; ring
    have hr : singleProfileRow w φ ((m,q)::tail) a K x =
        singleProfileRow w φ ((m,q)::tail) a (fun _ => K 0) x+
        singleProfileRow w φ ((m,q)::tail) a L x := by
      conv_lhs => rw [hd]
      exact singleProfileRow_add w φ _ a _ _ x
    rw [hr]
    congr 1
    change ((single tail).step (m,q)).profileRow w φ a (singleSlot tail) (fun _ => 1) L x = _
    rw [profileRow_step_zero hw φ (single tail) m q ha _ (fun _ => 1) L (by intros; dsimp [L]; ring)]
    change shiftedMean _ m _ (singleProfileRow w φ tail m (fun j => L (j+1))) x = _
    have he : singleProfileRow w φ tail m (fun j => L (j+1)) = fun y =>
        singleProfileRow w φ tail m (fun _ => kernelIncrement K 0) y+
        profilePressure w φ tail (fun j => kernelIncrement K (j+1)) y := by
      funext y
      rw [ih ha.2.2.2]
      have hi : kernelIncrement (fun j => L (j+1)) = fun j => kernelIncrement K (j+1) := by
        funext j σ τ
        dsimp [kernelIncrement,L]
        ring
      rw [hi]
      rfl
    rw [he]
    rfl

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem profilePair_nil_zero (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (T : ReplicaTree ι S []) (a : ℝ) (P : T.Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (hK : ∀ σ τ, K 0 σ τ = 0) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P K x = 0 := by
  have hz (p : MarkedPlacement T) (q : MarkedPlacement p.tree) :
      q.tree.splitIndex (q.embed p.mark) q.mark = 0 := Nat.eq_zero_of_le_zero (q.tree.splitIndex_le _ _)
  simp [profilePairExpectation,hz,hK,expect]

 theorem expect_mul_const (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (P : T.Assignment → ℝ) (c : ℝ) (x : ι → ℝ) :
    T.expect w φ (fun σ => P σ*c) x = T.expect w φ P x*c := by
  simp only [expect,Finset.sum_mul,mul_assoc]

 theorem expect_fork_reverse (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T U : ReplicaTree ι S steps)
    (P : (T.fork U).Assignment → ℝ) (x : ι → ℝ) :
    U.expect w φ (fun τ => T.expect w φ (fun σ => P (σ,τ)) x) x =
      (T.fork U).expect w φ P x := by
  rw [expect_fork]
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

 

def profileCovarianceRate (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    {steps : List (GaussianStep ι)} → (T : ReplicaTree ι S steps) → ℝ →
    (T.Assignment → ℝ) → (ℕ → S → S → ℝ) → (ι → ℝ) → ℝ
  | _, .leaf, _, _, _, _ => 0
  | (m,q)::tail, .step _ T, _, P, d, x =>
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (gaussianHierarchy w φ tail)
      (fun y => T.markedPairExpectation w φ m P (d 0) y+
        m*T.expect w φ P y*profilePressure w φ tail (fun j => d (j+1)) y+
        profileCovarianceRate w φ T m P (fun j => d (j+1)) y) x-
    m*(T.step (m,q)).expect w φ P x*profilePressure w φ ((m,q)::tail) d x
  | _, .fork T U, a, P, d, x =>
    U.expect w φ (fun τ => profileCovarianceRate w φ T a (fun σ => P (σ,τ)) d x) x+
    T.expect w φ (fun σ => profileCovarianceRate w φ U a (fun τ => P (σ,τ)) d x) x

variable [Nonempty S]

 

theorem profilePair_eq_covarianceRate {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P K x =
      T.markedPairExpectation w φ a P (K 0) x+
      a*T.expect w φ P x*profilePressure w φ steps (kernelIncrement K) x+
      profileCovarianceRate w φ T a P (kernelIncrement K) x := by
  induction T generalizing a K x with
  | leaf =>
    let L : ℕ → S → S → ℝ := fun j σ τ => K j σ τ-K 0 σ τ
    have hd : K = fun j σ τ => K 0 σ τ+L j σ τ := by funext j σ τ; dsimp [L]; ring
    have hp : (leaf : ReplicaTree ι S []).profilePairExpectation w φ a P K x =
        (leaf : ReplicaTree ι S []).profilePairExpectation w φ a P (fun _ => K 0) x+
        (leaf : ReplicaTree ι S []).profilePairExpectation w φ a P L x := by
      conv_lhs => rw [hd]
      exact profilePairExpectation_add w φ _ a P _ _ x
    rw [hp,profilePair_nil_zero w φ _ a P L (by intros; dsimp [L]; ring),profilePairExpectation_const]
    simp only [profilePressure,profileCovarianceRate,mul_zero,add_zero]
  | @step st tail T ih =>
    rcases st with ⟨m,q⟩
    let L : ℕ → S → S → ℝ := fun j σ τ => K j σ τ-K 0 σ τ
    have hd : K = fun j σ τ => K 0 σ τ+L j σ τ := by funext j σ τ; dsimp [L]; ring
    have hL : ∀ σ τ, L 0 σ τ = 0 := by intros; dsimp [L]; ring
    have hi : kernelIncrement L = kernelIncrement K := by funext j σ τ; dsimp [kernelIncrement,L]; ring
    have his : kernelIncrement (fun j => L (j+1)) = fun j => kernelIncrement K (j+1) := by
      funext j σ τ; dsimp [kernelIncrement,L]; ring
    have hc : L 1 = kernelIncrement K 0 := rfl
    have hr : singleProfileRow w φ ((m,q)::tail) a L x =
        profilePressure w φ ((m,q)::tail) (kernelIncrement K) x := by
      rw [singleProfileRow_eq_pressure hw φ _ ha L x,hi]
      have hz : (fun _ : ℕ => L 0) = fun _ _ _ => 0 := by funext j σ τ; exact hL σ τ
      rw [hz]
      simp only [singleProfileRow,profileRow_zero,zero_add]
    have hp : (T.step (m,q)).profilePairExpectation w φ a P K x =
        (T.step (m,q)).profilePairExpectation w φ a P (fun _ => K 0) x+
        (T.step (m,q)).profilePairExpectation w φ a P L x := by
      conv_lhs => rw [hd]
      exact profilePairExpectation_add w φ _ a P _ _ x
    rw [hp,profilePairExpectation_const,profilePair_step_zero hw φ T m q ha P L hL,hr]
    have hj (y : ι → ℝ) : T.profilePairExpectation w φ m P (fun j => L (j+1)) y =
        T.markedPairExpectation w φ m P (kernelIncrement K 0) y+
        m*T.expect w φ P y*profilePressure w φ tail (fun j => kernelIncrement K (j+1)) y+
        profileCovarianceRate w φ T m P (fun j => kernelIncrement K (j+1)) y := by
      simpa only [his,hc] using ih ha.2.2.2 P (fun j => L (j+1)) y
    simp_rw [hj]
    simp only [profileCovarianceRate]
    ring
  | @fork tail T U ihT ihU =>
    let L : ℕ → S → S → ℝ := fun j σ τ => K j σ τ-K 0 σ τ
    have hd : K = fun j σ τ => K 0 σ τ+L j σ τ := by funext j σ τ; dsimp [L]; ring
    have hL : ∀ σ τ, L 0 σ τ = 0 := by intros; dsimp [L]; ring
    have hz : L 0 = fun _ _ => 0 := by funext σ τ; exact hL σ τ
    have hi : kernelIncrement L = kernelIncrement K := by funext j σ τ; dsimp [kernelIncrement,L]; ring
    have hr : singleProfileRow w φ tail a L x = profilePressure w φ tail (kernelIncrement K) x := by
      rw [singleProfileRow_eq_pressure hw φ _ ha L x,hi]
      have hz' : (fun _ : ℕ => L 0) = fun _ _ _ => 0 := by funext j σ τ; exact hL σ τ
      rw [hz']
      simp only [singleProfileRow,profileRow_zero,zero_add]
    have hp : (T.fork U).profilePairExpectation w φ a P K x =
        (T.fork U).profilePairExpectation w φ a P (fun _ => K 0) x+
        (T.fork U).profilePairExpectation w φ a P L x := by
      conv_lhs => rw [hd]
      exact profilePairExpectation_add w φ _ a P _ _ x
    rw [hp,profilePairExpectation_const,profilePair_fork_zero w φ T U a P L hL,hr]
    have hzero (V : ReplicaTree ι S tail) (Q : V.Assignment → ℝ) :
        V.markedPairExpectation w φ a Q (L 0) x = 0 := by
      rw [hz,← profilePairExpectation_const]
      exact profilePair_zero w φ V a Q x
    simp_rw [ihT ha _ L x,ihU ha _ L x,hzero,zero_add,hi,expect_add,
      expect_mul_const,expect_const_mul]
    rw [expect_fork_reverse,← expect_fork]
    simp only [profileCovarianceRate]
    ring

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S]
attribute [local instance] Classical.propDecidable

 theorem profileRow_finsetSum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (s : T.Slot) (P : T.Assignment → ℝ) {κ : Type*} (is : Finset κ)
    (K : κ → ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profileRow w φ a s P (fun j σ τ => ∑ i ∈ is, K i j σ τ) x =
      ∑ i ∈ is, T.profileRow w φ a s P (K i) x := by
  simp only [profileRow,profileRowList,MarkedPlacement.profileTerm,Finset.mul_sum,expect_finsetSum]
  exact list_sum_finset_sum _ _ _

 theorem profilePairExpectation_finsetSum (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) {κ : Type*} (is : Finset κ) (K : κ → ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P (fun j σ τ => ∑ i ∈ is, K i j σ τ) x =
      ∑ i ∈ is, T.profilePairExpectation w φ a P (K i) x := by
  simp only [profilePairExpectation,Finset.mul_sum,expect_finsetSum]
  simp_rw [list_sum_finset_sum,Finset.mul_sum,list_sum_finset_sum]

 

def coordinateProfile (φ : S → (ι → ℝ) →L[ℝ] ℝ) (k : ℕ → ι → ℝ)
    (j : ℕ) (σ τ : S) : ℝ := ∑ i, k j i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1)

omit [Fintype S] in
 theorem coordinateProfile_add (φ : S → (ι → ℝ) →L[ℝ] ℝ) (k l : ℕ → ι → ℝ) :
    coordinateProfile φ (fun j i => k j i+l j i) =
      fun j σ τ => coordinateProfile φ k j σ τ+coordinateProfile φ l j σ τ := by
  funext j σ τ
  simp only [coordinateProfile,add_mul,Finset.sum_add_distrib]

omit [Fintype S] in
 theorem coordinateProfile_sub (φ : S → (ι → ℝ) →L[ℝ] ℝ) (k l : ℕ → ι → ℝ) :
    coordinateProfile φ (fun j i => k j i-l j i) =
      fun j σ τ => coordinateProfile φ k j σ τ-coordinateProfile φ l j σ τ := by
  funext j σ τ
  simp only [coordinateProfile,sub_mul,Finset.sum_sub_distrib]

 theorem profilePair_coordinate_const (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps) (a : ℝ)
    (P : T.Assignment → ℝ) (k : ι → ℝ) (x : ι → ℝ) :
    T.profilePairExpectation w φ a P (coordinateProfile φ (fun _ => k)) x =
      ∑ i, k i*powerJet w φ a [Pi.single i 1,Pi.single i 1] T P x := by
  unfold coordinateProfile
  simp only [mul_assoc]
  rw [profilePairExpectation_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [profilePairExpectation_smul,profilePairExpectation_const,← powerJet_two_marked]

variable [Nonempty S]

 theorem single_source_one_response {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (u v x : ι → ℝ) :
    sourceJet w φ a [u] (single steps) (fun σ => φ (singleEquiv (S := S) steps σ) v) x =
      gaussianHierarchyResponse w φ (fun σ => φ σ v) u steps x := by
  have h₁ := sourceJet_hasDerivAt hw φ [] (single steps) ha
    (fun σ => φ (singleEquiv (S := S) steps σ) v) u x 0
  have h₂ := gaussianHierarchyMean_hasDerivAt hw φ (fun σ => φ σ v) steps ha x u 0
  change HasDerivAt (fun s => (single steps).expect w φ
    (fun σ => φ (singleEquiv (S := S) steps σ) v) (x+s • u)) _ 0 at h₁
  simp_rw [single_expect hw φ steps ha (fun σ => φ σ v)] at h₁
  simpa only [List.nil_append,zero_smul,add_zero] using h₁.unique h₂

 

theorem singleProfileRow_coordinate_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a steps) (k : ι → ℝ) (x : ι → ℝ) :
    singleProfileRow w φ steps a (coordinateProfile φ (fun _ => k)) x =
      ∑ i, k i*(gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1))
        (Pi.single i 1) steps x+a*(gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) steps x)^2) := by
  unfold singleProfileRow
  unfold coordinateProfile
  simp only [mul_assoc]
  rw [profileRow_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [profileRow_smul,profileRow_const_separable]
  simp only [one_mul,atSlot_single]
  rw [← powerJet_single,powerJet_one_eq hw φ _ ha,single_source_one_response hw φ steps ha,
    single_expect hw φ steps ha (fun σ => φ σ (Pi.single i 1))]
  ring

end SKFluctuations.Hierarchy.ReplicaTree

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

theorem single_fin_classical (i : Fin (n+1)) :
    @Pi.single (Fin (n+1)) (fun _ => ℝ) _
      (fun u v => Classical.propDecidable (u=v)) i 1 =
    @Pi.single (Fin (n+1)) (fun _ => ℝ) _ (instDecidableEqFin (n+1)) i 1 := by
  funext j
  by_cases h : j=i <;> simp [h]

 theorem ClockExpr.eval_grad_source {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ) (i : Fin (n+1)) :
    ((ClockExpr.grad φ i as).source φ (Pi.single i 1)).eval w φ q =
      gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1)
        (clockSteps as (fun j i => Real.toNNReal (q j i))) := by
  funext x
  have h₁ := (ClockExpr.grad φ i as).hasDerivAt_source hw φ ho q (Pi.single i 1) x 0
  have h₂ := gaussianHierarchyMean_hasDerivAt hw φ (fun σ => φ σ (Pi.single i 1))
    (clockSteps as (fun j i => Real.toNNReal (q j i)))
    (clockSteps_ordered ho _) x (Pi.single i 1) 0
  simp_rw [ClockExpr.grad,ClockExpr.eval_mean] at h₁
  simpa only [zero_smul,add_zero,ClockExpr.grad] using h₁.unique h₂

 theorem ClockExpr.eval_step_coordSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (a : PositiveMass) (ho : MassOrdered a.val as) (E : Fin (n+1) → ClockExpr S as)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((ClockExpr.coordSum E).step a).eval w φ q x = ∑ i, ((E i).step a).eval w φ q x := by
  change varianceTest _ _ _ _ _ = _
  have he : (ClockExpr.coordSum E).eval w φ (fun j => q (j+1)) =
      fun y => ∑ i, (E i).eval w φ (fun j => q (j+1)) y := by
    funext y
    exact ClockExpr.eval_coordSum hw φ ho E _ y
  rw [he]
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ
    (clockSteps as (fun j i => Real.toNNReal (q (j+1) i))) (clockSteps_ordered ho _) 0).1
  exact varianceTest_sum hC (fun i => (E i).eval_smooth hw φ ho _ 0) a.val (q 0) x

 

theorem profilePressure_eq_eval {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    {a : ℝ} (ho : MassOrdered a as) (q d : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ReplicaTree.profilePressure w φ (clockSteps as (fun j i => Real.toNNReal (q j i)))
      (ReplicaTree.coordinateProfile φ d) x = 2*(ClockExpr.pressureCov φ as d).eval w φ q x := by
  induction as generalizing a q d x with
  | nil => simp [ReplicaTree.profilePressure,clockSteps,ClockExpr.pressureCov,ClockExpr.eval,gaussianHierarchyMean]
  | cons b bs ih =>
    let G : Fin (n+1) → ClockExpr S bs := fun i => ClockExpr.grad φ i bs
    let H : Fin (n+1) → ClockExpr S bs := fun i => (G i).source φ (Pi.single i 1)
    let R : ClockExpr S bs := ClockExpr.coordSum fun i =>
      ((H i).add (((G i).mul (G i)).scale b.val)).scale (d 0 i)
    let D : ClockExpr S bs := ClockExpr.pressureCov φ bs (fun j => d (j+1))
    have he (y : Fin (n+1) → ℝ) :
        ReplicaTree.singleProfileRow w φ (clockSteps bs (fun j i => Real.toNNReal (q (j+1) i))) b.val
          (fun _ => ReplicaTree.coordinateProfile φ d 0) y+
        ReplicaTree.profilePressure w φ (clockSteps bs (fun j i => Real.toNNReal (q (j+1) i)))
          (fun j => ReplicaTree.coordinateProfile φ d (j+1)) y =
        (R.add (D.scale 2)).eval w φ (fun j => q (j+1)) y := by
      rw [show (fun _ => ReplicaTree.coordinateProfile φ d 0) =
        ReplicaTree.coordinateProfile φ (fun _ => d 0) from rfl,
        ReplicaTree.singleProfileRow_coordinate_const hw φ _ (clockSteps_ordered ho.2.2 _)]
      change _+ReplicaTree.profilePressure w φ _ (ReplicaTree.coordinateProfile φ (fun j => d (j+1))) y = _
      rw [ih ho.2.2]
      simp only [R,D,H,G,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho.2.2]
      simp only [ClockExpr.eval_grad_source hw φ ho.2.2]
      simp only [ClockExpr.grad,ClockExpr.eval_mean,pow_two]
      simp_rw [single_fin_classical]
    change shiftedMean _ b.val _ _ x = _
    simp_rw [he]
    change ((R.add (D.scale 2)).step b).eval w φ q x = _
    rw [ClockExpr.eval_step_add hw φ b ho.2.2,ClockExpr.eval_step_scale]
    rw [show R = ClockExpr.coordSum (fun i =>
      ((H i).add (((G i).mul (G i)).scale b.val)).scale (d 0 i)) from rfl,
      ClockExpr.eval_step_coordSum hw φ b ho.2.2]
    simp_rw [ClockExpr.eval_step_scale,ClockExpr.eval_step_add hw φ b ho.2.2,ClockExpr.eval_step_scale]
    simp only [G,H,D,ClockExpr.pressureCov,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho,Finset.mul_sum,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem ClockExpr.eval_source_of_expect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ)
    (T : ReplicaTree (Fin (n+1)) S (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (P : T.Assignment → ℝ) (he : E.eval w φ q = T.expect w φ P) (v : Fin (n+1) → ℝ) :
    (E.source φ v).eval w φ q = ReplicaTree.sourceJet w φ a [v] T P := by
  funext x
  have h₁ := E.hasDerivAt_source hw φ ho q v x 0
  have h₂ := ReplicaTree.sourceJet_hasDerivAt hw φ [] T (clockSteps_ordered ho _) P v x 0
  change HasDerivAt (fun s => T.expect w φ P (x+s • v)) _ 0 at h₂
  rw [he] at h₁
  simpa only [zero_smul,add_zero,List.nil_append] using h₁.unique h₂

 theorem ClockExpr.eval_source_two_of_expect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ)
    (T : ReplicaTree (Fin (n+1)) S (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (P : T.Assignment → ℝ) (he : E.eval w φ q = T.expect w φ P) (v : Fin (n+1) → ℝ) :
    ((E.source φ v).source φ v).eval w φ q = ReplicaTree.sourceJet w φ a [v,v] T P := by
  funext x
  have h₁ := (E.source φ v).hasDerivAt_source hw φ ho q v x 0
  have h₂ := ReplicaTree.sourceJet_hasDerivAt hw φ [v] T (clockSteps_ordered ho _) P v x 0
  rw [E.eval_source_of_expect hw φ ho q T P he v] at h₁
  simpa only [zero_smul,add_zero,List.cons_append,List.nil_append] using h₁.unique h₂

 

theorem profilePair_const_eq_testedInsert {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → Fin (n+1) → ℝ)
    (T : ReplicaTree (Fin (n+1)) S (clockSteps as (fun j i => Real.toNNReal (q j i))))
    (P : T.Assignment → ℝ) (he : E.eval w φ q = T.expect w φ P)
    (d : Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.markedPairExpectation w φ a P (ReplicaTree.coordinateProfile φ (fun _ => d) 0) x =
      ∑ i, d i*(E.testedInsert φ a i).eval w φ q x := by
  rw [← ReplicaTree.profilePairExpectation_const]
  change T.profilePairExpectation w φ a P (ReplicaTree.coordinateProfile φ (fun _ => d)) x = _
  rw [ReplicaTree.profilePair_coordinate_const]
  apply Finset.sum_congr rfl
  intro i _
  rw [ReplicaTree.powerJet_two_eq hw φ T (clockSteps_ordered ho _)]
  simp only [ClockExpr.testedInsert,ClockExpr.potentialInsert,ClockExpr.eval]
  rw [E.eval_source_of_expect hw φ ho q T P he,E.eval_source_two_of_expect hw φ ho q T P he,
    ClockExpr.eval_grad_source hw φ ho]
  simp only [ClockExpr.grad,ClockExpr.eval_mean,he,pow_two]
  simp_rw [single_fin_classical]
  ring

end SKFluctuations.Hierarchy

end

end OAI
