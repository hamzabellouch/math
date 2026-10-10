import Mathlib
import OAI.Probability.SKFluctuations.ReplicaProfileStepIdentification

namespace OAI

/-! Replica Profile Differentiation. -/

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
attribute [local instance] Classical.propDecidable

 

theorem ClockTree.profileCovarianceRate_expand {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (P : T.Assignment → ℝ)
    (q d : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ReplicaTree.profileCovarianceRate w φ (T.realize (fun j i => Real.toNNReal (q j i))) a
      (fun τ => P ((T.assignmentEquiv (fun j i => Real.toNNReal (q j i))).symm τ))
      (ReplicaTree.coordinateProfile φ d) x =
      ∑ σ, P σ*(2*((T.weightExpr σ).covariance φ d).eval w φ q x) := by
  let e := T.assignmentEquiv (ι := Fin (n+1)) (fun j i => Real.toNNReal (q j i))
  have hP : (fun τ => P (e.symm τ)) = (fun τ => ∑ σ, P σ*(if τ=e σ then 1 else 0)) := by
    funext τ
    classical
    have hi (σ : T.Assignment) : τ=e σ ↔ σ=e.symm τ := by
      constructor
      · intro h; exact (e.symm_apply_eq.mpr h).symm
      · intro h; simp [h]
    simp_rw [hi]
    simp
  rw [hP,ReplicaTree.profileCovarianceRate_test_finsetSum hw φ _ (clockSteps_ordered ho _)]
  apply Finset.sum_congr rfl
  intro σ _
  rw [ReplicaTree.profileCovarianceRate_test_smul hw φ _ (clockSteps_ordered ho _)]
  rw [T.profileCovarianceRate_weight hw φ ho σ q d x]

 

theorem ClockTree.hasDerivAt_profileCovarianceRate {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (P : T.Assignment → ℝ)
    (q d : ℕ → Fin (n+1) → ℝ) {l r t : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*d j i) (ht : t ∈ Ioo l r)
    (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.expect w φ (fun j i => Real.toNNReal (q j i+s*d j i)) P x)
      (ReplicaTree.profileCovarianceRate w φ
        (T.realize (fun j i => Real.toNNReal (q j i+t*d j i))) a
        (fun τ => P ((T.assignmentEquiv (fun j i => Real.toNNReal (q j i+t*d j i))).symm τ))
        (ReplicaTree.coordinateProfile φ d) x/2) t := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun σ _ =>
    ((T.weightExpr σ).hasDerivAt_covariance hw φ ho q d hp ht x).mul_const (P σ))
  simp_rw [ClockTree.eval_weightExpr] at hd
  rw [T.profileCovarianceRate_expand hw φ ho]
  have he : (∑ σ, fun s : ℝ => T.weight w φ
      (fun j i => Real.toNNReal (q j i+s*d j i)) σ x*P σ) =
      (fun s => T.expect w φ (fun j i => Real.toNNReal (q j i+s*d j i)) P x) := by
    funext s
    simp only [Finset.sum_apply,ClockTree.expect]
  rw [he] at hd
  have hv : (∑ σ, P σ*(2*((T.weightExpr σ).covariance φ d).eval w φ
      (fun j i => q j i+t*d j i) x))/2 =
      ∑ σ, ((T.weightExpr σ).covariance φ d).eval w φ (fun j i => q j i+t*d j i) x*P σ := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  rw [hv]
  exact hd

 

theorem ClockTree.hasDerivAt_profilePair {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (P : T.Assignment → ℝ)
    (q K : ℕ → Fin (n+1) → ℝ) (hK : K 0=0) {l r t : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*(K (j+1) i-K j i))
    (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.expect w φ
      (fun j i => Real.toNNReal (q j i+s*(K (j+1) i-K j i))) P x)
      ((T.realize (fun j i => Real.toNNReal (q j i+t*(K (j+1) i-K j i)))).profilePairExpectation w φ 0
        (fun τ => P ((T.assignmentEquiv
          (fun j i => Real.toNNReal (q j i+t*(K (j+1) i-K j i)))).symm τ))
        (ReplicaTree.coordinateProfile φ K) x/2) t := by
  have hi : ReplicaTree.kernelIncrement (ReplicaTree.coordinateProfile φ K) =
      ReplicaTree.coordinateProfile φ (fun j i => K (j+1) i-K j i) := by
    funext j σ τ
    simp [ReplicaTree.kernelIncrement,ReplicaTree.coordinateProfile,sub_mul,Finset.sum_sub_distrib]
  have hz : ReplicaTree.coordinateProfile φ K 0 = fun _ _ => 0 := by
    funext σ τ
    simp only [ReplicaTree.coordinateProfile,hK,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
  rw [ReplicaTree.profilePair_eq_covarianceRate hw φ _ (clockSteps_ordered ho _),hi,hz,
    ← ReplicaTree.profilePairExpectation_const,ReplicaTree.profilePair_zero]
  simp only [zero_mul,zero_add]
  exact T.hasDerivAt_profileCovarianceRate hw φ ho P q _ hp ht x

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy.ClockTree
open scoped NNReal BigOperators
variable {S ι : Type*}

namespace MarkedPlacement

theorem realize_restrict {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (q : ℕ → ι → ℝ≥0) (σ : p.tree.Assignment) :
    (p.realize q).restrict (p.tree.assignmentEquiv q σ) = T.assignmentEquiv q (p.restrict σ) := by
  change T.assignmentEquiv q (p.restrict ((p.tree.assignmentEquiv q).symm
    (p.tree.assignmentEquiv q σ))) = _
  rw [Equiv.symm_apply_apply]

theorem realize_spin {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (q : ℕ → ι → ℝ≥0) (σ : p.tree.Assignment) :
    (p.realize q).spin (p.tree.assignmentEquiv q σ) = p.spin σ := by
  change p.spin ((p.tree.assignmentEquiv q).symm (p.tree.assignmentEquiv q σ)) = _
  rw [Equiv.symm_apply_apply]

theorem realize_embed {as : List PositiveMass} {T : ClockTree S as}
    (p : MarkedPlacement T) (q : ℕ → ι → ℝ≥0) (s : T.Slot) :
    (p.realize q).embed (T.slotEquiv q s) = p.tree.slotEquiv q (p.embed s) := by
  change p.tree.slotEquiv q (p.embed ((T.slotEquiv q).symm (T.slotEquiv q s))) = _
  rw [Equiv.symm_apply_apply]

end MarkedPlacement

def profilePairTest {as : List PositiveMass} {T : ClockTree S as}
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (σ : r.tree.Assignment) : ℝ :=
  P (p.restrict (r.restrict σ))*K (r.tree.splitIndex (r.embed p.mark) r.mark)
    (p.spin (r.restrict σ)) (r.spin σ)

variable [Fintype S] [Fintype ι]

def profilePair (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (a : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) : ℝ :=
  ((T.markedAttach a).map fun p => p.coeff*
    ((p.tree.markedAttach a).map fun r => r.coeff*
      r.tree.expect w φ q (profilePairTest P K p r) x).sum).sum

theorem profilePair_realize (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (a : ℝ)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) (x : ι → ℝ) :
    T.profilePair w φ a q P K x = (T.realize q).profilePairExpectation w φ a
      (fun σ => P ((T.assignmentEquiv q).symm σ)) K x := by
  unfold profilePair ReplicaTree.profilePairExpectation
  rw [← T.markedAttach_realize a q,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  change p.coeff*_ = p.coeff*_
  congr 1
  dsimp only [MarkedPlacement.realize]
  change _ = (List.map _ ((p.tree.realize q).markedAttach a)).sum
  rw [← p.tree.markedAttach_realize a q,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  dsimp only [MarkedPlacement.realize]
  change r.coeff*_ = r.coeff*_
  congr 1
  rw [r.tree.expect_realize]
  congr 1
  funext σ
  obtain ⟨τ,rfl⟩ := (r.tree.assignmentEquiv q).surjective σ
  simp only [Equiv.symm_apply_apply,profilePairTest,realize_splitIndex]

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
attribute [local instance] Classical.propDecidable

 

def ClockExpr.homSum {as : List PositiveMass} (Es : List (ClockExpr S as)) : ClockExpr S as :=
  Es.foldr ClockExpr.add ((ClockExpr.mean (fun _ => 0) as).scale 0)

omit [Nonempty S] in
theorem ClockExpr.eval_homSum (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (Es : List (ClockExpr S as))
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (ClockExpr.homSum Es).eval w φ q x = (Es.map (fun E => E.eval w φ q x)).sum := by
  induction Es with
  | nil => simp [ClockExpr.homSum,ClockExpr.eval]
  | cons E Es ih => exact congrArg (E.eval w φ q x+·) ih

omit [Nonempty S] in
theorem ClockExpr.covariance_eval_homSum (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (Es : List (ClockExpr S as)) (d q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((ClockExpr.homSum Es).covariance φ d).eval w φ q x =
      (Es.map (fun E => (E.covariance φ d).eval w φ q x)).sum := by
  induction Es with
  | nil => simp [ClockExpr.homSum,ClockExpr.covariance,ClockExpr.eval]
  | cons E Es ih => exact congrArg ((E.covariance φ d).eval w φ q x+·) ih

 
def ClockTree.homTest {as : List PositiveMass} (T : ClockTree S as)
    (P : T.Assignment → ℝ) : ClockExpr S as :=
  ClockExpr.homSum ((Finset.univ : Finset T.Assignment).toList.map fun σ =>
    (T.weightExpr σ).scale (P σ))

omit [Nonempty S] in
theorem ClockTree.eval_homTest (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (P : T.Assignment → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (T.homTest P).eval w φ q x = T.expect w φ (fun j i => Real.toNNReal (q j i)) P x := by
  rw [ClockTree.homTest,ClockExpr.eval_homSum]
  simp only [List.map_map,Function.comp_def,ClockExpr.eval,ClockTree.eval_weightExpr,
    Finset.sum_map_toList,ClockTree.expect]
  apply Finset.sum_congr rfl
  intro σ _
  exact mul_comm _ _

omit [Nonempty S] in
theorem ClockTree.covariance_eval_homTest (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (P : T.Assignment → ℝ)
    (d q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((T.homTest P).covariance φ d).eval w φ q x =
      ∑ σ, P σ*((T.weightExpr σ).covariance φ d).eval w φ q x := by
  rw [ClockTree.homTest,ClockExpr.covariance_eval_homSum]
  simp only [List.map_map,Function.comp_def,ClockExpr.covariance,ClockExpr.eval,Finset.sum_map_toList]

 

theorem ClockTree.rootCov_eq_profilePair {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (P : T.Assignment → ℝ)
    (q K : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ((T.homTest P).rootCov φ (K 0) (fun j i => K (j+1) i-K j i)).eval w φ q x =
      T.profilePair w φ 0 (fun j i => Real.toNNReal (q j i)) P
        (ReplicaTree.coordinateProfile φ K) x/2 := by
  let Q := fun j i => Real.toNNReal (q j i)
  let V := T.realize Q
  let P' := fun τ => P ((T.assignmentEquiv Q).symm τ)
  have he : (T.homTest P).eval w φ q = V.expect w φ P' := by
    funext y
    rw [T.eval_homTest w φ]
    exact T.expect_realize w φ Q P y
  have hi : ReplicaTree.kernelIncrement (ReplicaTree.coordinateProfile φ K) =
      ReplicaTree.coordinateProfile φ (fun j i => K (j+1) i-K j i) := by
    funext j σ τ
    simp [ReplicaTree.kernelIncrement,ReplicaTree.coordinateProfile,sub_mul,Finset.sum_sub_distrib]
  rw [ClockTree.profilePair_realize,ReplicaTree.profilePair_eq_covarianceRate hw φ _
    (clockSteps_ordered ho _),hi]
  simp only [zero_mul]
  have hc := profilePair_const_eq_testedInsert hw φ (T.homTest P) ho q V P' he (K 0) x
  have hk : ReplicaTree.coordinateProfile φ (fun _ => K 0) 0 =
      ReplicaTree.coordinateProfile φ K 0 := rfl
  rw [hk] at hc
  rw [hc,T.profileCovarianceRate_expand hw φ ho]
  simp only [ClockExpr.rootCov,ClockExpr.eval,ClockExpr.eval_coordSum hw φ ho,
    ClockExpr.testedInsert,ClockExpr.potentialInsert,zero_mul,mul_zero,add_zero,
    zero_pow (by decide : 2 ≠ 0),ClockTree.covariance_eval_homTest]
  rw [add_div,Finset.sum_div,Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro σ _
    ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem ClockExpr.rootEval_homSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    {a : ℝ} (ho : MassOrdered a as) (Es : List (ClockExpr S as))
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (ClockExpr.homSum Es).rootEval w φ q₀ q x = (Es.map (fun E => E.rootEval w φ q₀ q x)).sum := by
  induction Es with
  | nil => simp [ClockExpr.homSum,ClockExpr.rootEval_scale]
  | cons E Es ih =>
    change (E.add (ClockExpr.homSum Es)).rootEval w φ q₀ q x = _
    rw [ClockExpr.rootEval_add hw φ _ _ ho,ih]
    rfl

 

def ClockTree.rootExpect (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (P : T.Assignment → ℝ)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  (T.homTest P).rootEval w φ q₀ q x

omit [Nonempty S] in
theorem ClockTree.rootExpect_eq_integral (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (P : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ P q₀ q x =
      ∫ y, T.expect w φ (fun j i => Real.toNNReal (q j i)) P (x+y)
        ∂(Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q₀ i))) := by
  unfold ClockTree.rootExpect ClockExpr.rootEval
  simp only [varianceTest_zero_root,zeroContinuation]
  congr 1
  funext y
  exact T.eval_homTest w φ P q (x+y)

 
def ClockTree.profileExpr {as : List PositiveMass} (T : ClockTree S as)
    (P : T.Assignment → ℝ) (K : ℕ → S → S → ℝ) : ClockExpr S as :=
  (ClockExpr.homSum ((T.markedAttach 0).map fun p =>
    (ClockExpr.homSum ((p.tree.markedAttach 0).map fun r =>
      (r.tree.homTest (ClockTree.profilePairTest P K p r)).scale r.coeff)).scale p.coeff)).scale (1/2)

omit [Nonempty S] in
theorem ClockTree.eval_profileExpr (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (P : T.Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (T.profileExpr P K).eval w φ q x =
      T.profilePair w φ 0 (fun j i => Real.toNNReal (q j i)) P K x/2 := by
  simp only [ClockTree.profileExpr,ClockExpr.eval,ClockExpr.eval_homSum,
    List.map_map,Function.comp_def,ClockTree.eval_homTest,ClockTree.profilePair]
  ring

 
def ClockTree.rootProfilePair (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (P : T.Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p => p.coeff*
    ((p.tree.markedAttach 0).map fun r => r.coeff*
      r.tree.rootExpect w φ (ClockTree.profilePairTest P K p r) q₀ q x).sum).sum

theorem ClockTree.rootEval_profileExpr {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (P : T.Assignment → ℝ)
    (K : ℕ → S → S → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (T.profileExpr P K).rootEval w φ q₀ q x = T.rootProfilePair w φ P K q₀ q x/2 := by
  simp only [ClockTree.profileExpr,ClockExpr.rootEval_scale,ClockExpr.rootEval_homSum hw φ ho,
    List.map_map,Function.comp_def,ClockTree.rootProfilePair,ClockTree.rootExpect]
  ring

 

theorem ClockTree.hasDerivAt_rootProfilePair {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) (P : T.Assignment → ℝ)
    (q₀ : Fin (n+1) → ℝ) (q K : ℕ → Fin (n+1) → ℝ) {l r t : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*(K (j+1) i-K j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*K 0 i) (ht : t ∈ Ioo l r)
    (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.rootExpect w φ P (fun i => q₀ i+s*K 0 i)
      (fun j i => q j i+s*(K (j+1) i-K j i)) x)
      (T.rootProfilePair w φ P (ReplicaTree.coordinateProfile φ K) (fun i => q₀ i+t*K 0 i)
        (fun j i => q j i+t*(K (j+1) i-K j i)) x/2) t := by
  have h := (T.homTest P).hasDerivAt_rootCov hw φ ho q₀ (K 0) q _ hp hr ht x
  have he : ((T.homTest P).rootCov φ (K 0) (fun j i => K (j+1) i-K j i)).eval w φ
      (fun j i => q j i+t*(K (j+1) i-K j i)) =
      (T.profileExpr P (ReplicaTree.coordinateProfile φ K)).eval w φ
      (fun j i => q j i+t*(K (j+1) i-K j i)) := by
    funext y
    rw [T.rootCov_eq_profilePair hw φ ho,T.eval_profileExpr]
  change HasDerivAt _ (varianceTest 0 (fun _ => 0) _ _ x) t at h
  rw [he] at h
  change HasDerivAt _ ((T.profileExpr P (ReplicaTree.coordinateProfile φ K)).rootEval w φ _ _ x) t at h
  rw [T.rootEval_profileExpr hw φ ho] at h
  exact h

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

def ClockTree.rootProfileJets (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) : List (ℕ → S → S → ℝ) →
      (T : ClockTree S as) → (T.Assignment → ℝ) → ℝ
  | [], T, P => T.rootExpect w φ P q₀ q x
  | K::Ks, T, P =>
    ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun r => r.coeff*
        rootProfileJets w φ q₀ q x Ks r.tree (ClockTree.profilePairTest P K p r)).sum).sum/2

omit [Fintype S] [Nonempty S] in
theorem hasDerivAt_listSum {α : Type*} (L : List α) (f : α → ℝ → ℝ) (g : α → ℝ)
    {t : ℝ} (h : ∀ a ∈ L, HasDerivAt (f a) (g a) t) :
    HasDerivAt (fun s => (L.map fun a => f a s).sum) (L.map g).sum t := by
  induction L with
  | nil => exact hasDerivAt_const t 0
  | cons a L ih =>
    exact (h a List.mem_cons_self).add
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

 

theorem ClockTree.hasDerivAt_rootProfileJets {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    (P : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ) (q K : ℕ → Fin (n+1) → ℝ)
    {l r t : ℝ} (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*(K (j+1) i-K j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*K 0 i) (ht : t ∈ Ioo l r)
    (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => ClockTree.rootProfileJets w φ (fun i => q₀ i+s*K 0 i)
      (fun j i => q j i+s*(K (j+1) i-K j i)) x Ks T P)
      (ClockTree.rootProfileJets w φ (fun i => q₀ i+t*K 0 i)
        (fun j i => q j i+t*(K (j+1) i-K j i)) x
        (Ks++[ReplicaTree.coordinateProfile φ K]) T P) t := by
  induction Ks generalizing T with
  | nil => exact T.hasDerivAt_rootProfilePair hw φ ho P q₀ q K hp hr ht x
  | cons L Ks ih =>
    exact (hasDerivAt_listSum (T.markedAttach 0) _ _ (fun p _ =>
      (hasDerivAt_listSum (p.tree.markedAttach 0) _ _ (fun r _ =>
        (ih r.tree (ClockTree.profilePairTest P L p r)).const_mul r.coeff)).const_mul p.coeff)).div_const 2

 

theorem ClockTree.iteratedDeriv_rootProfileJets {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (T : ClockTree S as) (P : T.Assignment → ℝ)
    (q₀ : Fin (n+1) → ℝ) (q K : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*(K (j+1) i-K j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*K 0 i) (x : Fin (n+1) → ℝ)
    (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    iteratedDeriv k (fun s => T.rootExpect w φ P (fun i => q₀ i+s*K 0 i)
      (fun j i => q j i+s*(K (j+1) i-K j i)) x) t =
      ClockTree.rootProfileJets w φ (fun i => q₀ i+t*K 0 i)
        (fun j i => q j i+t*(K (j+1) i-K j i)) x
        (List.replicate k (ReplicaTree.coordinateProfile φ K)) T P := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s => T.rootExpect w φ P (fun i => q₀ i+s*K 0 i)
        (fun j i => q j i+s*(K (j+1) i-K j i)) x) =ᶠ[𝓝 t]
        (fun s => ClockTree.rootProfileJets w φ (fun i => q₀ i+s*K 0 i)
          (fun j i => q j i+s*(K (j+1) i-K j i)) x
          (List.replicate k (ReplicaTree.coordinateProfile φ K)) T P) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact ih hs
    rw [he.deriv_eq]
    simpa only [List.replicate_succ'] using
      (ClockTree.hasDerivAt_rootProfileJets hw φ ho
        (List.replicate k (ReplicaTree.coordinateProfile φ K)) T P q₀ q K hp hr ht x).deriv

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators
variable {S : Type*}

theorem markedAttach_variation {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) :
    ((T.markedAttach a).map fun p => |p.coeff|).sum = 2*(T.leaves:ℝ)-a := by
  let q : ℕ → Unit → ℝ≥0 := fun _ _ => 0
  have h := (T.realize q).markedAttach_variation (clockSteps_ordered ha q)
  rw [← T.markedAttach_realize a q,List.map_map] at h
  simpa only [Function.comp_def,MarkedPlacement.realize,realize_leaves] using h

theorem markedAttach_leaves {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a) :
    p.tree.leaves ≤ T.leaves+1 := by
  let q : ℕ → Unit → ℝ≥0 := fun _ _ => 0
  have hmem : p.realize q ∈ (T.realize q).markedAttach a := by
    rw [← T.markedAttach_realize a q]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have h := (T.realize q).markedAttach_leaves a (p.realize q) hmem
  change (p.tree.realize q).leaves ≤ (T.realize q).leaves+1 at h
  simpa only [realize_leaves] using h

theorem marked_list_weight_abs_le {as : List PositiveMass} {T : ClockTree S as}
    (ps : List (MarkedPlacement T)) (F : MarkedPlacement T → ℝ) {C : ℝ}
    (hF : ∀ p ∈ ps, |F p| ≤ C) :
    |(ps.map fun p => p.coeff*F p).sum| ≤ (ps.map fun p => |p.coeff|).sum*C := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,add_mul]
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF p List.mem_cons_self) (abs_nonneg _))
      (ih (fun q hq => hF q (List.mem_cons_of_mem _ hq))))

variable [Fintype S] [Nonempty S] {n : ℕ}

theorem rootExpect_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) (ho : MassOrdered 0 as) {P : T.Assignment → ℝ} {C : ℝ}
    (hP : ∀ σ, |P σ| ≤ C) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) : |T.rootExpect w φ P q₀ q x| ≤ C := by
  rw [T.rootExpect_eq_integral]
  have hB (y : Fin (n+1) → ℝ) :
      |T.expect w φ (fun j i => Real.toNNReal (q j i)) P (x+y)| ≤ C := by
    rw [T.expect_realize]
    exact (T.realize _).expect_abs_le hw φ (clockSteps_ordered ho _) (fun σ => hP _) _
  have h := norm_integral_le_of_norm_le_const (f := fun y => T.expect w φ (fun j i => Real.toNNReal (q j i)) P (x+y)) (C := C) (μ := Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q₀ i)))
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hB y))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open scoped NNReal BigOperators
variable {S : Type*}

 

def jetVariation : ℕ → ℕ → ℝ
  | _, 0 => 1
  | r, k+1 => 2*(r:ℝ)*(r+1)*jetVariation (r+2) k

theorem jetVariation_nonneg (r k : ℕ) : 0 ≤ jetVariation r k := by
  induction k generalizing r with
  | zero => exact zero_le_one
  | succ k ih =>
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by positivity)) (ih _)

theorem marked_pair_weight_abs_le {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) {r : ℕ} (hT : T.leaves ≤ r)
    (F : (p : MarkedPlacement T) → MarkedPlacement p.tree → ℝ) {D : ℝ}
    (hD : 0 ≤ D) (hF : ∀ p ∈ T.markedAttach 0, ∀ s ∈ p.tree.markedAttach 0, |F p s| ≤ D) :
    |((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun s => s.coeff*F p s).sum).sum/2| ≤
      (2*(r:ℝ)*(r+1))*D := by
  have hinner (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0) :
      |((p.tree.markedAttach 0).map fun s => s.coeff*F p s).sum| ≤ 2*((r:ℝ)+1)*D := by
    calc
      _ ≤ ((p.tree.markedAttach 0).map fun s => |s.coeff|).sum*D :=
        marked_list_weight_abs_le (p.tree.markedAttach 0) (F p) (hF p hp)
      _ = (2*(p.tree.leaves:ℝ))*D := by rw [p.tree.markedAttach_variation ho,sub_zero]
      _ ≤ 2*((r:ℝ)+1)*D := by
        apply mul_le_mul_of_nonneg_right _ hD
        have hh : p.tree.leaves ≤ r+1 := (T.markedAttach_leaves 0 p hp).trans (Nat.add_le_add_right hT 1)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hh) (by norm_num)
  have houter := marked_list_weight_abs_le (T.markedAttach 0)
    (fun p => ((p.tree.markedAttach 0).map fun s => s.coeff*F p s).sum) hinner
  rw [T.markedAttach_variation ho,sub_zero] at houter
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _ ≤ (2*(T.leaves:ℝ)*(2*((r:ℝ)+1)*D))/2 := div_le_div_of_nonneg_right houter (by norm_num)
    _ ≤ (2*(r:ℝ)*(2*((r:ℝ)+1)*D))/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hT) (by norm_num)
    _ = _ := by ring

variable [Fintype S] [Nonempty S] {n : ℕ}

 

theorem rootProfileJets_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (ho : MassOrdered 0 as) (Ks : List (ℕ → S → S → ℝ)) (T : ClockTree S as)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment → ℝ) {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hP : ∀ σ, |P σ| ≤ C)
    (hK : ∀ K ∈ Ks, ∀ j σ τ, |K j σ τ| ≤ M)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    |rootProfileJets w φ q₀ q x Ks T P| ≤ jetVariation r Ks.length*C*M^Ks.length := by
  induction Ks generalizing T r C with
  | nil =>
    simpa only [rootProfileJets,jetVariation,List.length_nil,pow_zero,mul_one,one_mul] using
      T.rootExpect_abs_le hw φ ho hP q₀ q x
  | cons K Ks ih =>
    have hD : 0 ≤ jetVariation (r+2) Ks.length*(C*M)*M^Ks.length := by
      exact mul_nonneg (mul_nonneg (jetVariation_nonneg _ _) (mul_nonneg hC hM)) (pow_nonneg hM _)
    have h := T.marked_pair_weight_abs_le ho hT
      (fun p s => rootProfileJets w φ q₀ q x Ks s.tree (profilePairTest P K p s)) hD
      (fun p hp s hs => by
        apply ih s.tree (r := r+2)
          (by
            have h₁ := T.markedAttach_leaves 0 p hp
            have h₂ := p.tree.markedAttach_leaves 0 s hs
            omega) (profilePairTest P K p s) (mul_nonneg hC hM)
        · intro σ
          dsimp only [profilePairTest]
          rw [abs_mul]
          exact mul_le_mul (hP _) (hK K List.mem_cons_self _ _ _) (abs_nonneg _) hC
        · intro L hL
          exact hK L (List.mem_cons_of_mem _ hL))
    change |((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun s => s.coeff*
        rootProfileJets w φ q₀ q x Ks s.tree (profilePairTest P K p s)).sum).sum/2| ≤ _
    apply h.trans_eq
    simp only [List.length_cons,jetVariation,pow_succ]
    ring

end SKFluctuations.Hierarchy.ClockTree

end

end OAI
