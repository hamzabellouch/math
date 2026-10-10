import Mathlib
import OAI.Probability.SKFluctuations.CavityFactorization
import OAI.Probability.SKFluctuations.CavityRow
import OAI.Probability.SKFluctuations.VarianceTestZeroRoot

namespace OAI

/-! Cavity Actual Endpoint. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators NNReal

abbrev RestCoordinate (n : ℕ) := Edge n ⊕ Fin n
abbrev ActiveCoordinate (n : ℕ) := RestCoordinate n ⊕ Fin 1
abbrev DormantCoordinate (n : ℕ) := Fin n ⊕ Fin 1
abbrev FullCoordinate (n : ℕ) := ActiveCoordinate n ⊕ DormantCoordinate n

def restCoefficient (n : ℕ) (σ : Spin n) : RestCoordinate n → ℝ
  | Sum.inl e => spinValue (σ e.val.1)*spinValue (σ e.val.2)/Real.sqrt (n+1 : ℕ)
  | Sum.inr i => spinValue (σ i)

def restFeature (n : ℕ) (σ : Spin n) : (RestCoordinate n → ℝ) →L[ℝ] ℝ :=
  ∑ i, restCoefficient n σ i • ContinuousLinearMap.proj i

def dormantCoefficient (n : ℕ) (σ : Spin n × Bool) : DormantCoordinate n → ℝ
  | Sum.inl i => spinValue σ.2*spinValue (σ.1 i)/Real.sqrt (n+1 : ℕ)
  | Sum.inr _ => spinValue σ.2

def dormantFeature (n : ℕ) (σ : Spin n × Bool) : (DormantCoordinate n → ℝ) →L[ℝ] ℝ :=
  ∑ i, dormantCoefficient n σ i • ContinuousLinearMap.proj i

 

def fullFeature (n : ℕ) (σ : Spin n × Bool) : (FullCoordinate n → ℝ) →L[ℝ] ℝ :=
  (productFeature (restFeature n) scalarFeature σ).comp sumLeft+
    (dormantFeature n σ).comp sumRight

def restWeight (n : ℕ) (_ : Spin n) : ℝ := (2:ℝ)^(-(n:ℤ))
def fullWeight (n : ℕ) (σ : Spin n × Bool) : ℝ := restWeight n σ.1 * (1/2:ℝ)

theorem restWeight_pos (n : ℕ) (σ : Spin n) : 0 < restWeight n σ := by
  unfold restWeight
  positivity

theorem fullWeight_eq (n : ℕ) (σ : Spin n × Bool) :
    fullWeight n σ = (2:ℝ)^(-((n+1:ℕ):ℤ)) := by
  simp only [fullWeight,restWeight,Nat.cast_add,Nat.cast_one,neg_add,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  norm_num

@[simp] theorem restFeature_apply (n : ℕ) (σ : Spin n) (x : RestCoordinate n → ℝ) :
    restFeature n σ x = ∑ j, restCoefficient n σ j*x j := by
  simp [restFeature]

@[simp] theorem dormantFeature_apply (n : ℕ) (σ : Spin n × Bool) (x : DormantCoordinate n → ℝ) :
    dormantFeature n σ x = ∑ j, dormantCoefficient n σ j*x j := by
  simp [dormantFeature]

@[simp] theorem fullFeature_apply (n : ℕ) (σ : Spin n × Bool) (x : FullCoordinate n → ℝ) :
    fullFeature n σ x =
      restFeature n σ.1 (fun i => x (.inl (.inl i)))+
      scalarFeature σ.2 (fun i => x (.inl (.inr i)))+
      dormantFeature n σ (fun i => x (.inr i)) := rfl

 
theorem fullFeature_restrict (n : ℕ) (σ : Spin n × Bool) :
    (fullFeature n σ).comp cavityEmbed = productFeature (restFeature n) scalarFeature σ := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,fullFeature_apply,cavityEmbed_inl,cavityEmbed_inr]
  rw [show (fun _ : DormantCoordinate n => (0:ℝ)) = 0 from rfl,map_zero,add_zero]
  rfl

 

def fullVariance (n : ℕ) (q : RestCoordinate n → ℝ) (t b h K : ℝ) : FullCoordinate n → ℝ :=
  Sum.elim (Sum.elim q (fun _ => (1-t)*K))
    (Sum.elim (fun _ => t*b) (fun _ => t*h))

theorem fullVariance_nonneg (n : ℕ) (q : RestCoordinate n → ℝ)
    (hq : ∀ j, 0 ≤ q j) {t b h K : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hb : 0 ≤ b) (hh : 0 ≤ h) (hK : 0 ≤ K) :
    ∀ j, 0 ≤ fullVariance n q t b h K j := by
  intro j
  rcases j with (j | i) | (i | i)
  · exact hq j
  · exact mul_nonneg (sub_nonneg.mpr ht.2) hK
  · exact mul_nonneg ht.1 hb
  · exact mul_nonneg ht.1 hh

def fullVarianceNN (n : ℕ) (q : RestCoordinate n → ℝ≥0) (t : ℝ) (b h K : ℝ≥0) :
    FullCoordinate n → ℝ≥0 := fun j => Real.toNNReal (fullVariance n (fun i => q i) t b h K j)

theorem fullVarianceNN_zero (n : ℕ) (q : RestCoordinate n → ℝ≥0) (b h K : ℝ≥0) :
    fullVarianceNN n q 0 b h K = Sum.elim (Sum.elim q (fun _ => K)) (fun _ => 0) := by
  funext j
  rcases j with (j | i) | (i | i) <;> simp [fullVarianceNN,fullVariance]

 

theorem fullHierarchy_scalar_endpoint (n : ℕ)
    (steps : List (GaussianStep (ActiveCoordinate n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ActiveCoordinate n → ℝ) :
    gaussianHierarchy (fullWeight n) (fullFeature n) (zeroRowSteps steps) (cavityEmbed x) =
      gaussianHierarchy (restWeight n) (restFeature n) (leftSteps steps) (fun j => x (.inl j))+
      gaussianHierarchy (fun _ : Bool => (1/2:ℝ)) scalarFeature (rightSteps steps) (fun j => x (.inr j)) := by
  rw [gaussianHierarchy_zeroRow]
  simp only [fullFeature_restrict]
  exact gaussianHierarchy_product (v := fun _ : Bool => (1/2:ℝ))
    (restWeight_pos n) (by intro s; norm_num)
    (restFeature n) scalarFeature steps ha x

 

theorem fullReplica_scalar_endpoint (n : ℕ)
    {steps : List (GaussianStep (ActiveCoordinate n))}
    (R : ReplicaTree (ActiveCoordinate n) (Spin n × Bool) steps)
    {a : ℝ} (ha : OrderedSteps a steps)
    (P : R.cavityLeft.Assignment → ℝ) (Q : R.cavityRight.Assignment → ℝ)
    (x : ActiveCoordinate n → ℝ) :
    R.zeroRow.expect (fullWeight n) (fullFeature n)
      (fun σ => P (R.cavityAssignment ((R.zeroRowAssignment (κ := DormantCoordinate n)) σ)).1 *
        Q (R.cavityAssignment ((R.zeroRowAssignment (κ := DormantCoordinate n)) σ)).2)
      (cavityEmbed x) =
      R.cavityLeft.expect (restWeight n) (restFeature n) P (fun j => x (.inl j))*
      R.cavityRight.expect (fun _ : Bool => (1/2:ℝ)) scalarFeature Q (fun j => x (.inr j)) := by
  have hz := R.expect_zeroRow (fullWeight n) (fullFeature n)
    (fun σ => P (R.cavityAssignment σ).1 * Q (R.cavityAssignment σ).2) x
  simp only [fullFeature_restrict] at hz
  exact hz.trans (R.expect_cavity_product (v := fun _ : Bool => (1/2:ℝ))
    (restWeight_pos n) (by intro s; norm_num) (restFeature n) scalarFeature ha P Q x)

 

def originalDisorderPoint (n : ℕ) (beta : ℝ) (g : Disorder (n+1)) : FullCoordinate n → ℝ :=
  Sum.elim (Sum.elim
    (Sum.elim (fun e => beta*g (oldEdge e)) (fun _ => 0)) (fun _ => 0))
    (Sum.elim (fun i => beta*g (rowEdge i)) (fun _ => 0))

 

theorem fullFeature_originalDisorderPoint (n : ℕ) (beta : ℝ) (g : Disorder (n+1))
    (σ : Spin n × Bool) :
    fullFeature n σ (originalDisorderPoint n beta g) =
      hamiltonian beta (n+1) g (spinEquiv n σ) := by
  rw [hamiltonian_one_site]
  simp only [fullFeature_apply,restFeature_apply,dormantFeature_apply,
    Fintype.sum_sum_type,originalDisorderPoint,Sum.elim_inl,Sum.elim_inr,
    restCoefficient,dormantCoefficient,mul_zero,Finset.sum_const_zero,add_zero,
    scalarFeature,smul_apply,ContinuousLinearMap.proj_apply,
    smul_eq_mul,spinEquiv,Equiv.coe_fn_mk,joinSpin_last]
  have hr : restSpin (joinSpin σ) = σ.1 := by
    funext i
    simp [restSpin]
  rw [hr]
  unfold restHamiltonian rowField restDisorder rowDisorder
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

 
theorem fullPartition_originalDisorderPoint (n : ℕ) (beta : ℝ) (g : Disorder (n+1)) :
    spinPartition (fullWeight n) (fullFeature n) (originalDisorderPoint n beta g) =
      partitionFunction beta (n+1) g := by
  unfold spinPartition partitionFunction
  simp_rw [fullWeight_eq,fullFeature_originalDisorderPoint]
  rw [← Finset.mul_sum]
  congr 1
  exact (spinEquiv n).sum_comp (fun σ => Real.exp (hamiltonian beta (n+1) g σ))

 

theorem fullLogPartition_originalDisorderPoint (n : ℕ) (beta : ℝ)
    (g : Disorder (n+1)) :
    spinLogPartition (fullWeight n) (fullFeature n) (originalDisorderPoint n beta g) =
      freeEnergy beta (n+1) g := by
  unfold spinLogPartition freeEnergy
  rw [fullPartition_originalDisorderPoint]

end SKFluctuations.Cavity

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S]

 
def ReplicaTree.assignmentGauge (π : S ≃ S) : {steps : List (GaussianStep ι)} →
    (R : ReplicaTree ι S steps) → R.Assignment ≃ R.Assignment
  | _, .leaf => π
  | _, .step _ R => R.assignmentGauge π
  | _, .fork R U => (R.assignmentGauge π).prodCongr (U.assignmentGauge π)

 

theorem ReplicaTree.weight_gauge (T : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x)
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps)
    (hT : ∀ p ∈ steps, MeasurePreserving T
      (Measure.pi fun i => gaussianReal 0 (p.2 i))
      (Measure.pi fun i => gaussianReal 0 (p.2 i)))
    (σ : R.Assignment) (x : ι → ℝ) :
    R.weight w φ (R.assignmentGauge π σ) (T x) = R.weight w φ σ x := by
  induction R generalizing x with
  | leaf => exact spinWeight_equiv T π hw hφ x σ
  | @step p tail R ih =>
    have ht : ∀ p ∈ tail, MeasurePreserving T
        (Measure.pi fun i => gaussianReal 0 (p.2 i))
        (Measure.pi fun i => gaussianReal 0 (p.2 i)) :=
      fun p hp => hT p (List.mem_cons_of_mem _ hp)
    exact shiftedMean_equiv T (hT _ List.mem_cons_self) p.1
      (gaussianHierarchy_equiv T π hw hφ tail ht) (fun y => ih ht σ y) x
  | fork R U ihR ihU =>
    change R.weight w φ (R.assignmentGauge π σ.1) (T x) *
      U.weight w φ (U.assignmentGauge π σ.2) (T x) = _
    rw [ihR hT,ihU hT]
    rfl

 
theorem ReplicaTree.expect_gauge (T : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x)
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps)
    (hT : ∀ p ∈ steps, MeasurePreserving T
      (Measure.pi fun i => gaussianReal 0 (p.2 i))
      (Measure.pi fun i => gaussianReal 0 (p.2 i)))
    (P : R.Assignment → ℝ) (x : ι → ℝ) :
    R.expect w φ P (T x) = R.expect w φ (fun σ => P (R.assignmentGauge π σ)) x := by
  unfold ReplicaTree.expect
  rw [← (R.assignmentGauge π).sum_comp (fun σ => R.weight w φ σ (T x)*P σ)]
  simp_rw [R.weight_gauge T π hw hφ hT]

 

theorem ReplicaTree.expect_gauge_odd (T : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (π : S ≃ S)
    {w : S → ℝ} {φ : S → (ι → ℝ) →L[ℝ] ℝ}
    (hw : ∀ s, w (π s) = w s) (hφ : ∀ s x, φ (π s) (T x) = φ s x)
    {steps : List (GaussianStep ι)} (R : ReplicaTree ι S steps)
    (hT : ∀ p ∈ steps, MeasurePreserving T
      (Measure.pi fun i => gaussianReal 0 (p.2 i))
      (Measure.pi fun i => gaussianReal 0 (p.2 i)))
    (P : R.Assignment → ℝ) (hP : ∀ σ, P (R.assignmentGauge π σ) = -P σ)
    (x : ι → ℝ) (hx : T x = x) : R.expect w φ P x = 0 := by
  have h := R.expect_gauge T π hw hφ hT P x
  rw [hx] at h
  simp only [hP,ReplicaTree.expect,mul_neg,Finset.sum_neg_distrib] at h
  unfold ReplicaTree.expect
  linarith

end SKFluctuations.Hierarchy

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators NNReal

 
def rowSpinFlip (n : ℕ) : (Spin n × Bool) ≃ (Spin n × Bool) :=
  (Equiv.refl (Spin n)).prodCongr Equiv.boolNot

@[simp] theorem rowSpinFlip_apply (n : ℕ) (σ : Spin n × Bool) :
    rowSpinFlip n σ = (σ.1,!σ.2) := rfl

@[simp] theorem spinValue_not (s : Bool) : spinValue (!s) = -spinValue s := by
  cases s <;> norm_num [spinValue]

 
def rowDriverSign (n : ℕ) : FullCoordinate n → ℝ :=
  Sum.elim (Sum.elim (fun _ => 1) (fun _ => -1)) (fun _ => -1)

theorem rowDriverSign_sq (n : ℕ) (i : FullCoordinate n) :
    rowDriverSign n i*rowDriverSign n i = 1 := by
  rcases i with (i | i) | i <;> norm_num [rowDriverSign]

def rowDriverFlip (n : ℕ) : (FullCoordinate n → ℝ) ≃L[ℝ] (FullCoordinate n → ℝ) :=
  signEquiv (rowDriverSign n) (rowDriverSign_sq n)

theorem fullWeight_rowSpinFlip (n : ℕ) (σ : Spin n × Bool) :
    fullWeight n (rowSpinFlip n σ) = fullWeight n σ := rfl

 

theorem fullFeature_rowFlip (n : ℕ) (σ : Spin n × Bool) (x : FullCoordinate n → ℝ) :
    fullFeature n (rowSpinFlip n σ) (rowDriverFlip n x) = fullFeature n σ x := by
  simp only [fullFeature_apply,rowSpinFlip_apply,restFeature_apply,dormantFeature_apply,
    rowDriverFlip,signEquiv_apply,rowDriverSign,Sum.elim_inl,Sum.elim_inr,
    one_mul,neg_one_mul,dormantCoefficient]
  congr 1
  · cases σ.2 <;> simp [scalarFeature]
  · apply Finset.sum_congr rfl
    intro i _
    rcases i with i | i <;> simp only [spinValue_not] <;> ring

theorem rowDriverFlip_gaussian (n : ℕ) (q : FullCoordinate n → ℝ≥0) :
    MeasurePreserving (rowDriverFlip n) (Measure.pi fun i => gaussianReal 0 (q i))
      (Measure.pi fun i => gaussianReal 0 (q i)) :=
  signEquiv_gaussian (rowDriverSign n) (rowDriverSign_sq n) q

 
theorem rowDriverFlip_fixed (n : ℕ) (x : FullCoordinate n → ℝ)
    (hs : ∀ i, x (.inl (.inr i)) = 0) (hr : ∀ i, x (.inr i) = 0) :
    rowDriverFlip n x = x := by
  ext i
  rcases i with (i | i) | i <;> simp [rowDriverFlip,rowDriverSign,hs,hr]

 

theorem actualRow_odd_block (n : ℕ) {steps : List (GaussianStep (FullCoordinate n))}
    (R : ReplicaTree (FullCoordinate n) (Spin n × Bool) steps)
    (P : R.Assignment → ℝ)
    (hP : ∀ σ, P (R.assignmentGauge (rowSpinFlip n) σ) = -P σ)
    (x : FullCoordinate n → ℝ)
    (hs : ∀ i, x (.inl (.inr i)) = 0) (hr : ∀ i, x (.inr i) = 0) :
    R.expect (fullWeight n) (fullFeature n) P x = 0 :=
  R.expect_gauge_odd (rowDriverFlip n) (rowSpinFlip n)
    (fullWeight_rowSpinFlip n) (fullFeature_rowFlip n)
    (fun p _ => rowDriverFlip_gaussian n p.2) P hP x (rowDriverFlip_fixed n x hs hr)

end SKFluctuations.Cavity

 

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators NNReal

def fullCoefficient (n : ℕ) (σ : Spin n × Bool) : FullCoordinate n → ℝ :=
  Sum.elim (Sum.elim (restCoefficient n σ.1) (fun _ => spinValue σ.2))
    (dormantCoefficient n σ)

@[simp] theorem scalarFeature_apply_spin (s : Bool) (x : Fin 1 → ℝ) :
    scalarFeature s x = spinValue s*x 0 := by
  cases s <;> simp [scalarFeature,spinValue]

@[simp] theorem fullFeature_single (n : ℕ) (σ : Spin n × Bool) (i : FullCoordinate n) :
    fullFeature n σ (Pi.single i 1) = fullCoefficient n σ i := by
  classical
  rcases i with (i | i) | i
  · simp [fullFeature_apply,restFeature_apply,dormantFeature_apply,
      Pi.single_apply,fullCoefficient]
  · have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [fullFeature_apply,restFeature_apply,dormantFeature_apply,
      Pi.single_apply,fullCoefficient]
  · simp [fullFeature_apply,restFeature_apply,dormantFeature_apply,
      Pi.single_apply,fullCoefficient]

def fullAmplitude (n : ℕ) : FullCoordinate n → ℝ :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => 1/Real.sqrt (n+1:ℕ)) (fun _ => 1))
    (fun _ => 1)) (Sum.elim (fun _ => 1/Real.sqrt (n+1:ℕ)) (fun _ => 1))

theorem fullAmplitude_nonneg (n : ℕ) (i : FullCoordinate n) : 0 ≤ fullAmplitude n i := by
  rcases i with ((i | i) | i) | (i | i) <;> simp [fullAmplitude,Real.sqrt_nonneg]

theorem fullFeature_abs (n : ℕ) (σ : Spin n × Bool) (i : FullCoordinate n) :
    |fullFeature n σ (Pi.single i 1)| = fullAmplitude n i := by
  rw [fullFeature_single]
  rcases i with ((i | i) | i) | (i | i) <;>
    simp [fullCoefficient,restCoefficient,dormantCoefficient,fullAmplitude,abs_mul,
      abs_spinValue,abs_div,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem fullFeature_square (n : ℕ) (σ : Spin n × Bool) (i : FullCoordinate n) :
    (fullFeature n σ (Pi.single i 1))^2 = (fullAmplitude n i)^2 := by
  rw [← fullFeature_abs n σ i,sq_abs]

theorem fullWeight_pos (n : ℕ) (σ : Spin n × Bool) : 0 < fullWeight n σ := by
  rw [fullWeight_eq]
  positivity

 

def rowChangeBound (n : ℕ) (B H K : ℝ) : FullCoordinate n → ℝ :=
  Sum.elim (Sum.elim (fun _ => 0) (fun _ => K)) (Sum.elim (fun _ => B) (fun _ => H))

theorem rowChangeBound_nonneg (n : ℕ) {B H K : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (i : FullCoordinate n) : 0 ≤ rowChangeBound n B H K i := by
  rcases i with (i | i) | (i | i) <;> simp [rowChangeBound,hB,hH,hK]

theorem rowChangeBound_cost (n : ℕ) (B H K : ℝ) :
    (∑ i, rowChangeBound n B H K i*(fullAmplitude n i)^2) =
      K+(n:ℝ)/(n+1)*B+H := by
  have hn : (0:ℝ) < n+1 := by positivity
  simp only [rowChangeBound,fullAmplitude,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    zero_mul,Finset.sum_const_zero,one_pow,mul_one,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,zero_add]
  rw [div_pow,one_pow,Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n+1:ℕ))]
  push_cast
  ring

theorem rowChangeBound_cost_le (n : ℕ) {B H K : ℝ} (hB : 0 ≤ B) :
    (∑ i, rowChangeBound n B H K i*(fullAmplitude n i)^2) ≤ K+B+H := by
  rw [rowChangeBound_cost]
  have hn : (n:ℝ)/(n+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  nlinarith

theorem fullVariance_monotone {J : Type*} [Preorder J] (n : ℕ)
    {q : J → RestCoordinate n → ℝ} {b h K : J → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : Monotone b) (hh : Monotone h) (hK : Monotone K) (i : FullCoordinate n) :
    Monotone (fun j => fullVariance n (q j) t (b j) (h j) (K j) i) := by
  rcases i with (i | i) | (i | i)
  · exact hq i
  · exact fun _ _ hj => mul_le_mul_of_nonneg_left (hK hj) (sub_nonneg.mpr ht.2)
  · exact fun _ _ hj => mul_le_mul_of_nonneg_left (hb hj) ht.1
  · exact fun _ _ hj => mul_le_mul_of_nonneg_left (hh hj) ht.1

 

theorem actualRow_disorderWeight_close (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (q r : ℕ → FullCoordinate n → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hq0 : ∀ i, 0 ≤ q 0 i) (hr0 : ∀ i, 0 ≤ r 0 i)
    {B H K : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hm : ∀ i j, j ≤ as.length → |q j i-r j i| ≤ rowChangeBound n B H K i)
    (σ : T.Assignment) (x : FullCoordinate n → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*(K+B+H))
      (T.disorderWeight (fullWeight n) (fullFeature n) 0 q σ x)
      (T.disorderWeight (fullWeight n) (fullFeature n) 0 r σ x) := by
  have h := T.disorderWeight_cumulative_close (fullWeight_pos n) (fullFeature n)
    (fun i => (fullAmplitude n i)^2) (fullFeature_square n) ho
    (fullAmplitude n) (rowChangeBound n B H K) (fullAmplitude_nonneg n)
    (fun i τ => (fullFeature_abs n τ i).le) 0 q r hq hr hq0 hr0
    (rowChangeBound_nonneg n hB hH hK) hm σ x
  apply h.mono
  exact mul_le_mul_of_nonneg_left (rowChangeBound_cost_le n hB) (by positivity)

 

theorem actualRow_disorderExpect_close (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (q r : ℕ → FullCoordinate n → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hq0 : ∀ i, 0 ≤ q 0 i) (hr0 : ∀ i, 0 ≤ r 0 i)
    {B H K : ℝ} (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hm : ∀ i j, j ≤ as.length → |q j i-r j i| ≤ rowChangeBound n B H K i)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) (x : FullCoordinate n → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*(K+B+H))
      (T.disorderExpect (fullWeight n) (fullFeature n) 0 q P x)
      (T.disorderExpect (fullWeight n) (fullFeature n) 0 r P x) :=
  T.disorderExpect_close (fullWeight n) (fullFeature n) 0 q r P hP x
    (fun σ => actualRow_disorderWeight_close n T ho q r hq hr hq0 hr0 hB hH hK hm σ x)

 

def cavityPath {J : Type*} [LinearOrder J] (n : ℕ) (U : J) (l t : ℝ)
    (q : J → RestCoordinate n → ℝ) (b h K : J → ℝ) (j : J) : FullCoordinate n → ℝ :=
  fullVariance n (q j) t (relocatedClock U l b j)
    (relocatedClock U l h j) (relocatedClock U l K j)

theorem cavityPath_monotone {J : Type*} [LinearOrder J] (n : ℕ) (U : J)
    {l t : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    {q : J → RestCoordinate n → ℝ} {b h K : J → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j) (i : FullCoordinate n) :
    Monotone (fun j => cavityPath n U l t q b h K j i) :=
  fullVariance_monotone n ht hq (relocatedClock_monotone U hl hb hb0)
    (relocatedClock_monotone U hl hh hh0) (relocatedClock_monotone U hl hK hK0) i

theorem cavityPath_nonneg {J : Type*} [LinearOrder J] (n : ℕ) (U : J)
    {l t : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    {q : J → RestCoordinate n → ℝ} {b h K : J → ℝ}
    (hq0 : ∀ j i, 0 ≤ q j i) (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j)
    (j : J) (i : FullCoordinate n) : 0 ≤ cavityPath n U l t q b h K j i :=
  fullVariance_nonneg n (q j) (hq0 j) ht (relocatedClock_nonneg U hl.1 hb0 j)
    (relocatedClock_nonneg U hl.1 hh0 j) (relocatedClock_nonneg U hl.1 hK0 j) i

theorem cavityPath_row_bound {J : Type*} [LinearOrder J] (n : ℕ) (U : J)
    {l t : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (q : J → RestCoordinate n → ℝ) {b h K : J → ℝ}
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j)
    (j : J) (i : FullCoordinate n) (hi : ∀ r, i ≠ Sum.inl (Sum.inl r)) :
    cavityPath n U l t q b h K j i ≤ rowChangeBound n (b j) (h j) (K j) i := by
  rcases i with (i | i) | (i | i)
  · exact (hi i rfl).elim
  · exact (mul_le_of_le_one_left (relocatedClock_nonneg U hl.1 hK0 j) (by linarith [ht.1])).trans
      (relocatedClock_le U hl.2 hK0 j)
  · exact (mul_le_of_le_one_left (relocatedClock_nonneg U hl.1 hb0 j) ht.2).trans
      (relocatedClock_le U hl.2 hb0 j)
  · exact (mul_le_of_le_one_left (relocatedClock_nonneg U hl.1 hh0 j) ht.2).trans
      (relocatedClock_le U hl.2 hh0 j)

 

theorem cavityPath_sub_bound {J : Type*} [LinearOrder J] (n : ℕ) (U : J)
    {l t l' t' : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hl' : l' ∈ Set.Icc (0:ℝ) 1) (ht' : t' ∈ Set.Icc (0:ℝ) 1)
    {q : J → RestCoordinate n → ℝ} {b h K : J → ℝ}
    (hq0 : ∀ j i, 0 ≤ q j i) (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j)
    (j : J) (i : FullCoordinate n) :
    |cavityPath n U l t q b h K j i-cavityPath n U l' t' q b h K j i| ≤
      rowChangeBound n (b j) (h j) (K j) i := by
  by_cases hi : ∃ r, i = Sum.inl (Sum.inl r)
  · rcases hi with ⟨r,rfl⟩
    simp [cavityPath,fullVariance,rowChangeBound]
  · have hi' : ∀ r, i ≠ Sum.inl (Sum.inl r) := fun r hir => hi ⟨r,hir⟩
    have ha := cavityPath_nonneg n U hl ht hq0 hb0 hh0 hK0 j i
    have hb := cavityPath_nonneg n U hl' ht' hq0 hb0 hh0 hK0 j i
    have hc := cavityPath_row_bound n U hl ht q hb0 hh0 hK0 j i hi'
    have hd := cavityPath_row_bound n U hl' ht' q hb0 hh0 hK0 j i hi'
    exact abs_le.mpr ⟨by linarith,by linarith⟩

 

theorem cavityPath_expect_close (n : ℕ) (U : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    {l t l' t' : ℝ} (hl : l ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hl' : l' ∈ Set.Icc (0:ℝ) 1) (ht' : t' ∈ Set.Icc (0:ℝ) 1)
    {q : ℕ → RestCoordinate n → ℝ} {b h K : ℕ → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hq0 : ∀ j i, 0 ≤ q j i) (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) (x : FullCoordinate n → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*
      (K as.length+b as.length+h as.length))
      (T.disorderExpect (fullWeight n) (fullFeature n) 0 (cavityPath n U l t q b h K) P x)
      (T.disorderExpect (fullWeight n) (fullFeature n) 0 (cavityPath n U l' t' q b h K) P x) := by
  apply actualRow_disorderExpect_close n T ho _ _
    (cavityPath_monotone n U hl ht hq hb hh hK hb0 hh0 hK0)
    (cavityPath_monotone n U hl' ht' hq hb hh hK hb0 hh0 hK0)
    (cavityPath_nonneg n U hl ht hq0 hb0 hh0 hK0 0)
    (cavityPath_nonneg n U hl' ht' hq0 hb0 hh0 hK0 0)
    (hb0 as.length) (hh0 as.length) (hK0 as.length) _ P hP x
  intro i j hj
  apply (cavityPath_sub_bound n U hl ht hl' ht' hq0 hb0 hh0 hK0 j i).trans
  rcases i with (i | i) | (i | i)
  · exact le_rfl
  · exact hK hj
  · exact hb hj
  · exact hh hj

end SKFluctuations.Cavity

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

theorem levelPairMean_product_le_succ {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (x : ι → ℝ) :
    levelPairMean w φ (fun σ τ => A σ*A τ) steps j x ≤
      levelPairMean w φ (fun σ τ => A σ*A τ) steps (j+1) x := by
  induction steps generalizing a j x with
  | nil => cases j <;> exact le_rfl
  | cons st steps ih =>
    rcases st with ⟨m,q⟩
    cases j with
    | zero =>
      simp only [levelPairMean]
      rw [hierarchyPairMean_product hw φ A A _ ha]
      have he : hierarchyPairMean w φ (fun σ τ => A σ*A τ) steps =
          fun y => gaussianHierarchyMean w φ A steps y*gaussianHierarchyMean w φ A steps y :=
        funext (hierarchyPairMean_product hw φ A A steps ha.2.2.2)
      rw [he]
      obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ steps ha.2.2.2 0).1
      have hh := shiftedMean_square_sub_nonneg
        hC.continuous
        (gaussianHierarchyMean_smooth hw φ A steps ha.2.2.2 0)
        (gaussianHierarchy_integrable hw φ steps ha.2.2.2 m q x)
      simpa only [pow_two,gaussianHierarchyMean] using sub_nonneg.mp hh
    | succ j =>
      exact shiftedMean_mono (levelPairMean_smooth hw φ _ steps ha.2.2.2 j 0)
        (levelPairMean_smooth hw φ _ steps ha.2.2.2 (j+1) 0)
        (ih ha.2.2.2 j) (gaussianHierarchy_integrable hw φ steps ha.2.2.2 m q x)

theorem levelPairMean_product_monotone {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    Monotone (fun j => levelPairMean w φ (fun σ τ => A σ*A τ) steps j x) :=
  monotone_nat_of_le_succ fun j => levelPairMean_product_le_succ hw φ A steps ha j x

theorem levelPairMean_sum {κ : Type*} [Fintype κ] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : κ → S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (x : ι → ℝ) :
    levelPairMean w φ (fun σ τ => ∑ i, K i σ τ) steps j x =
      ∑ i, levelPairMean w φ (K i) steps j x := by
  induction steps generalizing a j x with
  | nil => cases j <;> exact hierarchyPairMean_sum w φ K [] x
  | cons st steps ih =>
    cases j with
    | zero => exact hierarchyPairMean_sum w φ K _ x
    | succ j =>
      simp only [levelPairMean]
      rw [funext (ih ha.2.2.2 j)]
      exact shiftedMean_finsetSum Finset.univ (fun i _ => levelPairMean_smooth hw φ (K i) steps ha.2.2.2 j 0)
        (gaussianHierarchy_integrable hw φ steps ha.2.2.2 st.1 st.2 x)

theorem levelPairMean_const_mul {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (j : ℕ) (c : ℝ) (x : ι → ℝ) :
    levelPairMean w φ (fun σ τ => c*K σ τ) steps j x =
      c*levelPairMean w φ K steps j x := by
  simpa only [zero_mul,add_zero] using levelPairMean_linear hw φ K K steps ha c 0 j x

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal BigOperators

 

theorem levelPairMean_overlap_monotone {ι : Type*} [Fintype ι] (n : ℕ)
    {w : Spin n → ℝ} (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    Monotone (fun j => levelPairMean w φ (orderedOverlap n) steps j x) := by
  have he : orderedOverlap n = fun σ τ => (1/(n:ℝ))*∑ i, spinValue (σ i)*spinValue (τ i) := by
    funext σ τ
    unfold orderedOverlap
    ring
  intro j k hjk
  change levelPairMean w φ (orderedOverlap n) steps j x ≤
    levelPairMean w φ (orderedOverlap n) steps k x
  rw [he,levelPairMean_const_mul hw φ _ steps ha j,levelPairMean_const_mul hw φ _ steps ha k,
    levelPairMean_sum hw φ _ steps ha j,levelPairMean_sum hw φ _ steps ha k]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    levelPairMean_product_monotone hw φ (fun σ => spinValue (σ i)) steps ha x hjk) (by positivity)

theorem rootLevelPairMean_overlap_monotone {ι : Type*} [Fintype ι] (n : ℕ)
    {w : Spin n → ℝ} (hw : ∀ σ, 0 < w σ) (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ)
    (q : ι → ℝ≥0) (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) :
    Monotone (fun j => rootLevelPairMean w φ q (orderedOverlap n) steps j) := by
  intro j k hjk
  exact integral_mono
    ((levelPairMean_smooth hw φ _ steps ha j 0).integrable_zero_shift 0)
    ((levelPairMean_smooth hw φ _ steps ha k 0).integrable_zero_shift 0)
    (fun x => levelPairMean_overlap_monotone n hw φ steps ha (0+x) hjk)

end SKFluctuations

end

end OAI
