import Mathlib
import OAI.Probability.SKFluctuations.PotentialHeatTrace

namespace OAI

/-! Cavity Factorization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

section ProductIncrement
variable {E F : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [NormedAddCommGroup F]
  [MeasurableSpace F]
  {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

 

theorem shiftedContinuation_prod_add {P : E → ℝ} {Q : F → ℝ} (m : ℝ)
    (x : E × F)
    (hP : Integrable (fun z => Real.exp (m*P (x.1+z))) μ)
    (hQ : Integrable (fun z => Real.exp (m*Q (x.2+z))) ν) :
    shiftedContinuation (μ.prod ν) m (fun y => P y.1+Q y.2) x =
      shiftedContinuation μ m P x.1+shiftedContinuation ν m Q x.2 := by
  unfold shiftedContinuation
  simp only [Prod.fst_add,Prod.snd_add,mul_add,Real.exp_add]
  rw [integral_prod_mul (fun z => Real.exp (m*P (x.1+z)))
    (fun z => Real.exp (m*Q (x.2+z))),
    Real.log_mul (partition_pos m hP).ne' (partition_pos m hQ).ne']
  exact add_div _ _ _

 

theorem shiftedMean_prod_mul (m : ℝ) (P A : E → ℝ) (Q B : F → ℝ) (x : E × F) :
    shiftedMean (μ.prod ν) m (fun y => P y.1+Q y.2)
      (fun y => A y.1*B y.2) x =
      shiftedMean μ m P A x.1*shiftedMean ν m Q B x.2 := by
  unfold shiftedMean tiltedMean
  simp only [Prod.fst_add,Prod.snd_add,mul_add,Real.exp_add]
  have he (z : E × F) :
      (A (x.1+z.1)*B (x.2+z.2))*(Real.exp (m*P (x.1+z.1))*Real.exp (m*Q (x.2+z.2))) =
      (A (x.1+z.1)*Real.exp (m*P (x.1+z.1)))*
      (B (x.2+z.2)*Real.exp (m*Q (x.2+z.2))) := by ring
  simp_rw [he]
  rw [integral_prod_mul (fun z => A (x.1+z)*Real.exp (m*P (x.1+z)))
    (fun z => B (x.2+z)*Real.exp (m*Q (x.2+z))),
    integral_prod_mul (fun z => Real.exp (m*P (x.1+z)))
    (fun z => Real.exp (m*Q (x.2+z)))]
  exact mul_div_mul_comm _ _ _ _
end ProductIncrement

section SumCoordinates
variable {ι κ S T : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Fintype T]
  [Nonempty S] [Nonempty T]

def sumLeft : (ι ⊕ κ → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inl i)
def sumRight : (ι ⊕ κ → ℝ) →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Sum.inr i)

def productFeature (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    (s : S × T) : (ι ⊕ κ → ℝ) →L[ℝ] ℝ :=
  (φ s.1).comp sumLeft+(ψ s.2).comp sumRight

omit [Fintype ι] [Fintype κ] [Fintype S] [Fintype T] [Nonempty S] [Nonempty T] in
@[simp] theorem productFeature_apply (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (ψ : T → (κ → ℝ) →L[ℝ] ℝ) (s : S × T) (x : ι ⊕ κ → ℝ) :
    productFeature φ ψ s x = φ s.1 (fun i => x (Sum.inl i))+
      ψ s.2 (fun i => x (Sum.inr i)) := rfl

omit [Nonempty S] [Nonempty T] in
theorem spinPartition_product (w : S → ℝ) (v : T → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ) (x : ι ⊕ κ → ℝ) :
    spinPartition (fun s : S × T => w s.1*v s.2) (productFeature φ ψ) x =
      spinPartition w φ (fun i => x (Sum.inl i))*
      spinPartition v ψ (fun i => x (Sum.inr i)) := by
  simp only [spinPartition,productFeature_apply,Real.exp_add,Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem spinLogPartition_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ) (x : ι ⊕ κ → ℝ) :
    spinLogPartition (fun s : S × T => w s.1*v s.2) (productFeature φ ψ) x =
      spinLogPartition w φ (fun i => x (Sum.inl i))+
      spinLogPartition v ψ (fun i => x (Sum.inr i)) := by
  unfold spinLogPartition
  rw [spinPartition_product,Real.log_mul (spinPartition_pos hw φ _).ne'
    (spinPartition_pos hv ψ _).ne']

omit [Nonempty S] [Nonempty T] in
theorem spinWeight_product (w : S → ℝ) (v : T → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    (x : ι ⊕ κ → ℝ) (s : S × T) :
    spinWeight (fun s : S × T => w s.1*v s.2) (productFeature φ ψ) x s =
      spinWeight w φ (fun i => x (Sum.inl i)) s.1*
      spinWeight v ψ (fun i => x (Sum.inr i)) s.2 := by
  simp only [spinWeight,productFeature_apply,Real.exp_add,spinPartition_product]
  rw [← mul_div_mul_comm]
  congr 1
  ring

def leftSteps (steps : List (GaussianStep (ι ⊕ κ))) : List (GaussianStep ι) :=
  steps.map fun p => (p.1,fun i => p.2 (Sum.inl i))
def rightSteps (steps : List (GaussianStep (ι ⊕ κ))) : List (GaussianStep κ) :=
  steps.map fun p => (p.1,fun i => p.2 (Sum.inr i))

omit [Fintype ι] [Fintype κ] in
theorem OrderedSteps.leftSteps {a : ℝ} {steps : List (GaussianStep (ι ⊕ κ))}
    (h : OrderedSteps a steps) : OrderedSteps a (leftSteps steps) := by
  induction steps generalizing a with
  | nil => exact h
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    exact ⟨h.1,h.2.1,h.2.2.1,ih h.2.2.2⟩

omit [Fintype ι] [Fintype κ] in
theorem OrderedSteps.rightSteps {a : ℝ} {steps : List (GaussianStep (ι ⊕ κ))}
    (h : OrderedSteps a steps) : OrderedSteps a (rightSteps steps) := by
  induction steps generalizing a with
  | nil => exact h
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    exact ⟨h.1,h.2.1,h.2.2.1,ih h.2.2.2⟩

 

theorem gaussianHierarchy_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    (steps : List (GaussianStep (ι ⊕ κ))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ι ⊕ κ → ℝ) :
    gaussianHierarchy (fun s : S × T => w s.1*v s.2) (productFeature φ ψ) steps x =
      gaussianHierarchy w φ (leftSteps steps) (fun i => x (Sum.inl i))+
      gaussianHierarchy v ψ (rightSteps steps) (fun i => x (Sum.inr i)) := by
  induction steps generalizing a x with
  | nil => exact spinLogPartition_product hw hv φ ψ x
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    simp only [gaussianHierarchy,leftSteps,rightSteps,List.map_cons]
    have htail := ha.2.2.2
    have hi : gaussianHierarchy (fun s : S × T => w s.1*v s.2)
        (productFeature φ ψ) tail = fun y =>
        gaussianHierarchy w φ (leftSteps tail) (fun i => y (Sum.inl i))+
        gaussianHierarchy v ψ (rightSteps tail) (fun i => y (Sum.inr i)) :=
      funext fun y => ih htail y
    rw [hi]
    let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
    have hp := measurePreserving_sumPiEquivProdPi (fun j => gaussianReal 0 (q j))
    have heq := hp.integral_comp e.measurableEmbedding
      (fun z => Real.exp (m*(gaussianHierarchy w φ (leftSteps tail)
          ((fun i => x (Sum.inl i))+z.1)+
        gaussianHierarchy v ψ (rightSteps tail) ((fun i => x (Sum.inr i))+z.2))))
    change Real.log (∫ z, Real.exp (m*(gaussianHierarchy w φ (leftSteps tail)
        (fun i => (x+z) (Sum.inl i))+
      gaussianHierarchy v ψ (rightSteps tail) (fun i => (x+z) (Sum.inr i))))
        ∂Measure.pi fun j => gaussianReal 0 (q j)) / m = _
    simp only [MeasurableEquiv.coe_sumPiEquivProdPi,Equiv.sumPiEquivProdPi,Equiv.coe_fn_mk] at heq
    simp only [Pi.add_def] at heq ⊢
    rw [heq]
    exact shiftedContinuation_prod_add m
      ((fun i => x (Sum.inl i)),(fun i => x (Sum.inr i)))
      (gaussianHierarchy_integrable hw φ _ htail.leftSteps m _ _)
      (gaussianHierarchy_integrable hv ψ _ htail.rightSteps m _ _)

 
theorem integral_sumGaussian (q : ι ⊕ κ → ℝ≥0)
    (f : (ι → ℝ) × (κ → ℝ) → ℝ) :
    (∫ z, f ((fun i => z (Sum.inl i)),(fun i => z (Sum.inr i)))
      ∂Measure.pi fun j => gaussianReal 0 (q j)) =
      ∫ z, f z ∂(Measure.pi fun i => gaussianReal 0 (q (Sum.inl i))).prod
        (Measure.pi fun i => gaussianReal 0 (q (Sum.inr i))) := by
  have h := (measurePreserving_sumPiEquivProdPi (fun j => gaussianReal 0 (q j))).integral_comp'
    f
  simpa only [MeasurableEquiv.coe_sumPiEquivProdPi,Equiv.sumPiEquivProdPi,Equiv.coe_fn_mk] using h

theorem shiftedMean_sum_mul (q : ι ⊕ κ → ℝ≥0) (m : ℝ)
    (P A : (ι → ℝ) → ℝ) (Q B : (κ → ℝ) → ℝ) (x : ι ⊕ κ → ℝ) :
    shiftedMean (Measure.pi fun j => gaussianReal 0 (q j)) m
      (fun z => P (fun i => z (Sum.inl i))+Q (fun i => z (Sum.inr i)))
      (fun z => A (fun i => z (Sum.inl i))*B (fun i => z (Sum.inr i))) x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q (Sum.inl i))) m P A
        (fun i => x (Sum.inl i))*
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q (Sum.inr i))) m Q B
        (fun i => x (Sum.inr i)) := by
  have hn := integral_sumGaussian q (fun z =>
    (A ((fun i => x (Sum.inl i))+z.1)*B ((fun i => x (Sum.inr i))+z.2))*
      Real.exp (m*(P ((fun i => x (Sum.inl i))+z.1)+Q ((fun i => x (Sum.inr i))+z.2))))
  have hd := integral_sumGaussian q (fun z =>
      Real.exp (m*(P ((fun i => x (Sum.inl i))+z.1)+Q ((fun i => x (Sum.inr i))+z.2))))
  have hh := shiftedMean_prod_mul (μ := Measure.pi fun i => gaussianReal 0 (q (Sum.inl i)))
    (ν := Measure.pi fun i => gaussianReal 0 (q (Sum.inr i))) m P A Q B
    ((fun i => x (Sum.inl i)),(fun i => x (Sum.inr i)))
  unfold shiftedMean tiltedMean at hh ⊢
  simp only [Prod.fst_add,Prod.snd_add,Pi.add_def] at hn hd hh ⊢
  rw [hn,hd]
  exact hh

 

theorem gaussianHierarchyMean_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (B : T → ℝ)
    (steps : List (GaussianStep (ι ⊕ κ))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : ι ⊕ κ → ℝ) :
    gaussianHierarchyMean (fun s : S × T => w s.1*v s.2) (productFeature φ ψ)
        (fun s => A s.1*B s.2) steps x =
      gaussianHierarchyMean w φ A (leftSteps steps) (fun i => x (Sum.inl i))*
      gaussianHierarchyMean v ψ B (rightSteps steps) (fun i => x (Sum.inr i)) := by
  induction steps generalizing a x with
  | nil =>
    simp only [leftSteps,rightSteps,List.map_nil,gaussianHierarchyMean,spinWeight_product,Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    simp only [gaussianHierarchyMean,leftSteps,rightSteps,List.map_cons]
    have htail := ha.2.2.2
    have hP := funext fun y => gaussianHierarchy_product hw hv φ ψ tail htail y
    have hA := funext fun y => ih htail y
    rw [hP,hA]
    exact shiftedMean_sum_mul q m _ _ _ _ x

 
def ReplicaTree.cavityLeft : {steps : List (GaussianStep (ι ⊕ κ))} →
    ReplicaTree (ι ⊕ κ) (S × T) steps → ReplicaTree ι S (leftSteps steps)
  | _, .leaf => .leaf
  | _, .step (m,q) R => .step (m,fun i => q (Sum.inl i)) R.cavityLeft
  | _, .fork R U => .fork R.cavityLeft U.cavityLeft

 
def ReplicaTree.cavityRight : {steps : List (GaussianStep (ι ⊕ κ))} →
    ReplicaTree (ι ⊕ κ) (S × T) steps → ReplicaTree κ T (rightSteps steps)
  | _, .leaf => .leaf
  | _, .step (m,q) R => .step (m,fun i => q (Sum.inr i)) R.cavityRight
  | _, .fork R U => .fork R.cavityRight U.cavityRight

 

def ReplicaTree.cavityAssignment : {steps : List (GaussianStep (ι ⊕ κ))} →
    (R : ReplicaTree (ι ⊕ κ) (S × T) steps) →
    R.Assignment ≃ R.cavityLeft.Assignment × R.cavityRight.Assignment
  | _, .leaf => Equiv.refl _
  | _, .step _ R => R.cavityAssignment
  | _, .fork R U => (R.cavityAssignment.prodCongr U.cavityAssignment).trans
      (Equiv.prodProdProdComm _ _ _ _)

 

theorem ReplicaTree.weight_cavity_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep (ι ⊕ κ))} (R : ReplicaTree (ι ⊕ κ) (S × T) steps)
    {a : ℝ} (ha : OrderedSteps a steps) (σ : R.Assignment) (x : ι ⊕ κ → ℝ) :
    R.weight (fun s => w s.1*v s.2) (productFeature φ ψ) σ x =
      R.cavityLeft.weight w φ (R.cavityAssignment σ).1 (fun i => x (Sum.inl i))*
      R.cavityRight.weight v ψ (R.cavityAssignment σ).2 (fun i => x (Sum.inr i)) := by
  induction R generalizing a x with
  | leaf => exact spinWeight_product w v φ ψ x σ
  | @step st tail R ih =>
    obtain ⟨m,q⟩ := st
    change shiftedMean _ m _ _ x = _
    have hP := funext fun y => gaussianHierarchy_product hw hv φ ψ tail ha.2.2.2 y
    have hA := funext fun y => ih ha.2.2.2 σ y
    rw [hP,hA]
    exact shiftedMean_sum_mul q m _ _ _ _ x
  | fork R U ihR ihU =>
    change R.weight _ _ σ.1 x*U.weight _ _ σ.2 x = _
    rw [ihR ha,ihU ha]
    exact mul_mul_mul_comm _ _ _ _

 

theorem ReplicaTree.expect_cavity_product {w : S → ℝ} {v : T → ℝ}
    (hw : ∀ s, 0 < w s) (hv : ∀ t, 0 < v t)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ψ : T → (κ → ℝ) →L[ℝ] ℝ)
    {steps : List (GaussianStep (ι ⊕ κ))} (R : ReplicaTree (ι ⊕ κ) (S × T) steps)
    {a : ℝ} (ha : OrderedSteps a steps)
    (P : R.cavityLeft.Assignment → ℝ) (Q : R.cavityRight.Assignment → ℝ)
    (x : ι ⊕ κ → ℝ) :
    R.expect (fun s => w s.1*v s.2) (productFeature φ ψ)
      (fun σ => P (R.cavityAssignment σ).1*Q (R.cavityAssignment σ).2) x =
      R.cavityLeft.expect w φ P (fun i => x (Sum.inl i))*
      R.cavityRight.expect v ψ Q (fun i => x (Sum.inr i)) := by
  unfold ReplicaTree.expect
  simp_rw [R.weight_cavity_product hw hv φ ψ ha]
  let f := fun σ : R.cavityLeft.Assignment × R.cavityRight.Assignment =>
    (R.cavityLeft.weight w φ σ.1 (fun i => x (Sum.inl i))*P σ.1)*
    (R.cavityRight.weight v ψ σ.2 (fun i => x (Sum.inr i))*Q σ.2)
  calc
    _ = ∑ σ, f (R.cavityAssignment σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      dsimp [f]
      ring
    _ = ∑ σ, f σ := R.cavityAssignment.sum_comp f
    _ = _ := by
      simp only [f,Fintype.sum_prod_type]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
end SumCoordinates
end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

 

def cavityEmbed : (ι → ℝ) →L[ℝ] (ι ⊕ κ → ℝ) :=
  ContinuousLinearMap.pi fun j => match j with
    | Sum.inl i => ContinuousLinearMap.proj i
    | Sum.inr _ => 0

omit [Fintype ι] [Fintype κ] [Fintype S] in
@[simp] theorem cavityEmbed_inl (x : ι → ℝ) (i : ι) :
    cavityEmbed (κ := κ) x (Sum.inl i) = x i := rfl
omit [Fintype ι] [Fintype κ] [Fintype S] in
@[simp] theorem cavityEmbed_inr (x : ι → ℝ) (j : κ) :
    cavityEmbed x (Sum.inr j) = 0 := rfl

 

theorem integral_zeroRowGaussian (q : ι → ℝ≥0) (f : (ι ⊕ κ → ℝ) → ℝ) :
    (∫ z, f z ∂Measure.pi (fun j : ι ⊕ κ => gaussianReal 0 (Sum.elim q (fun _ => 0) j))) =
      ∫ z, f (cavityEmbed z) ∂Measure.pi fun i => gaussianReal 0 (q i) := by
  have hs := integral_sumGaussian (Sum.elim q (fun _ : κ => 0))
    (fun z : (ι → ℝ) × (κ → ℝ) => f (Sum.elim z.1 z.2))
  have he (z : ι ⊕ κ → ℝ) : Sum.elim (fun i => z (.inl i)) (fun i => z (.inr i)) = z := by
    funext j
    cases j <;> rfl
  simp only [he, Sum.elim_inl, Sum.elim_inr] at hs
  rw [isotropicGaussian_zero, Measure.prod_dirac,
    (measurableEmbedding_prod_mk_right (0 : κ → ℝ)).integral_map] at hs
  rw [hs]
  congr 1
  funext x
  congr 1
  funext j
  cases j <;> rfl

 

theorem shiftedContinuation_zeroRow (q : ι → ℝ≥0) (m : ℝ)
    (F : (ι ⊕ κ → ℝ) → ℝ) (x : ι → ℝ) :
    shiftedContinuation (Measure.pi (fun j : ι ⊕ κ => gaussianReal 0 (Sum.elim q (fun _ => 0) j))) m F (cavityEmbed x) =
      shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m
        (fun y => F (cavityEmbed y)) x := by
  unfold shiftedContinuation
  rw [integral_zeroRowGaussian]
  simp only [map_add]

 
theorem shiftedMean_zeroRow (q : ι → ℝ≥0) (m : ℝ)
    (F A : (ι ⊕ κ → ℝ) → ℝ) (x : ι → ℝ) :
    shiftedMean (Measure.pi (fun j : ι ⊕ κ => gaussianReal 0 (Sum.elim q (fun _ => 0) j))) m F A (cavityEmbed x) =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
        (fun y => F (cavityEmbed y)) (fun y => A (cavityEmbed y)) x := by
  unfold shiftedMean tiltedMean
  rw [integral_zeroRowGaussian,integral_zeroRowGaussian]
  simp only [map_add]

 
def zeroRowSteps (steps : List (GaussianStep ι)) : List (GaussianStep (ι ⊕ κ)) :=
  steps.map fun p => (p.1, Sum.elim p.2 (fun _ => 0))

omit [Fintype ι] [Fintype κ] [Fintype S] in
theorem zeroRowSteps_ordered {a : ℝ} {steps : List (GaussianStep ι)}
    (h : OrderedSteps a steps) : OrderedSteps a (zeroRowSteps (κ := κ) steps) := by
  induction steps generalizing a with
  | nil => exact h
  | cons p tail ih => exact ⟨h.1,h.2.1,h.2.2.1,ih h.2.2.2⟩

 

theorem gaussianHierarchy_zeroRow (w : S → ℝ)
    (φ : S → (ι ⊕ κ → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (x : ι → ℝ) :
    gaussianHierarchy w φ (zeroRowSteps steps) (cavityEmbed x) =
      gaussianHierarchy w (fun s => (φ s).comp cavityEmbed) steps x := by
  induction steps generalizing x with
  | nil => rfl
  | cons p tail ih =>
    obtain ⟨m,q⟩ := p
    simp only [zeroRowSteps,List.map_cons,gaussianHierarchy]
    rw [shiftedContinuation_zeroRow]
    exact congrArg (fun F => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m F x)
      (funext ih)

 
def ReplicaTree.zeroRow : {steps : List (GaussianStep ι)} →
    ReplicaTree ι S steps → ReplicaTree (ι ⊕ κ) S (zeroRowSteps steps)
  | _, .leaf => .leaf
  | _, .step (m,q) R => .step (m,Sum.elim q (fun _ => 0)) R.zeroRow
  | _, .fork R U => .fork R.zeroRow U.zeroRow

 

def ReplicaTree.zeroRowAssignment : {steps : List (GaussianStep ι)} →
    (R : ReplicaTree ι S steps) → (R.zeroRow (κ := κ)).Assignment ≃ R.Assignment
  | _, .leaf => Equiv.refl _
  | _, .step _ R => R.zeroRowAssignment
  | _, .fork R U => R.zeroRowAssignment.prodCongr U.zeroRowAssignment

 
theorem ReplicaTree.weight_zeroRow (w : S → ℝ)
    (φ : S → (ι ⊕ κ → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (R : ReplicaTree ι S steps) (σ : R.zeroRow.Assignment) (x : ι → ℝ) :
    R.zeroRow.weight w φ σ (cavityEmbed x) =
      R.weight w (fun s => (φ s).comp cavityEmbed) ((R.zeroRowAssignment (κ := κ)) σ) x := by
  induction R generalizing x with
  | leaf => rfl
  | @step st tail R ih =>
    obtain ⟨m,q⟩ := st
    change shiftedMean _ m _ _ (cavityEmbed x) = _
    rw [shiftedMean_zeroRow]
    change shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
      (fun y => gaussianHierarchy w φ (zeroRowSteps tail) (cavityEmbed y))
      (fun y => R.zeroRow.weight w φ σ (cavityEmbed y)) x =
      shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
        (gaussianHierarchy w (fun s => (φ s).comp cavityEmbed) tail)
        (R.weight w (fun s => (φ s).comp cavityEmbed) ((R.zeroRowAssignment (κ := κ)) σ)) x
    have hF := funext fun y => gaussianHierarchy_zeroRow w φ tail y
    rw [hF]
    exact congrArg (fun A => shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
      (gaussianHierarchy w (fun s => (φ s).comp cavityEmbed) tail) A x) (funext (ih σ))
  | fork R U ihR ihU =>
    change R.zeroRow.weight w φ σ.1 (cavityEmbed x)*U.zeroRow.weight w φ σ.2 (cavityEmbed x) = _
    rw [ihR,ihU]
    rfl

 
theorem ReplicaTree.expect_zeroRow (w : S → ℝ)
    (φ : S → (ι ⊕ κ → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (R : ReplicaTree ι S steps) (P : R.Assignment → ℝ) (x : ι → ℝ) :
    R.zeroRow.expect w φ (fun σ => P ((R.zeroRowAssignment (κ := κ)) σ)) (cavityEmbed x) =
      R.expect w (fun s => (φ s).comp cavityEmbed) P x := by
  unfold ReplicaTree.expect
  simp_rw [R.weight_zeroRow]
  exact (R.zeroRowAssignment (κ := κ)).sum_comp
    (fun σ : R.Assignment => R.weight w (fun s => (φ s).comp cavityEmbed) σ x * P σ)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {ι S T : Type*} [Fintype ι] [Fintype S] [Fintype T]

 
theorem spinPartition_spin_equiv (e : S ≃ T) (w : T → ℝ)
    (φ : T → (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    spinPartition (w ∘ e) (φ ∘ e) x = spinPartition w φ x :=
  e.sum_comp (fun s => w s * Real.exp (φ s x))

theorem spinLogPartition_spin_equiv (e : S ≃ T) (w : T → ℝ)
    (φ : T → (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    spinLogPartition (w ∘ e) (φ ∘ e) x = spinLogPartition w φ x := by
  unfold spinLogPartition
  rw [spinPartition_spin_equiv]

 

theorem gaussianHierarchy_spin_equiv (e : S ≃ T) (w : T → ℝ)
    (φ : T → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι)) (x : ι → ℝ) :
    gaussianHierarchy (w ∘ e) (φ ∘ e) steps x = gaussianHierarchy w φ steps x := by
  induction steps generalizing x with
  | nil => exact spinLogPartition_spin_equiv e w φ x
  | cons p tail ih =>
    change shiftedContinuation _ _ _ x = shiftedContinuation _ _ _ x
    rw [funext ih]

 
theorem spinWeight_spin_equiv (e : S ≃ T) (w : T → ℝ)
    (φ : T → (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) (s : S) :
    spinWeight (w ∘ e) (φ ∘ e) x s = spinWeight w φ x (e s) := by
  unfold spinWeight
  rw [spinPartition_spin_equiv]
  rfl

 

def ReplicaTree.spinEquiv (e : S ≃ T) : {steps : List (GaussianStep ι)} →
    ReplicaTree ι S steps → ReplicaTree ι T steps
  | _, .leaf => .leaf
  | _, .step p R => .step p (R.spinEquiv e)
  | _, .fork R U => .fork (R.spinEquiv e) (U.spinEquiv e)

def ReplicaTree.spinAssignmentEquiv (e : S ≃ T) : {steps : List (GaussianStep ι)} →
    (R : ReplicaTree ι S steps) → R.Assignment ≃ (R.spinEquiv e).Assignment
  | _, .leaf => e
  | _, .step _ R => R.spinAssignmentEquiv e
  | _, .fork R U => (R.spinAssignmentEquiv e).prodCongr (U.spinAssignmentEquiv e)

 

theorem ReplicaTree.weight_spin_equiv (e : S ≃ T) (w : T → ℝ)
    (φ : T → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (R : ReplicaTree ι S steps) (σ : R.Assignment) (x : ι → ℝ) :
    R.weight (w ∘ e) (φ ∘ e) σ x =
      (R.spinEquiv e).weight w φ (R.spinAssignmentEquiv e σ) x := by
  induction R generalizing x with
  | leaf => exact spinWeight_spin_equiv e w φ x σ
  | @step p tail R ih =>
    change shiftedMean _ p.1 (gaussianHierarchy (w ∘ e) (φ ∘ e) tail)
      (R.weight (w ∘ e) (φ ∘ e) σ) x =
      shiftedMean _ p.1 (gaussianHierarchy w φ tail)
        ((R.spinEquiv e).weight w φ (R.spinAssignmentEquiv e σ)) x
    rw [funext (gaussianHierarchy_spin_equiv e w φ tail),funext (ih σ)]
  | fork R U ihR ihU =>
    change R.weight _ _ σ.1 x * U.weight _ _ σ.2 x = _
    rw [ihR,ihU]
    rfl

 

theorem ReplicaTree.expect_spin_equiv (e : S ≃ T) (w : T → ℝ)
    (φ : T → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (R : ReplicaTree ι S steps) (P : (R.spinEquiv e).Assignment → ℝ) (x : ι → ℝ) :
    R.expect (w ∘ e) (φ ∘ e) (fun σ => P (R.spinAssignmentEquiv e σ)) x =
      (R.spinEquiv e).expect w φ P x := by
  unfold ReplicaTree.expect
  simp_rw [R.weight_spin_equiv]
  exact (R.spinAssignmentEquiv e).sum_comp (fun σ => (R.spinEquiv e).weight w φ σ x * P σ)

end SKFluctuations.Hierarchy

end

end OAI
