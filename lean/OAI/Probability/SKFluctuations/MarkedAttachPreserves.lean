import Mathlib
import OAI.Probability.SKFluctuations.Chain
import OAI.Probability.SKFluctuations.CompContDiff

namespace OAI

/-! Marked Attach Preserves. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem markedAttach_preserves {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (p : MarkedPlacement T) (hp : p ∈ T.markedAttach a) :
    p.toPlacement.Preserves w φ := by
  apply attach_preserves hw φ T ha p.toPlacement
  rw [← T.markedAttach_forget a]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

 

 theorem markedAttach_tested_hit {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (s : T.Slot) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    ((T.markedAttach a).map fun p => p.coeff*p.hit s*
      p.tree.expect w φ (fun σ => P (p.restrict σ)) x).sum = T.expect w φ P x := by
  have he : ((T.markedAttach a).map fun p => p.coeff*p.hit s*
      p.tree.expect w φ (fun σ => P (p.restrict σ)) x).sum =
      ((T.markedAttach a).map fun p => p.coeff*p.hit s*T.expect w φ P x).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.markedAttach_preserves hw φ ha p hp P x]
  rw [he,List.sum_map_mul_right,T.markedAttach_hit a s,one_mul]

 

 theorem markedAttach_tested_diagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    ((T.markedAttach a).map fun p => p.coeff*
      ((p.tree.markedAttach a).map fun q => q.coeff*q.hit p.mark*
        q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))) x).sum).sum = a*T.expect w φ P x := by
  have hi (p : MarkedPlacement T) :
      ((p.tree.markedAttach a).map fun q => q.coeff*q.hit p.mark*
        q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))) x).sum =
        p.tree.expect w φ (fun τ => P (p.restrict τ)) x :=
    p.tree.markedAttach_tested_hit hw φ ha p.mark (fun τ => P (p.restrict τ)) x
  simp_rw [hi]
  have he : ((T.markedAttach a).map fun p => p.coeff*
      p.tree.expect w φ (fun σ => P (p.restrict σ)) x).sum =
      ((T.markedAttach a).map fun p => p.coeff*T.expect w φ P x).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.markedAttach_preserves hw φ ha p hp P x]
  rw [he,List.sum_map_mul_right,T.markedAttach_mass a]

 theorem markedAttach_zero_diagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ReplicaTree ι S steps)
    (ha : OrderedSteps 0 steps) (P : T.Assignment → ℝ) (x : ι → ℝ) :
    ((T.markedAttach 0).map fun p => p.coeff*
      ((p.tree.markedAttach 0).map fun q => q.coeff*q.hit p.mark*
        q.tree.expect w φ (fun σ => P (p.restrict (q.restrict σ))) x).sum).sum = 0 := by
  rw [T.markedAttach_tested_diagonal hw φ ha,zero_mul]

end SKFluctuations.Hierarchy.ReplicaTree

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

 
def coordinateEquiv (e : κ ≃ ι) : (κ → ℝ) ≃L[ℝ] (ι → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : ι => ℝ) e

omit [Fintype ι] [Fintype κ] in
 theorem coordinateEquiv_apply (e : κ ≃ ι) (x : κ → ℝ) (i : ι) :
    coordinateEquiv e x i = x (e.symm i) := by
  obtain ⟨j,rfl⟩ := e.surjective i
  change Equiv.piCongrLeft (fun _ : ι => ℝ) e x (e j) = _
  simp only [Equiv.piCongrLeft_apply_apply,Equiv.symm_apply_apply]

 theorem coordinateEquiv_measPres (e : κ ≃ ι) (q : ι → ℝ≥0) :
    MeasurePreserving (coordinateEquiv e) (Measure.pi fun i => gaussianReal 0 (q (e i)))
      (Measure.pi fun i => gaussianReal 0 (q i)) :=
  measurePreserving_piCongrLeft (fun i => gaussianReal 0 (q i)) e

omit [Fintype ι] [Fintype κ] in
 theorem coordinateEquiv_single [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) (i : κ) :
    coordinateEquiv e (Pi.single i 1) = Pi.single (e i) 1 := by
  classical
  ext j
  simp only [coordinateEquiv_apply,Pi.single_apply,Equiv.symm_apply_eq]

 theorem shiftedContinuation_reindex (e : κ ≃ ι) (q : ι → ℝ≥0)
    (m : ℝ) (F : (ι → ℝ) → ℝ) (x : κ → ℝ) :
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q (e i))) m
      (fun y => F (coordinateEquiv e y)) x =
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m F (coordinateEquiv e x) := by
  unfold shiftedContinuation
  have h := (coordinateEquiv_measPres e q).integral_comp
    (coordinateEquiv e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => Real.exp (m*F (coordinateEquiv e x+z)))
  simpa only [← map_add] using congrArg (fun z : ℝ => Real.log z/m) h

 theorem shiftedMean_reindex (e : κ ≃ ι) (q : ι → ℝ≥0)
    (m : ℝ) (F A : (ι → ℝ) → ℝ) (x : κ → ℝ) :
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q (e i))) m
      (fun y => F (coordinateEquiv e y)) (fun y => A (coordinateEquiv e y)) x =
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m F A (coordinateEquiv e x) := by
  unfold shiftedMean tiltedMean
  have h₁ := (coordinateEquiv_measPres e q).integral_comp
    (coordinateEquiv e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => A (coordinateEquiv e x+z)*Real.exp (m*F (coordinateEquiv e x+z)))
  have h₂ := (coordinateEquiv_measPres e q).integral_comp
    (coordinateEquiv e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => Real.exp (m*F (coordinateEquiv e x+z)))
  simp_rw [← map_add] at h₁ h₂
  rw [h₁,h₂]

 def reindexFeature (e : κ ≃ ι) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    S → (κ → ℝ) →L[ℝ] ℝ := fun σ => (φ σ).comp (coordinateEquiv e).toContinuousLinearMap

 theorem spinWeight_reindex (e : κ ≃ ι) (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (x : κ → ℝ) (σ : S) :
    spinWeight w (reindexFeature e φ) x σ = spinWeight w φ (coordinateEquiv e x) σ := rfl

 theorem gaussianHierarchy_clock_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) :
    gaussianHierarchy w (reindexFeature e φ) (clockSteps as (fun j i => q j (e i))) =
      fun x => gaussianHierarchy w φ (clockSteps as q) (coordinateEquiv e x) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih =>
    funext x
    change shiftedContinuation _ _ (gaussianHierarchy w (reindexFeature e φ)
      (clockSteps as (fun j i => q (j+1) (e i)))) x = _
    rw [ih]
    exact shiftedContinuation_reindex e (q 0) a.val _ x

 theorem ClockTree.weight_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q : ℕ → ι → ℝ≥0) (σ : T.Assignment) (x : κ → ℝ) :
    T.weight w (reindexFeature e φ) (fun j i => q j (e i)) σ x =
      T.weight w φ q σ (coordinateEquiv e x) := by
  induction T generalizing q x with
  | leaf => rfl
  | step a T ih =>
    simp only [ClockTree.weight_step]
    rw [gaussianHierarchy_clock_reindex]
    have he : (fun y => T.weight w (reindexFeature e φ) (fun j i => q (j+1) (e i)) σ y) =
        fun y => T.weight w φ (fun j => q (j+1)) σ (coordinateEquiv e y) := funext (fun y => ih _ σ y)
    change shiftedMean _ _ _ (fun y => T.weight w (reindexFeature e φ) (fun j i => q (j+1) (e i)) σ y) x = _
    rw [he]
    exact shiftedMean_reindex e (q 0) a.val _ _ x
  | fork T U ihT ihU =>
    simp only [ClockTree.weight_fork,ihT,ihU]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

 

noncomputable def ClockTree.disorderWeight (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (l : ι → ℝ)
    (q : ℕ → ι → ℝ) (σ : T.Assignment) (x : ι → ℝ) : ℝ :=
  ∫ z, T.weight w φ (cumulativeIncrements (q 0) (fun j => q (j+1))) σ (x+z)
    ∂(Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i-l i)))

 theorem ClockTree.rootWeight_eq_disorder {n : ℕ} (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (σ : T.Assignment) (x : Fin (n+1) → ℝ) :
    T.rootWeight w φ l q σ x = T.disorderWeight w φ l q σ x := by
  simp only [ClockTree.rootWeight,ClockTree.atomicHead,shiftedMean_zero,
    zeroContinuation,ClockTree.disorderWeight]

 theorem ClockTree.disorderWeight_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (l : ι → ℝ) (q : ℕ → ι → ℝ) (σ : T.Assignment) (x : κ → ℝ) :
    T.disorderWeight w (reindexFeature e φ) (fun i => l (e i)) (fun j i => q j (e i)) σ x =
      T.disorderWeight w φ l q σ (coordinateEquiv e x) := by
  unfold ClockTree.disorderWeight
  have he : cumulativeIncrements (fun i => q 0 (e i)) (fun j i => q (j+1) (e i)) =
      fun j i => cumulativeIncrements (q 0) (fun k => q (k+1)) j (e i) := by
    funext j i
    cases j <;> rfl
  rw [he]
  simp_rw [T.weight_reindex, map_add]
  exact (coordinateEquiv_measPres e (fun i => Real.toNNReal (q 0 i-l i))).integral_comp
    (coordinateEquiv e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun z => T.weight w φ (cumulativeIncrements (q 0) (fun j => q (j+1))) σ (coordinateEquiv e x+z))

variable [Nonempty S]

 theorem ClockTree.disorderWeight_probability {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (l : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    (∀ σ, 0 ≤ T.disorderWeight w φ l q σ x) ∧ ∑ σ, T.disorderWeight w φ l q σ x = 1 := by
  constructor
  · intro σ
    exact integral_nonneg fun z => (T.weight_probability hw φ ho _ (x+z)).1 σ
  · unfold ClockTree.disorderWeight
    rw [← integral_finsetSum Finset.univ (fun σ _ =>
      (T.weight_smooth hw φ ho _ σ 0).integrable_zero_shift x)]
    simp_rw [(T.weight_probability hw φ ho _ _).2]
    simp

 

 theorem ClockTree.disorderWeight_cumulative_close [DecidableEq ι] [Nonempty ι] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as) (D M : ι → ℝ)
    (hD : ∀ i, 0 ≤ D i) (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (l : ι → ℝ) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hM : ∀ i, 0 ≤ M i) (hm : ∀ i j, j ≤ as.length → |q j i-r j i| ≤ M i)
    (σ : T.Assignment) (x : ι → ℝ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*∑ i, M i*(D i)^2)
      (T.disorderWeight w φ l q σ x) (T.disorderWeight w φ l r σ x) := by
  classical
  let d := Fintype.card ι-1
  have hd : d+1 = Fintype.card ι := Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  let e : Fin (d+1) ≃ ι := (finCongr hd).trans (Fintype.equivFin ι).symm
  have hp (τ : S) (i : Fin (d+1)) : reindexFeature e φ τ (Pi.single i 1) = φ τ (Pi.single (e i) 1) := by
    change φ τ (coordinateEquiv e (Pi.single i 1)) = _
    rw [coordinateEquiv_single]
  have h := T.rootCumulative_close hw (reindexFeature e φ) (fun i => C (e i))
    (fun τ i => by rw [hp]; exact hC τ (e i)) ho (fun i => D (e i)) (fun i => M (e i))
    (fun i => hD (e i)) (fun i τ => by rw [hp]; exact hB (e i) τ)
    (fun i => l (e i)) (fun j i => q j (e i)) (fun j i => r j (e i))
    (fun i => hq (e i)) (fun i => hr (e i)) (fun i => hql (e i)) (fun i => hrl (e i))
    (fun i => hM (e i)) (fun i j hj => hm (e i) j hj) σ ((coordinateEquiv e).symm x)
  rw [T.rootWeight_eq_disorder,T.rootWeight_eq_disorder,T.disorderWeight_reindex,
    T.disorderWeight_reindex,ContinuousLinearEquiv.apply_symm_apply] at h
  convert h using 1
  congr 1
  exact (e.sum_comp (fun i => M i*(D i)^2)).symm

 

noncomputable def ClockTree.disorderExpect (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (l : ι → ℝ)
    (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ σ, T.disorderWeight w φ l q σ x*P σ

omit [Nonempty S] in
 theorem ClockTree.disorderExpect_close (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (l : ι → ℝ) (q r : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) {c : ℝ} (x : ι → ℝ)
    (h : ∀ σ, ExpClose c (T.disorderWeight w φ l q σ x) (T.disorderWeight w φ l r σ x)) :
    ExpClose c (T.disorderExpect w φ l q P x) (T.disorderExpect w φ l r P x) := by
  unfold ClockTree.disorderExpect
  apply ExpClose.finset_sum
  intro σ _
  simpa only [add_zero] using (h σ).mul (ExpClose.refl (hP σ))

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators Topology NNReal

 
abbrev OrderedFeatureIndex (n : ℕ) := Sum (Fin n) (Fin n × Fin n)

def orderedFeatureCoefficient (n : ℕ) (σ : Spin n) : OrderedFeatureIndex n → ℝ
  | Sum.inl i => spinValue (σ i)
  | Sum.inr ij => spinValue (σ ij.1)*spinValue (σ ij.2)/Real.sqrt (2*(n:ℝ))

def orderedFeature (n : ℕ) (σ : Spin n) : (OrderedFeatureIndex n → ℝ) →L[ℝ] ℝ :=
  ∑ i, orderedFeatureCoefficient n σ i • ContinuousLinearMap.proj i

@[simp] theorem orderedFeature_apply (n : ℕ) (σ : Spin n) (x : OrderedFeatureIndex n → ℝ) :
    orderedFeature n σ x = ∑ i, orderedFeatureCoefficient n σ i*x i := by
  simp [orderedFeature]

@[simp] theorem orderedFeature_single (n : ℕ) (σ : Spin n) (i : OrderedFeatureIndex n) :
    orderedFeature n σ (Pi.single i 1) = orderedFeatureCoefficient n σ i := by
  classical
  simp [orderedFeature_apply,Pi.single_apply]

def orderedAmplitude (n : ℕ) : OrderedFeatureIndex n → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 1/Real.sqrt (2*(n:ℝ))

theorem orderedAmplitude_nonneg (n : ℕ) (i : OrderedFeatureIndex n) :
    0 ≤ orderedAmplitude n i := by
  cases i <;> simp [orderedAmplitude,Real.sqrt_nonneg]

theorem orderedFeature_abs (n : ℕ) (σ : Spin n) (i : OrderedFeatureIndex n) :
    |orderedFeature n σ (Pi.single i 1)| = orderedAmplitude n i := by
  rw [orderedFeature_single]
  cases i with
  | inl i => simp only [orderedFeatureCoefficient,orderedAmplitude,abs_spinValue]
  | inr ij => simp only [orderedFeatureCoefficient,orderedAmplitude,abs_div,abs_mul,
      abs_spinValue,one_mul,abs_of_nonneg (Real.sqrt_nonneg _)]

theorem orderedFeature_square (n : ℕ) (σ : Spin n) (i : OrderedFeatureIndex n) :
    (orderedFeature n σ (Pi.single i 1))^2 = (orderedAmplitude n i)^2 := by
  rw [← orderedFeature_abs n σ i,sq_abs]

 

def orderedClock (n : ℕ) (b h : ℕ → ℝ) (j : ℕ) : OrderedFeatureIndex n → ℝ
  | Sum.inl _ => h j
  | Sum.inr _ => b j

theorem orderedAmplitude_sum (n : ℕ) (hn : 0 < n) (B H : ℝ) :
    (∑ i : OrderedFeatureIndex n, (Sum.elim (fun _ => H) (fun _ => B) i)*
      (orderedAmplitude n i)^2) = (n:ℝ)*(H+B/2) := by
  have hnp : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hs : Real.sqrt (2*(n:ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hs2 : (Real.sqrt (2*(n:ℝ)))^2 = 2*(n:ℝ) := Real.sq_sqrt (by positivity)
  rw [Fintype.sum_sum_type]
  simp only [orderedAmplitude,Sum.elim_inl,Sum.elim_inr,one_pow,mul_one,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_prod,nsmul_eq_mul,
    Nat.cast_mul,div_pow,one_pow,hs2]
  field_simp

 
def orderedOverlap (n : ℕ) (σ τ : Spin n) : ℝ :=
  (∑ i, spinValue (σ i)*spinValue (τ i))/(n:ℝ)

 theorem orderedCovariance (n : ℕ) (hn : 0 < n) (σ τ : Spin n) (b h : ℝ) :
    (∑ i : OrderedFeatureIndex n, Sum.elim (fun _ => h) (fun _ => b) i*
      orderedFeatureCoefficient n σ i*orderedFeatureCoefficient n τ i) =
      (n:ℝ)*h*orderedOverlap n σ τ+(n:ℝ)*b/2*(orderedOverlap n σ τ)^2 := by
  have hn0 : (n:ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  have hs2 : (Real.sqrt (2*(n:ℝ)))^2 = 2*(n:ℝ) := Real.sq_sqrt (by positivity)
  have he (i j : Fin n) :
      b*(spinValue (σ i)*spinValue (σ j)/Real.sqrt (2*(n:ℝ)))*
        (spinValue (τ i)*spinValue (τ j)/Real.sqrt (2*(n:ℝ))) =
      b/(2*(n:ℝ))*(spinValue (σ i)*spinValue (τ i))*(spinValue (σ j)*spinValue (τ j)) := by
    calc
      _ = b/(Real.sqrt (2*(n:ℝ)))^2*(spinValue (σ i)*spinValue (τ i))*
        (spinValue (σ j)*spinValue (τ j)) := by ring
      _ = _ := by rw [hs2]
  rw [Fintype.sum_sum_type]
  simp only [orderedFeatureCoefficient,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type]
  simp_rw [he]
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul,← Finset.mul_sum]
  have hf : (∑ i, h*spinValue (σ i)*spinValue (τ i)) =
      h*∑ i, spinValue (σ i)*spinValue (τ i) := by simp only [mul_assoc,Finset.mul_sum]
  rw [hf]
  dsimp [orderedOverlap]
  field_simp

end SKFluctuations

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem ExpClose.abs_sub_le {c p q : ℝ} (h : ExpClose c p q) (hc : 0 ≤ c) :
    |p-q| ≤ c*(p+q) := by
  have hp : p-q ≤ c*p := by
    have hq := mul_le_mul_of_nonneg_left h.le_mul (Real.exp_pos (-c)).le
    have he : Real.exp (-c)*Real.exp c = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    rw [← mul_assoc,he,one_mul] at hq
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-c)) h.left_nonneg
    nlinarith
  have hq : q-p ≤ c*q := by
    have hp := mul_le_mul_of_nonneg_left h.rev_le_mul (Real.exp_pos (-c)).le
    have he : Real.exp (-c)*Real.exp c = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    rw [← mul_assoc,he,one_mul] at hp
    have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-c)) h.right_nonneg
    nlinarith
  exact abs_le.mpr ⟨by nlinarith [mul_nonneg hc h.left_nonneg],
    by nlinarith [mul_nonneg hc h.right_nonneg]⟩

variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]
 theorem ClockTree.disorderExpect_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (ho : MassOrdered 0 as) (l : ι → ℝ) (q r : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (K : ℝ) (hP : ∀ σ, |P σ| ≤ K)
    {c : ℝ} (hc : 0 ≤ c) (x : ι → ℝ)
    (h : ∀ σ, ExpClose c (T.disorderWeight w φ l q σ x) (T.disorderWeight w φ l r σ x)) :
    |T.disorderExpect w φ l q P x-T.disorderExpect w φ l r P x| ≤ 2*c*K := by
  unfold ClockTree.disorderExpect
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ, |T.disorderWeight w φ l q σ x*P σ-T.disorderWeight w φ l r σ x*P σ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ, (c*(T.disorderWeight w φ l q σ x+T.disorderWeight w φ l r σ x))*K := by
      apply Finset.sum_le_sum
      intro σ _
      rw [← sub_mul,abs_mul]
      exact mul_le_mul ((h σ).abs_sub_le hc) (hP σ) (abs_nonneg _) (mul_nonneg hc
        (add_nonneg (h σ).left_nonneg (h σ).right_nonneg))
    _ = 2*c*K := by
      rw [← Finset.sum_mul,← Finset.mul_sum,Finset.sum_add_distrib,
        (T.disorderWeight_probability hw φ ho l q x).2,(T.disorderWeight_probability hw φ ho l r x).2]
      ring

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators Topology NNReal

 

def treeComparisonConstant (r : ℕ) : ℝ := 2*(7*(r:ℝ)+8*(r:ℝ)^2*(r+1:ℝ))

theorem treeComparisonConstant_nonneg (r : ℕ) : 0 ≤ treeComparisonConstant r := by
  unfold treeComparisonConstant
  positivity

 

def orderedSKWeight (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n) as)
    (b h : ℕ → ℝ) (σ : T.Assignment) (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  T.disorderWeight (uniformWeight n) (orderedFeature n) 0 (orderedClock n b h) σ x

def orderedSKExpect (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n) as)
    (b h : ℕ → ℝ) (P : T.Assignment → ℝ) (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  T.disorderExpect (uniformWeight n) (orderedFeature n) 0 (orderedClock n b h) P x

 

theorem orderedSKWeight_cumulative_close (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (b h b' h' : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb' : Monotone b') (hh' : Monotone h')
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hdB : ∀ j, j ≤ as.length → |b j-b' j| ≤ B)
    (hdH : ∀ j, j ≤ as.length → |h j-h' j| ≤ H)
    (σ : T.Assignment) (x : OrderedFeatureIndex n → ℝ) :
    ExpClose (treeComparisonConstant T.leaves*(n:ℝ)*(H+B/2))
      (orderedSKWeight n T b h σ x) (orderedSKWeight n T b' h' σ x) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have ha := T.disorderWeight_cumulative_close (uniformWeight_pos n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) (orderedFeature_square n) ho
    (orderedAmplitude n) (Sum.elim (fun _ => H) (fun _ => B))
    (orderedAmplitude_nonneg n) (fun i τ => (orderedFeature_abs n τ i).le)
    0 (orderedClock n b h) (orderedClock n b' h')
    (fun i => by cases i with | inl i => exact hh | inr i => exact hb)
    (fun i => by cases i with | inl i => exact hh' | inr i => exact hb')
    (fun i => by cases i with | inl i => exact hh0 | inr i => exact hb0)
    (fun i => by cases i with | inl i => exact hh0' | inr i => exact hb0')
    (fun i => by cases i with | inl i => exact hH | inr i => exact hB)
    (fun i j hj => by cases i with | inl i => exact hdH j hj | inr i => exact hdB j hj) σ x
  rw [orderedAmplitude_sum n hn B H] at ha
  convert ha using 1 <;> first | rfl | (unfold treeComparisonConstant; ring)

 

theorem orderedSKExpect_cumulative_close (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (b h b' h' : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb' : Monotone b') (hh' : Monotone h')
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hdB : ∀ j, j ≤ as.length → |b j-b' j| ≤ B)
    (hdH : ∀ j, j ≤ as.length → |h j-h' j| ≤ H)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) (x : OrderedFeatureIndex n → ℝ) :
    ExpClose (treeComparisonConstant T.leaves*(n:ℝ)*(H+B/2))
      (orderedSKExpect n T b h P x) (orderedSKExpect n T b' h' P x) := by
  apply T.disorderExpect_close (uniformWeight n) (orderedFeature n) 0
    (orderedClock n b h) (orderedClock n b' h') P hP x
  exact fun σ => orderedSKWeight_cumulative_close n hn T ho b h b' h' hb hh hb' hh'
    hb0 hh0 hb0' hh0' B H hB hH hdB hdH σ x

 

theorem orderedSKExpect_cumulative_abs_le (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (b h b' h' : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb' : Monotone b') (hh' : Monotone h')
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hdB : ∀ j, j ≤ as.length → |b j-b' j| ≤ B)
    (hdH : ∀ j, j ≤ as.length → |h j-h' j| ≤ H)
    (P : T.Assignment → ℝ) (K : ℝ) (hP : ∀ σ, |P σ| ≤ K) (x : OrderedFeatureIndex n → ℝ) :
    |orderedSKExpect n T b h P x-orderedSKExpect n T b' h' P x| ≤
      2*(treeComparisonConstant T.leaves*(n:ℝ)*(H+B/2))*K := by
  have hc : 0 ≤ treeComparisonConstant T.leaves*(n:ℝ)*(H+B/2) :=
    mul_nonneg (mul_nonneg (treeComparisonConstant_nonneg _) (Nat.cast_nonneg _))
      (add_nonneg hH (div_nonneg hB (by norm_num)))
  exact T.disorderExpect_abs_le (uniformWeight_pos n) (orderedFeature n) ho 0
    (orderedClock n b h) (orderedClock n b' h') P K hP hc x
    (fun σ => orderedSKWeight_cumulative_close n hn T ho b h b' h' hb hh hb' hh'
      hb0 hh0 hb0' hh0' B H hB hH hdB hdH σ x)

end SKFluctuations

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S]

 

noncomputable def disorderPressure (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (as : List PositiveMass) (l : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i-l i)))
    (gaussianHierarchy w φ (diagonalBoundarySteps as (q 0) (fun j => q (j+1)))) x-
      (1/2:ℝ)*∑ i, (q as.length i-l i)*C i

 theorem gaussianHierarchy_boundary_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) (l : ι → ℝ) (q : ℕ → ι → ℝ) :
    gaussianHierarchy w (reindexFeature e φ)
      (diagonalBoundarySteps as (fun i => l (e i)) (fun j i => q j (e i))) =
      fun x => gaussianHierarchy w φ (diagonalBoundarySteps as l q) (coordinateEquiv e x) := by
  rw [← clockSteps_cumulative,← clockSteps_cumulative]
  have he : cumulativeIncrements (fun i => l (e i)) (fun j i => q j (e i)) =
      fun j i => cumulativeIncrements l q j (e i) := by
    funext j i
    cases j <;> rfl
  rw [he,gaussianHierarchy_clock_reindex]

 theorem disorderPressure_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ) (as : List PositiveMass)
    (l : ι → ℝ) (q : ℕ → ι → ℝ) (x : κ → ℝ) :
    disorderPressure w (reindexFeature e φ) (fun i => C (e i)) as
      (fun i => l (e i)) (fun j i => q j (e i)) x =
    disorderPressure w φ C as l q (coordinateEquiv e x) := by
  unfold disorderPressure
  rw [gaussianHierarchy_boundary_reindex]
  congr 1
  · unfold zeroContinuation
    simp_rw [map_add]
    exact (coordinateEquiv_measPres e (fun i => Real.toNNReal (q 0 i-l i))).integral_comp
      (coordinateEquiv e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun z => gaussianHierarchy w φ (diagonalBoundarySteps as (q 0) (fun j => q (j+1))) (coordinateEquiv e x+z))
  · congr 1
    exact e.sum_comp (fun i => (q as.length i-l i)*C i)

variable [Nonempty S]

 theorem disorderPressure_eq_corrected {n : ℕ} (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (C : Fin (n+1) → ℝ)
    (as : List PositiveMass) (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    disorderPressure w φ C as l q x = correctedDiagonalRoot w φ C as l q x := rfl

 

 theorem disorderPressure_comparison [DecidableEq ι] [Nonempty ι] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D : ι → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    {l : ι → ℝ} {q r : ℕ → ι → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i) (x : ι → ℝ) :
    |disorderPressure w φ C as l q x-disorderPressure w φ C as l r x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*rootBoundaryCost (as++[⟨1,by norm_num⟩])
        (fun j => q j i) (fun j => r j i) := by
  classical
  let d := Fintype.card ι-1
  have hd : d+1 = Fintype.card ι := Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  let e : Fin (d+1) ≃ ι := (finCongr hd).trans (Fintype.equivFin ι).symm
  have hp (τ : S) (i : Fin (d+1)) : reindexFeature e φ τ (Pi.single i 1) = φ τ (Pi.single (e i) 1) := by
    change φ τ (coordinateEquiv e (Pi.single i 1)) = _
    rw [coordinateEquiv_single]
  have h := correctedDiagonalRoot_comparison hw (reindexFeature e φ) (fun i => C (e i)) (fun i => D (e i))
    (fun τ i => by rw [hp]; exact hC τ (e i)) (fun i τ => by rw [hp]; exact hB (e i) τ)
    as ho hu (fun i => hq (e i)) (fun i => hr (e i)) (fun i => hql (e i)) (fun i => hrl (e i))
    ((coordinateEquiv e).symm x)
  rw [← disorderPressure_eq_corrected,← disorderPressure_eq_corrected,disorderPressure_reindex,
    disorderPressure_reindex,ContinuousLinearEquiv.apply_symm_apply] at h
  apply h.trans_eq
  congr 1
  exact e.sum_comp (fun i => (D i)^2*rootBoundaryCost (as++[⟨1,by norm_num⟩])
    (fun j => q j i) (fun j => r j i))

end SKFluctuations.Hierarchy

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators Topology NNReal

 

noncomputable def orderedSKPressure (n : ℕ) (as : List PositiveMass) (b h : ℕ → ℝ)
    (x : OrderedFeatureIndex n → ℝ) : ℝ :=
  disorderPressure (uniformWeight n) (orderedFeature n) (fun i => (orderedAmplitude n i)^2)
    as 0 (orderedClock n b h) x/(n:ℝ)

 

theorem orderedSKPressure_comparison (n : ℕ) (hn : 0 < n) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    (b h b' h' : ℕ → ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb' : Monotone b') (hh' : Monotone h')
    (hb0 : 0 ≤ b 0) (hh0 : 0 ≤ h 0) (hb0' : 0 ≤ b' 0) (hh0' : 0 ≤ h' 0)
    (x : OrderedFeatureIndex n → ℝ) :
    |orderedSKPressure n as b h x-orderedSKPressure n as b' h' x| ≤
      (1/4:ℝ)*rootBoundaryCost (as++[⟨1,by norm_num⟩]) b b'+
      (1/2:ℝ)*rootBoundaryCost (as++[⟨1,by norm_num⟩]) h h' := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hnp : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hp := disorderPressure_comparison (uniformWeight_pos n) (orderedFeature n)
    (fun i => (orderedAmplitude n i)^2) (orderedAmplitude n) (orderedFeature_square n)
    (fun i σ => (orderedFeature_abs n σ i).le) as ho hu
    (l := 0) (q := orderedClock n b h) (r := orderedClock n b' h')
    (fun i => by cases i with | inl i => exact hh | inr i => exact hb)
    (fun i => by cases i with | inl i => exact hh' | inr i => exact hb')
    (fun i => by cases i with | inl i => exact hh0 | inr i => exact hb0)
    (fun i => by cases i with | inl i => exact hh0' | inr i => exact hb0') x
  have hs : (∑ i : OrderedFeatureIndex n, (orderedAmplitude n i)^2*
      rootBoundaryCost (as++[⟨1,by norm_num⟩])
        (fun j => orderedClock n b h j i) (fun j => orderedClock n b' h' j i)) =
      (n:ℝ)*(rootBoundaryCost (as++[⟨1,by norm_num⟩]) h h'+
        rootBoundaryCost (as++[⟨1,by norm_num⟩]) b b'/2) := by
    calc
      _ = ∑ i : OrderedFeatureIndex n, Sum.elim
          (fun _ => rootBoundaryCost (as++[(⟨1,by norm_num⟩ : PositiveMass)]) h h')
          (fun _ => rootBoundaryCost (as++[(⟨1,by norm_num⟩ : PositiveMass)]) b b') i*
            (orderedAmplitude n i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        cases i <;> exact mul_comm _ _
      _ = _ := orderedAmplitude_sum n hn _ _
  rw [hs] at hp
  unfold orderedSKPressure
  rw [← sub_div,abs_div,abs_of_pos hnp]
  apply (div_le_iff₀ hnp).mpr
  convert hp using 1; first | rfl | ring

end SKFluctuations

end

end OAI
