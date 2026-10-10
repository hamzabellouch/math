import Mathlib
import OAI.Probability.SKFluctuations.ClockPairRepresentation

namespace OAI

/-! Physical Projection. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal BigOperators

 

theorem physicalPair_rooted_law {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    (physicalPathLaw μ n (pre++(mid++tail)) x hx).map
      (fun p => (p.1,actualPairCut pre mid tail (x p.1) p.2)) =
    (actualTwoSegmentLaw μ n tail mid pre x hx).map
      (fun p => (p.1.1,twoSegmentStart n pre mid x p,twoSegmentEnd n pre mid x p)) := by
  have hg : Measurable (fun p : TwoSegmentState P n pre mid =>
      (p.1.1,twoSegmentStart n pre mid x p,twoSegmentEnd n pre mid x p)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((twoSegmentStart_measurable n pre mid hx).prodMk (twoSegmentEnd_measurable n pre mid hx))
  calc
    _ = (μ ⊗ₘ (pairSegmentKernel (uniformWeight n) (finiteFeature n) pre mid tail).comap x hx).map
        (fun p => (p.1,segmentPairField pre mid (x p.1) p.2)) :=
      actualPairCut_rooted_law (uniformWeight_pos n) (finiteFeature n) pre mid tail ha μ x hx
    _ = _ := by
      rw [← actualTwoSegmentLaw_eq_pair μ n tail mid pre ha x hx,
        Measure.map_map hg MeasurableEquiv.prodAssoc.symm.measurable]
      rfl

 

theorem integral_physicalPair_eq_segments {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (F : P × ((FeatureIndex n → ℝ) × (FeatureIndex n → ℝ)) → ℝ) (hF : Measurable F) :
    (∫ p, F (p.1,actualPairCut pre mid tail (x p.1) p.2)
      ∂physicalPathLaw μ n (pre++(mid++tail)) x hx) =
    (∫ p, F (p.1.1,twoSegmentStart n pre mid x p,twoSegmentEnd n pre mid x p)
      ∂actualTwoSegmentLaw μ n tail mid pre x hx) := by
  have hf : Measurable (fun p : PhysicalPathState P n (pre++(mid++tail)) =>
      (p.1,actualPairCut pre mid tail (x p.1) p.2)) :=
    measurable_fst.prodMk ((actualPairCut_measurable_joint pre mid tail).comp
      ((hx.comp measurable_fst).prodMk measurable_snd))
  have hg : Measurable (fun p : TwoSegmentState P n pre mid =>
      (p.1.1,twoSegmentStart n pre mid x p,twoSegmentEnd n pre mid x p)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((twoSegmentStart_measurable n pre mid hx).prodMk (twoSegmentEnd_measurable n pre mid hx))
  rw [← integral_map hf.aemeasurable hF.aestronglyMeasurable,
    physicalPair_rooted_law μ n tail mid pre ha x hx,
    integral_map hg.aemeasurable hF.aestronglyMeasurable]

 

theorem eventually_physical_random_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (tail mid pre : List (GaussianStep (FeatureIndex n)))
      (a D : ℝ), 0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++(mid++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p, |∑ i, V p.1 i * physicalPairIncrement n tail mid pre x p i|^(2*k+2)
      ∂physicalPathLaw μ n (pre++(mid++tail)) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_uniform_actual_random_later_projection k B] with n hn
  intro P _ tail mid pre a D ha0 hD hDB ha μ _ V hV x hx hI hc
  let F : P × ((FeatureIndex n → ℝ) × (FeatureIndex n → ℝ)) → ℝ :=
    fun p => |∑ i, V p.1 i*(actualSpinMean n tail p.2.2 i-
      actualSpinMean n (mid++tail) p.2.1 i)|^(2*k+2)
  have hF : Measurable F := by
    apply Measurable.pow_const
    apply Measurable.abs
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp (hV.comp measurable_fst)).mul
      ((((measurable_pi_apply i).comp (actualSpinMean_measurable n tail
        ((ha.suffix pre _).suffix mid tail))).comp (measurable_snd.comp measurable_snd)).sub
        (((measurable_pi_apply i).comp (actualSpinMean_measurable n (mid++tail)
          (ha.suffix pre _))).comp (measurable_fst.comp measurable_snd)))
  change (∫ p, F (p.1,actualPairCut pre mid tail (x p.1) p.2)
      ∂physicalPathLaw μ n (pre++(mid++tail)) x hx) ≤ _
  rw [integral_physicalPair_eq_segments μ n tail mid pre ha x hx F hF]
  exact hn P tail mid pre a D ha0 hD hDB ha μ V hV x hx hI hc

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalPathLaw_finite {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    IsFiniteMeasure (physicalPathLaw μ n steps x hx) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  unfold physicalPathLaw
  infer_instance

theorem physicalPairIncrement_moment_integrable {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Integrable (fun p => (projectionEuclideanNorm n (physicalPairIncrement n tail mid pre x p))^(2*k+2))
      (physicalPathLaw μ n (pre++(mid++tail)) x hx) := by
  have := physicalPathLaw_finite μ n (pre++(mid++tail)) ha x hx
  have hm : Measurable (fun p : PhysicalPathState P n (pre++(mid++tail)) =>
      actualPairCut pre mid tail (x p.1) p.2) :=
    (actualPairCut_measurable_joint pre mid tail).comp ((hx.comp measurable_fst).prodMk measurable_snd)
  exact actualSpinMean_sub_moment_integrable _ n k tail (mid++tail)
    ((ha.suffix pre _).suffix mid tail) (ha.suffix pre _) _ _ hm.snd hm.fst

theorem norm_physicalPairIncrement {P : Type} (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) (x : P → FeatureIndex n → ℝ)
    (p : PhysicalPathState P n (pre++(mid++tail))) :
    projectionEuclideanNorm n (physicalPairIncrement n tail mid pre x p) =
      ‖actualSpinPath n (pre++(mid++tail)) x (pre.length+mid.length) p -
        actualSpinPath n (pre++(mid++tail)) x pre.length p‖ := by
  rw [← physicalPairIncrement_eq_spinPath,EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  rfl

 

def physicalForkPathLaw {P : Type} [MeasurableSpace P]
    (μ : Measure P) (n : ℕ) (bsteps asteps : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :=
  physicalPathLaw (physicalPathLaw μ n bsteps x hx) n asteps
    (fun p : PhysicalPathState P n bsteps => x p.1) (hx.comp measurable_fst)

 

theorem eventually_physical_fork_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (btail bmid bpre atail amid apre : List (GaussianStep (FeatureIndex n)))
      (a ab D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (apre++(amid++atail)) → OrderedSteps ab (bpre++(bmid++btail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (d : Fin apre.length → ℝ), (∀ j, 0 ≤ d j) → (∑ j, d j = D) →
      (∀ j i, (hierarchyClocks apre j (Sum.inl i) : ℝ) = d j) →
    (∫ p, |∑ i, physicalPairIncrement n btail bmid bpre x p.1 i *
      physicalPairIncrement n atail amid apre
        (fun s : PhysicalPathState P n (bpre++(bmid++btail)) => x s.1) p i|^(2*k+2)
      ∂physicalForkPathLaw μ n (bpre++(bmid++btail)) (apre++(amid++atail)) x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (physicalPairIncrement n btail bmid bpre x p))^(2*k+2)
          ∂physicalPathLaw μ n (bpre++(bmid++btail)) x hx := by
  filter_upwards [eventually_physical_random_projection k B] with n hn
  intro P _ btail bmid bpre atail amid apre a ab D ha0 hD hDB ha hb μ _ x hx d hd hdD hc
  have := physicalPathLaw_finite μ n (bpre++(bmid++btail)) hb x hx
  exact hn (PhysicalPathState P n (bpre++(bmid++btail))) atail amid apre a D ha0 hD hDB ha
    (physicalPathLaw μ n (bpre++(bmid++btail)) x hx) (physicalPairIncrement n btail bmid bpre x)
    (physicalPairIncrement_measurable n btail bmid bpre hb hx)
    (fun p : PhysicalPathState P n (bpre++(bmid++btail)) => x p.1) (hx.comp measurable_fst)
    (physicalPairIncrement_moment_integrable μ n k btail bmid bpre hb x hx)
    (fun _ => alignedFieldClock_of_physical n apre d hd D hdD hc _)

end SKFluctuations

 

namespace SKFluctuations.Hierarchy.ReplicaTree
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

theorem expect_atSlot {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)}
    (T : ReplicaTree ι S steps) {a : ℝ} (ha : OrderedSteps a steps)
    (s : T.Slot) (P : S → ℝ) (x : ι → ℝ) :
    T.expect w φ (fun σ => P (T.atSlot σ s)) x = gaussianHierarchyMean w φ P steps x := by
  induction T generalizing a x with
  | leaf => rfl
  | step st T ih =>
    rcases st with ⟨m,q⟩
    rw [expect_step hw φ T m q ha.2.2.2]
    have he : (fun y => T.expect w φ (fun σ => P (T.atSlot σ s)) y) =
        gaussianHierarchyMean w φ P _ := funext (ih ha.2.2.2 s)
    change shiftedMean _ m _ (fun y => T.expect w φ (fun σ => P (T.atSlot σ s)) y) x = _
    rw [he]
    rfl
  | fork T V ihT ihV =>
    cases s with
    | inl s =>
      change (T.fork V).expect w φ (fun σ => P (T.atSlot σ.1 s)) x = _
      rw [expect_fork]
      simp_rw [expect_const hw φ V ha]
      exact ihT ha s x
    | inr s =>
      change (T.fork V).expect w φ (fun σ => P (V.atSlot σ.2 s)) x = _
      rw [expect_fork]
      simp_rw [ihV ha s]
      exact expect_const hw φ T ha _ x

end SKFluctuations.Hierarchy.ReplicaTree
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal BigOperators

 

def scalarCavityRow (cs : List HeatClock) (T : ReplicaTree (Fin 1) Bool (heatSteps cs))
    (a : ℝ) (s : T.Slot) (x : ℝ) : ℝ :=
  T.row (fun _ => (1/2:ℝ)) scalarFeature a
    (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1))
    (fun σ => scalarFeature σ (fun _ => 1)) (fun _ => x)

theorem scalarSourceJet_one_mean {steps : List (GaussianStep (Fin 1))}
    (ho : OrderedSteps 0 steps) (x : ℝ) :
    scalarSourceJet steps 1 x = gaussianHierarchyMean (fun _ : Bool => (1/2:ℝ))
      scalarFeature (fun σ => scalarFeature σ (fun _ => 1)) steps (fun _ => x) := by
  change (ReplicaTree.single steps).expect (fun _ => (1/2:ℝ)) scalarFeature
    (fun σ => scalarFeature (ReplicaTree.singleEquiv (S:=Bool) steps σ) (fun _ => 1)) (fun _ => x) = _
  exact ReplicaTree.single_expect (by intro σ; norm_num : ∀ σ : Bool, (0:ℝ)<1/2) scalarFeature steps ho (fun σ => scalarFeature σ (fun _ => 1)) (fun _ => x)

 
theorem scalarCavityRow_eq (cs : List HeatClock)
    (T : ReplicaTree (Fin 1) Bool (heatSteps cs)) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) (s : T.Slot) (x : ℝ) :
    scalarCavityRow cs T a s x = scalarSourceJet (heatSteps cs) 2 x+
      a*(scalarSourceJet (heatSteps cs) 1 x)^2 := by
  have ho0 := ho.lower le_rfl ho.nonneg
  have hd := T.hasDerivAt_expect (by intro σ; norm_num : ∀ σ : Bool, (0:ℝ)<1/2)
    scalarFeature (fun _ => 1) ho (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1)) 0 x
  have he (y : ℝ) : (0 : Fin 1 → ℝ)+y • (fun _ => (1:ℝ)) = (fun _ => y) := by ext i; simp
  simp_rw [he] at hd
  have hm (y : ℝ) : T.expect (fun _ : Bool => (1/2:ℝ)) scalarFeature
      (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1)) (fun _ => y) =
      scalarSourceJet (heatSteps cs) 1 y := by
    exact (T.expect_atSlot (by intro σ; norm_num : ∀ σ : Bool, (0:ℝ)<1/2) scalarFeature ho
      s (fun σ => scalarFeature σ (fun _ => 1)) (fun _ => y)).trans (scalarSourceJet_one_mean ho0 y).symm
  simp_rw [hm,← scalarSourceJet_one_mean ho0] at hd
  have hh := hd.unique (scalarSourceJet_hasDerivAt ho0 1 x)
  change scalarCavityRow cs T a s x-a*scalarSourceJet (heatSteps cs) 1 x*
    scalarSourceJet (heatSteps cs) 1 x = scalarSourceJet (heatSteps cs) 2 x at hh
  nlinarith

 

theorem scalarCavityRow_zero (cs : List HeatClock)
    (T : ReplicaTree (Fin 1) Bool (heatSteps cs)) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) (s : T.Slot) :
    scalarCavityRow cs T a s 0 = (scalarTerminal.schedule cs).H 0 0 := by
  rw [scalarCavityRow_eq cs T ho s,scalarSourceJet_schedule_gradient_zero cs (ho.lower le_rfl ho.nonneg)]
  simpa only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero,Pi.zero_def] using
    scalarSourceJet_two_schedule cs (ho.lower le_rfl ho.nonneg) 0

 
theorem scalarCavityRow_zero_bounds (cs : List HeatClock)
    (T : ReplicaTree (Fin 1) Bool (heatSteps cs)) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) (s : T.Slot) :
    Real.exp (-4*(cs.map (fun c => (c.time:ℝ))).sum) ≤ scalarCavityRow cs T a s 0 ∧
      scalarCavityRow cs T a s 0 ≤ 1 := by
  have ho0 := ho.lower le_rfl ho.nonneg
  rw [scalarCavityRow_zero cs T ho s]
  constructor
  · have hl := scalar_schedule_curvature_lower cs
      (fun c hc => (scalar_schedule_ordered_masses ho0 c hc).2) (0 : Fin 1 → ℝ)
    simpa [Scalar.curvature] using hl
  · change (scalarTerminal.schedule cs).H 0 (fun _ => 0) ≤ 1
    rw [← scalarSourceJet_two_schedule cs ho0 0]
    exact scalarSourceJet_schedule_curvature_le_one cs ho0 0

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

def ClockTree.weightVariation {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {l r : ℝ} :
    {as : List PositiveMass} → (T : ClockTree S as) →
    (q d : ℕ → Fin (n+1) → ℝ) →
    (hpos : ∀ j t, t ∈ Ioo l r → ∀ i, 0 < q j i+t*d j i) → (σ : T.Assignment) →
    JetVariation (T.weightFamily hw φ (fun j t i => q j i+t*d j i)
      (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) σ) l r
  | _, .leaf, _, _, _, σ => (spinWeightJet hw φ σ).constantVariation
  | _, .step a T, q, d, hp, σ =>
    (T.weightVariation hw φ (fun j => q (j+1)) (fun j => d (j+1)) (fun j => hp (j+1)) σ).varianceEvolve
      a.property (q 0) (d 0) (hp 0)
  | _, .fork T U, q, d, hp, σ =>
    (T.weightVariation hw φ q d hp σ.1).productTest (U.weightVariation hw φ q d hp σ.2)

theorem ClockTree.hasDerivAt_weight_fullPath {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j t, t ∈ Ioo l r → ∀ i, 0 < q j i+t*d j i)
    (σ : T.Assignment) {t : ℝ} (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.weight w φ (fun j i => Real.toNNReal (q j i+s*d j i)) σ x)
      ((T.weightVariation hw φ q d hp σ).B t x) t := by
  have h := (T.weightVariation hw φ q d hp σ).derivA t ht x
  have he (s : ℝ) := (T.weightFamily_actual hw φ (fun j s i => q j i+s*d j i)
    (fun _ => continuous_pi fun _ => continuous_const.add (continuous_id.mul continuous_const)) σ s).2
  simpa only [he] using h

 

theorem ClockTree.hasDerivAt_expect_fullPath {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ j t, t ∈ Ioo l r → ∀ i, 0 < q j i+t*d j i)
    (P : T.Assignment → ℝ) {t : ℝ} (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt (fun s => T.expect w φ (fun j i => Real.toNNReal (q j i+s*d j i)) P x)
      (∑ σ, (T.weightVariation hw φ q d hp σ).B t x*P σ) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) fun σ _ => (T.hasDerivAt_weight_fullPath hw φ q d hp σ ht x).mul_const (P σ)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem continuous_monotoneProfileIntegral (M : ℝ → ℝ) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (l : ℝ) (t : ℝ≥0) :
    Continuous (fun α : boundedMassProfiles => ∫ s in l..l+(t:ℝ), M (α.val s)) := by
  have hmono (α : boundedMassProfiles) : Monotone (fun s => M (α.val s)) := by
    intro s u hsu
    exact hm (α.property.1 s) (α.property.1 u) (α.property.2 hsu)
  have he (α : boundedMassProfiles) (k : ℕ) :
      |(∫ s in l..l+(t:ℝ), M (α.val s))-dyadicLowerSum (fun s => M (α.val s)) l t k| ≤
        (t:ℝ)*(M 1-M 0)*(1/2:ℝ)^k := by
    apply (dyadicLowerSum_integral_error (hmono α) l t k).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ t.coe_nonneg
    exact sub_le_sub (hm (α.property.1 _) (by norm_num) (α.property.1 _).2)
      (hm (by norm_num) (α.property.1 _) (α.property.1 _).1)
  have ht : TendstoUniformly
      (fun k (α : boundedMassProfiles) => dyadicLowerSum (fun s => M (α.val s)) l t k)
      (fun α => ∫ s in l..l+(t:ℝ), M (α.val s)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    have hp : Tendsto (fun k : ℕ => (t:ℝ)*(M 1-M 0)*(1/2:ℝ)^k) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)).const_mul ((t:ℝ)*(M 1-M 0))
    filter_upwards [hp.eventually (gt_mem_nhds hε)] with k hk
    intro α
    rw [Real.dist_eq]
    exact (he α k).trans_lt hk
  apply ht.continuous
  apply Eventually.frequently
  apply Eventually.of_forall
  intro k
  exact dyadicLowerSum_continuous _ (fun s => hM.comp ((continuous_apply s).comp continuous_subtype_val)) l t k

 theorem continuous_monotoneProfileIntegral_between (M : ℝ → ℝ) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) {l r : ℝ} (hlr : l≤r) :
    Continuous (fun α : boundedMassProfiles => ∫ s in l..r, M (α.val s)) := by
  have hc := continuous_monotoneProfileIntegral M hM hm l ⟨r-l, sub_nonneg.mpr hlr⟩
  change Continuous (fun α : boundedMassProfiles => ∫ s in l..l+(r-l), M (α.val s)) at hc
  have he : l+(r-l)=r := by ring
  rw [he] at hc
  exact hc

 def inverseIntegralConstraints (r₀ u₀ : ℝ) (k M : ℝ → ℝ) : Set boundedMassProfiles :=
  {α | α.val r₀=u₀ ∧ α.val 1=1 ∧ ∀ x ∈ Icc r₀ 1, ∀ y ∈ Icc r₀ 1, x≤y →
    (∫ t in x..y, k t) ≤ α.val y-α.val x ∧
      α.val y-α.val x ≤ ∫ t in x..y, M (α.val t)}

 theorem inverseIntegralConstraints_closed (r₀ u₀ : ℝ) (k M : ℝ → ℝ)
    (hM : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1)) :
    IsClosed (inverseIntegralConstraints r₀ u₀ k M) := by
  have heval (s : ℝ) : Continuous (fun α : boundedMassProfiles => α.val s) :=
    (continuous_apply s).comp continuous_subtype_val
  change IsClosed ({α : boundedMassProfiles | α.val r₀=u₀} ∩
    ({α : boundedMassProfiles | α.val 1=1} ∩ {α | ∀ x ∈ Icc r₀ 1, ∀ y ∈ Icc r₀ 1, x≤y →
    (∫ t in x..y, k t) ≤ α.val y-α.val x ∧ α.val y-α.val x ≤ ∫ t in x..y, M (α.val t)}))
  refine (isClosed_eq (heval _) continuous_const).inter ((isClosed_eq (heval _) continuous_const).inter ?_)
  simp only [ofPred_forall]
  refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun y =>
    isClosed_iInter fun _ => isClosed_iInter fun hxy => ?_
  exact (isClosed_le continuous_const ((heval y).sub (heval x))).inter
    (isClosed_le ((heval y).sub (heval x)) (continuous_monotoneProfileIntegral_between M hM hm hxy))

 theorem inverseIntegralConstraints_compact (r₀ u₀ : ℝ) (k M : ℝ → ℝ)
    (hM : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1)) :
    IsCompact (inverseIntegralConstraints r₀ u₀ k M) := by
  let : CompactSpace boundedMassProfiles := isCompact_iff_compactSpace.mp boundedMassProfiles_compact
  exact (inverseIntegralConstraints_closed r₀ u₀ k M hM hm).isCompact

 theorem inverseIntegralConstraints_lipschitz {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    {α : boundedMassProfiles} (hα : α ∈ inverseIntegralConstraints r₀ u₀ k M) :
    LipschitzOnWith ⟨M 1,hM⟩ α.val (Icc r₀ 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change |α.val x-α.val y| ≤ M 1*|x-y|
  have bound {s t : ℝ} (hs : s ∈ Icc r₀ 1) (ht : t ∈ Icc r₀ 1) (hst : s≤t) :
      α.val t-α.val s ≤ M 1*(t-s) := by
    apply (hα.2.2 s hs t ht hst).2.trans
    calc
      (∫ u in s..t, M (α.val u)) ≤ ∫ u in s..t, M 1 := by
        apply intervalIntegral.integral_mono_on hst
        · exact (show Monotone (fun u => M (α.val u)) from fun u v huv =>
            hm (α.property.1 u) (α.property.1 v) (α.property.2 huv)).intervalIntegrable
        · exact intervalIntegrable_const
        · intro u _
          exact hm (α.property.1 u) (by norm_num) (α.property.1 u).2
      _ = M 1*(t-s) := by simp [mul_comm]
  rcases le_total x y with hxy | hyx
  · simpa only [NNReal.coe_mk,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (α.property.2 hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using bound hx hy hxy
  · simpa only [NNReal.coe_mk,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (α.property.2 hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)] using bound hy hx hyx

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 theorem lipschitz_ae_deriv_lower_iff {a b : ℝ} (hab : a≤b) {f g : ℝ → ℝ}
    {C : ℝ≥0} (hf : LipschitzOnWith C f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∀ᵐ x, x ∈ Icc a b → g x≤deriv f x) ↔
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x≤y → (∫ t in x..y, g t)≤f y-f x := by
  have hgint {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x≤y) :
      IntervalIntegrable g volume x y :=
    (hg.mono (Icc_subset_Icc hx.1 hy.2)).intervalIntegrable_of_Icc hxy
  have hac {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x≤y) :
      AbsolutelyContinuousOnInterval f x y := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    rw [uIcc_of_le hxy]
    exact hf.mono (Icc_subset_Icc hx.1 hy.2)
  constructor
  · intro h x hx y hy hxy
    rw [← (hac hx hy hxy).integral_deriv_eq_sub]
    apply intervalIntegral.integral_mono_ae_restrict hxy (hgint hx hy hxy)
      (hac hx hy hxy).intervalIntegrable_deriv
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [h] with z hz hzx
    exact hz ⟨hx.1.trans hzx.1,hzx.2.trans hy.2⟩
  · intro h
    have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
    have hb : b ∈ Icc a b := ⟨hab,le_rfl⟩
    have hm : MonotoneOn (fun x => f x-∫ t in a..x, g t) (Icc a b) := by
      intro x hx y hy hxy
      have hi := intervalIntegral.integral_add_adjacent_intervals
        (hgint ha hx hx.1) (hgint hx hy hxy)
      have hh := h x hx y hy hxy
      dsimp
      linarith
    filter_upwards [(hac ha hb hab).ae_differentiableAt,volume.ae_ne a,volume.ae_ne b]
      with x hdiff hxa hxb hx
    have hxi : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa),lt_of_le_of_ne hx.2 hxb⟩
    have hxn : Icc a b ∈ 𝓝 x := Icc_mem_nhds hxi.1 hxi.2
    have hdx : DifferentiableAt ℝ f x := hdiff (by simpa only [uIcc_of_le hab] using hx)
    have hdg : HasDerivAt (fun u => ∫ t in a..u, g t) (g x) x :=
      intervalIntegral.integral_hasDerivAt_right (hgint ha hx hx.1)
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg.mono Ioo_subset_Icc_self) x hxi)
        ((hg x hx).continuousAt hxn)
    have hn : 0≤derivWithin (fun u => f u-∫ t in a..u, g t) (Icc a b) x :=
      hm.derivWithin_nonneg
    rw [derivWithin_of_mem_nhds hxn] at hn
    have he : deriv (fun u => f u-∫ t in a..u, g t) x=deriv f x-g x :=
      (hdx.hasDerivAt.sub hdg).deriv
    rw [he] at hn
    linarith

 theorem lipschitz_ae_deriv_upper_iff {a b : ℝ} (hab : a≤b) {f g : ℝ → ℝ}
    {C : ℝ≥0} (hf : LipschitzOnWith C f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∀ᵐ x, x ∈ Icc a b → deriv f x≤g x) ↔
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x≤y → f y-f x≤∫ t in x..y, g t := by
  have he := lipschitz_ae_deriv_lower_iff hab hf.neg hg.neg
  constructor
  · intro h
    have ha := he.mp (by
      filter_upwards [h] with x hx hxi
      simpa only [Pi.neg_apply,deriv.neg,neg_le_neg_iff] using hx hxi)
    intro x hx y hy hxy
    have hb := ha x hx y hy hxy
    simp only [Pi.neg_apply,intervalIntegral.integral_neg] at hb
    linarith
  · intro h
    have ha := he.mpr (by
      intro x hx y hy hxy
      have hb := h x hx y hy hxy
      simp only [Pi.neg_apply,intervalIntegral.integral_neg]
      linarith)
    filter_upwards [ha] with x hx hxi
    simpa only [Pi.neg_apply,deriv.neg,neg_le_neg_iff] using hx hxi

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def inverseDifferentialConstraints (r₀ u₀ : ℝ) (k M : ℝ → ℝ) : Set boundedMassProfiles :=
  {α | α.val r₀=u₀ ∧ α.val 1=1 ∧ ∃ C : ℝ≥0,
    LipschitzOnWith C α.val (Icc r₀ 1) ∧
    ∀ᵐ t, t ∈ Icc r₀ 1 → k t≤deriv α.val t ∧ deriv α.val t≤M (α.val t)}

 theorem inverseDifferentialConstraints_eq (r₀ u₀ : ℝ) (hr : r₀≤1) (k M : ℝ → ℝ)
    (hk : ContinuousOn k (Icc r₀ 1)) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM1 : 0≤M 1) :
    inverseDifferentialConstraints r₀ u₀ k M=inverseIntegralConstraints r₀ u₀ k M := by
  ext α
  constructor
  · rintro ⟨hα₀,hα₁,C,hC,hae⟩
    refine ⟨hα₀,hα₁,?_⟩
    have hl := (lipschitz_ae_deriv_lower_iff hr hC hk).mp
      (hae.mono fun t ht hti => (ht hti).1)
    have hu := (lipschitz_ae_deriv_upper_iff hr hC (hM.comp_continuousOn hC.continuousOn)).mp
      (hae.mono fun t ht hti => (ht hti).2)
    exact fun x hx y hy hxy => ⟨hl x hx y hy hxy,hu x hx y hy hxy⟩
  · intro hα
    have hC := inverseIntegralConstraints_lipschitz hm hM1 hα
    refine ⟨hα.1,hα.2.1,⟨M 1,hM1⟩,hC,?_⟩
    have hl := (lipschitz_ae_deriv_lower_iff hr hC hk).mpr
      (fun x hx y hy hxy => (hα.2.2 x hx y hy hxy).1)
    have hu := (lipschitz_ae_deriv_upper_iff hr hC (hM.comp_continuousOn hC.continuousOn)).mpr
      (fun x hx y hy hxy => (hα.2.2 x hx y hy hxy).2)
    filter_upwards [hl,hu] with t ht₁ ht₂ hti
    exact ⟨ht₁ hti,ht₂ hti⟩

 theorem inverseDifferentialConstraints_compact (r₀ u₀ : ℝ) (hr : r₀≤1) (k M : ℝ → ℝ)
    (hk : ContinuousOn k (Icc r₀ 1)) (hM : Continuous M)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM1 : 0≤M 1) :
    IsCompact (inverseDifferentialConstraints r₀ u₀ k M) := by
  rw [inverseDifferentialConstraints_eq r₀ u₀ hr k M hk hM hm hM1]
  exact inverseIntegralConstraints_compact r₀ u₀ k M hM hm

  

 def comparisonFloor (N δ U r : ℝ) : ℝ := N^δ*U^2/(r+N^(2*δ)*U)^2
 def comparisonCap (N δ U L E d u : ℝ) : ℝ :=
   N^δ*((u+U)/L+(d^3/E)*(u+U)^2)
 def comparisonLowerScale (N E d : ℝ) : ℝ := Real.sqrt N*E/d
 def comparisonSmallMass (N E : ℝ) : ℝ := 1/(N*E)
 def comparisonConstraintLength (N E d : ℝ) : ℝ :=
   min (comparisonSmallMass N E) ((comparisonLowerScale N E d)^3/d^2)

 theorem comparisonCap_continuous (N δ U L E d : ℝ) :
    Continuous (comparisonCap N δ U L E d) := by
  unfold comparisonCap
  fun_prop

 theorem comparisonCap_monotoneOn {N δ U L E d : ℝ} (hN : 0<N) (hU : 0≤U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) :
    MonotoneOn (comparisonCap N δ U L E d) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  unfold comparisonCap
  gcongr
  linarith [hu.1]

 theorem comparisonCap_nonneg {N δ U L E d u : ℝ} (hN : 0<N) (hU : 0≤U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hu : 0≤u) :
    0≤comparisonCap N δ U L E d u := by
  unfold comparisonCap
  positivity

 theorem comparisonFloor_pos {N δ U r : ℝ} (hN : 0<N) (hU : 0<U) (hr : 0≤r) :
    0<comparisonFloor N δ U r := by
  unfold comparisonFloor
  have hq : 0<N^(2*δ) := Real.rpow_pos_of_pos hN _
  positivity

 theorem comparisonFloor_continuousOn {N δ U r₀ : ℝ} (hN : 0<N) (hU : 0<U)
    (hr : 0≤r₀) : ContinuousOn (comparisonFloor N δ U) (Icc r₀ 1) := by
  intro r hrmem
  unfold comparisonFloor
  have hp : 0<r+N^(2*δ)*U := add_pos_of_nonneg_of_pos (hr.trans hrmem.1)
    (mul_pos (Real.rpow_pos_of_pos hN _) hU)
  fun_prop (disch := positivity)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal

 def inverseRestriction {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M) : C(Icc r₀ 1,ℝ) :=
  ⟨fun t => α.val.val t,
    (inverseIntegralConstraints_lipschitz hm hM α.property).continuousOn.domRestrict⟩

 theorem inverseRestriction_continuous {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1) :
    Continuous (inverseRestriction (r₀:=r₀) (u₀:=u₀) (k:=k) hm hM) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc₁ : Continuous (fun q : inverseIntegralConstraints r₀ u₀ k M × Icc r₀ 1 =>
      M 1*dist q.2 p.2) := continuous_const.mul (continuous_snd.dist continuous_const)
  have hce : Continuous (fun q : inverseIntegralConstraints r₀ u₀ k M × Icc r₀ 1 =>
      q.1.val.val p.2) :=
    (continuous_apply p.2.val).comp (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
  have hc₂ := hce.dist (continuous_const (y:=p.1.val.val p.2))
  have hlim : Tendsto (fun q : inverseIntegralConstraints r₀ u₀ k M × Icc r₀ 1 =>
      M 1*dist q.2 p.2+dist (q.1.val.val p.2) (p.1.val.val p.2)) (𝓝 p) (𝓝 0) := by
    simpa only [dist_self,mul_zero,add_zero] using ((hc₁.tendsto p).add (hc₂.tendsto p))
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hlim
  apply Eventually.of_forall
  intro q
  apply (dist_triangle (q.1.val.val q.2) (q.1.val.val p.2) (p.1.val.val p.2)).trans
  exact add_le_add
    ((inverseIntegralConstraints_lipschitz hm hM q.1.property).dist_le_mul
      q.2 q.2.property p.2 p.2.property) le_rfl

 theorem inverseRestriction_compact {r₀ u₀ : ℝ} {k M : ℝ → ℝ}
    (hMc : Continuous M) (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1) :
    IsCompact (range (inverseRestriction (r₀:=r₀) (u₀:=u₀) (k:=k) hm hM)) := by
  let : CompactSpace (inverseIntegralConstraints r₀ u₀ k M) :=
    isCompact_iff_compactSpace.mp (inverseIntegralConstraints_compact r₀ u₀ k M hMc hm)
  exact isCompact_range (inverseRestriction_continuous hm hM)

end SKFluctuations.Hierarchy

end

end OAI
