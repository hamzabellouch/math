import Mathlib
import OAI.Probability.SKFluctuations.ActualSpinMartingale

namespace OAI

/-! Uniform Actual Later Projection. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_uniform_actual_random_later_projection
    (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P], ∀ (tail mid pre : List (GaussianStep (FeatureIndex n)))
      (a D : ℝ), 0 < a → 0 < D → D ≤ B → OrderedSteps a (pre++(mid++tail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (V : P → Fin n → ℝ) (_hV : Measurable V)
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x),
      Integrable (fun p => (projectionEuclideanNorm n (V p))^(2*k+2)) μ →
      (∀ p, AlignedFieldClock (fieldProjectionDirection n (V p)) D pre) →
    (∫ p : (P × (Fin pre.length → FeatureIndex n → ℝ)) × (Fin mid.length → FeatureIndex n → ℝ),
       |∑ i, V p.1.1 i *
          (actualSpinMean n tail (forwardEnd mid.length (hierarchyIncrements mid)
            (forwardEnd pre.length (hierarchyIncrements pre) (x p.1.1) p.1.2) p.2) i -
           actualSpinMean n (mid++tail)
            (forwardEnd pre.length (hierarchyIncrements pre) (x p.1.1) p.1.2) i)|^(2*k+2)
        ∂actualTwoSegmentLaw μ n tail mid pre x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (V p))^(2*k+2) ∂μ := by
  filter_upwards [eventually_uniform_random_projection_moment k B] with n hn
  intro P _ tail mid pre a D ha0 hD hDB ha μ _ V hV x hx hI hc
  have hmid := ha.suffix pre (mid++tail)
  have htail := hmid.suffix mid tail
  have hmark₁ := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) (mid++tail) pre ha
  have hmark₂ := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) tail mid hmid
  let κ₁ := (segmentKernel (uniformWeight n) (finiteFeature n) (mid++tail) pre).comap x hx
  let x₁ : P × (Fin pre.length → FeatureIndex n → ℝ) → FeatureIndex n → ℝ :=
    fun p => forwardEnd pre.length (hierarchyIncrements pre) (x p.1) p.2
  have hx₁ : Measurable x₁ := (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
    ((hx.comp measurable_fst).prodMk measurable_snd)
  let κ₂ := (segmentKernel (uniformWeight n) (finiteFeature n) tail mid).comap x₁ hx₁
  let μ₁ := μ ⊗ₘ κ₁
  let μ₂ := μ₁ ⊗ₘ κ₂
  have hp₁ : MeasurePreserving (Prod.fst : P × (Fin pre.length → FeatureIndex n → ℝ) → P) μ₁ μ :=
    ⟨measurable_fst, Measure.fst_compProd μ κ₁⟩
  have hp₂ : MeasurePreserving (Prod.fst : (P × (Fin pre.length → FeatureIndex n → ℝ)) ×
      (Fin mid.length → FeatureIndex n → ℝ) → P × (Fin pre.length → FeatureIndex n → ℝ)) μ₂ μ₁ :=
    ⟨measurable_fst, Measure.fst_compProd μ₁ κ₂⟩
  have hI₁ : Integrable (fun p : P × (Fin pre.length → FeatureIndex n → ℝ) =>
      (projectionEuclideanNorm n (V p.1))^(2*k+2)) μ₁ :=
    (hp₁.integrable_comp (((projectionEuclideanNorm_measurable n).comp hV).pow_const _).aestronglyMeasurable).mpr hI
  have hI₂ : Integrable (fun p : (P × (Fin pre.length → FeatureIndex n → ℝ)) ×
      (Fin mid.length → FeatureIndex n → ℝ) => (projectionEuclideanNorm n (V p.1.1))^(2*k+2)) μ₂ :=
    (hp₂.integrable_comp ((((projectionEuclideanNorm_measurable n).comp hV).comp measurable_fst).pow_const _).aestronglyMeasurable).mpr hI₁
  have hx₂ : Measurable (fun p : (P × (Fin pre.length → FeatureIndex n → ℝ)) ×
      (Fin mid.length → FeatureIndex n → ℝ) =>
        forwardEnd mid.length (hierarchyIncrements mid) (x₁ p.1) p.2) :=
    (measurable_forwardEnd _ (hierarchyIncrements_measurable mid)).comp
      ((hx₁.comp measurable_fst).prodMk measurable_snd)
  have hi := random_directional_increment_integrable μ₂ n k tail (mid++tail) htail hmid
    (fun p => V p.1.1) (hV.comp (measurable_fst.comp measurable_fst))
    (fun p => forwardEnd mid.length (hierarchyIncrements mid) (x₁ p.1) p.2)
    (fun p => x₁ p.1) hx₂ (hx₁.comp measurable_fst) hI₂
  simp_rw [mul_sub, Finset.sum_sub_distrib,spinProjection_actualSpinMean n _ tail htail,
    spinProjection_actualSpinMean n _ (mid++tail) hmid]
  change (∫ p, |gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1.1))
    tail (forwardEnd mid.length (hierarchyIncrements mid) (x₁ p.1) p.2) -
    gaussianHierarchyMean (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1.1))
      (mid++tail) (x₁ p.1)|^(2*k+2) ∂μ₂) ≤ _
  rw [Measure.integral_compProd hi]
  have hcent := random_projection_moment_integrable μ n k (mid++tail) pre ha V hV x hx hI
  calc
    _ ≤ ∫ p, hierarchyCenteredEvenMoment (uniformWeight n) (finiteFeature n) (spinProjection n (V p.1))
        (mid++tail) k (x₁ p) ∂μ₁ := by
      apply integral_mono (hi.integral_compProd) hcent
      intro p
      change (∫ q, _ ∂segmentKernel (uniformWeight n) (finiteFeature n) tail mid (x₁ p)) ≤ _
      rw [segmentKernel_apply (uniformWeight_pos n) (finiteFeature n) tail mid hmid]
      exact integral_segmentLaw_laterProjection_le (uniformWeight_pos n) (finiteFeature n)
        (spinProjection n (V p.1)) tail mid hmid k (x₁ p)
    _ ≤ _ := hn P (mid++tail) pre a D ha0 hD hDB ha μ V hV x hx hI hc

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Hierarchy
open scoped Topology NNReal ENNReal BigOperators

abbrev TwoSegmentState (P : Type) (n : ℕ)
    (pre mid : List (GaussianStep (FeatureIndex n))) :=
  (P × (Fin pre.length → FeatureIndex n → ℝ)) × (Fin mid.length → FeatureIndex n → ℝ)

def twoSegmentStart {P : Type} (n : ℕ) (pre mid : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (p : TwoSegmentState P n pre mid) : FeatureIndex n → ℝ :=
  forwardEnd pre.length (hierarchyIncrements pre) (x p.1.1) p.1.2

def twoSegmentEnd {P : Type} (n : ℕ) (pre mid : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (p : TwoSegmentState P n pre mid) : FeatureIndex n → ℝ :=
  forwardEnd mid.length (hierarchyIncrements mid) (twoSegmentStart n pre mid x p) p.2

theorem twoSegmentStart_measurable {P : Type} [MeasurableSpace P] (n : ℕ)
    (pre mid : List (GaussianStep (FeatureIndex n))) {x : P → FeatureIndex n → ℝ}
    (hx : Measurable x) : Measurable (twoSegmentStart n pre mid x) :=
  (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp
    ((hx.comp (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst))

theorem twoSegmentEnd_measurable {P : Type} [MeasurableSpace P] (n : ℕ)
    (pre mid : List (GaussianStep (FeatureIndex n))) {x : P → FeatureIndex n → ℝ}
    (hx : Measurable x) : Measurable (twoSegmentEnd n pre mid x) :=
  (measurable_forwardEnd _ (hierarchyIncrements_measurable mid)).comp
    ((twoSegmentStart_measurable n pre mid hx).prodMk measurable_snd)

def twoSegmentIncrement {P : Type} (n : ℕ) (tail mid pre : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (p : TwoSegmentState P n pre mid) : Fin n → ℝ :=
  actualSpinMean n tail (twoSegmentEnd n pre mid x p)-
    actualSpinMean n (mid++tail) (twoSegmentStart n pre mid x p)

theorem twoSegmentIncrement_measurable {P : Type} [MeasurableSpace P] (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) {x : P → FeatureIndex n → ℝ}
    (hx : Measurable x) : Measurable (twoSegmentIncrement n tail mid pre x) :=
  ((actualSpinMean_measurable n tail ((ha.suffix pre _).suffix mid tail)).comp
    (twoSegmentEnd_measurable n pre mid hx)).sub
    ((actualSpinMean_measurable n (mid++tail) (ha.suffix pre _)).comp
      (twoSegmentStart_measurable n pre mid hx))

theorem actualTwoSegmentLaw_finite {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    IsFiniteMeasure (actualTwoSegmentLaw μ n tail mid pre x hx) := by
  have := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) (mid++tail) pre ha
  have := segmentKernel_markov (uniformWeight_pos n) (finiteFeature n) tail mid (ha.suffix pre _)
  unfold actualTwoSegmentLaw
  infer_instance

theorem twoSegmentIncrement_moment_integrable {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (n k : ℕ)
    (tail mid pre : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (ha : OrderedSteps a (pre++(mid++tail))) (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :
    Integrable (fun p => (projectionEuclideanNorm n (twoSegmentIncrement n tail mid pre x p))^(2*k+2))
      (actualTwoSegmentLaw μ n tail mid pre x hx) := by
  have := actualTwoSegmentLaw_finite μ n tail mid pre ha x hx
  exact actualSpinMean_sub_moment_integrable _ n k tail (mid++tail)
    ((ha.suffix pre _).suffix mid tail) (ha.suffix pre _) _ _
    (twoSegmentEnd_measurable n pre mid hx) (twoSegmentStart_measurable n pre mid hx)

 

def actualForkTwoSegmentLaw {P : Type} [MeasurableSpace P]
    (μ : Measure P) (n : ℕ)
    (btail bmid bpre atail amid apre : List (GaussianStep (FeatureIndex n)))
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) :=
  actualTwoSegmentLaw (actualTwoSegmentLaw μ n btail bmid bpre x hx) n atail amid apre
    (fun p : TwoSegmentState P n bpre bmid => x p.1.1)
    (hx.comp (measurable_fst.comp measurable_fst))

 

theorem eventually_actual_fork_projection (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (btail bmid bpre atail amid apre : List (GaussianStep (FeatureIndex n)))
      (a ab D : ℝ), 0 < a → 0 < D → D ≤ B →
      OrderedSteps a (apre++(amid++atail)) → OrderedSteps ab (bpre++(bmid++btail)) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
      (d : Fin apre.length → ℝ), (∀ j, 0 ≤ d j) → (∑ j, d j = D) →
      (∀ j i, (hierarchyClocks apre j (Sum.inl i) : ℝ) = d j) →
    (∫ p, |∑ i, twoSegmentIncrement n btail bmid bpre x p.1.1 i *
      twoSegmentIncrement n atail amid apre (fun s : TwoSegmentState P n bpre bmid => x s.1.1) p i|^(2*k+2)
      ∂actualForkTwoSegmentLaw μ n btail bmid bpre atail amid apre x hx) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^(2*k+2)*
        ∫ p, (projectionEuclideanNorm n (twoSegmentIncrement n btail bmid bpre x p))^(2*k+2)
          ∂actualTwoSegmentLaw μ n btail bmid bpre x hx := by
  filter_upwards [eventually_uniform_actual_random_later_projection k B] with n hn
  intro P _ btail bmid bpre atail amid apre a ab D ha0 hD hDB ha hb μ _ x hx d hd hdD hc
  have := actualTwoSegmentLaw_finite μ n btail bmid bpre hb x hx
  exact hn (TwoSegmentState P n bpre bmid) atail amid apre a D ha0 hD hDB ha
    (actualTwoSegmentLaw μ n btail bmid bpre x hx) (twoSegmentIncrement n btail bmid bpre x)
    (twoSegmentIncrement_measurable n btail bmid bpre hb hx)
    (fun p : TwoSegmentState P n bpre bmid => x p.1.1)
    (hx.comp (measurable_fst.comp measurable_fst))
    (twoSegmentIncrement_moment_integrable μ n k btail bmid bpre hb x hx)
    (fun _ => alignedFieldClock_of_physical n apre d hd D hdD hc _)

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

omit [Fintype S] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem boundedContinuous_bddSmooth0 (f : BoundedContinuousFunction (ι → ℝ) ℝ) :
    BddSmooth 0 (fun x => f x) :=
  ⟨f.continuous, ‖f‖, norm_nonneg f, fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩

 

theorem actualCutField_law {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x : ι → ℝ) :
    (hierarchyPathKernel w φ (pre++tail) x).map (actualCutField (S := S) pre tail x) =
      (segmentLaw w φ tail pre x).map
        (forwardEnd pre.length (hierarchyIncrements pre) x) := by
  have := hierarchyPathKernel_markov hw φ (pre++tail) ha
  have := segmentLaw_isProbability hw φ tail pre ha x
  have hEnd : Measurable (forwardEnd pre.length (hierarchyIncrements pre) x) :=
    (measurable_forwardEnd _ (hierarchyIncrements_measurable pre)).comp (measurable_const.prodMk measurable_id)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (actualCutField_measurable pre tail x).aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hEnd.aemeasurable
      f.continuous.aestronglyMeasurable,
    integral_actualCutField_test hw φ pre tail ha (boundedContinuous_bddSmooth0 f) x,
    integral_segmentLaw_test hw φ (boundedContinuous_bddSmooth0 f) tail pre ha x]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

def runningMax (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | n+1 => max (runningMax u n) (u (n+1))

theorem runningMax_self_le (u : ℕ → ℝ) (n : ℕ) : u n ≤ runningMax u n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

theorem runningMax_monotone (u : ℕ → ℝ) : Monotone (runningMax u) :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

theorem runningMax_nonneg {u : ℕ → ℝ} (h : ∀ j, 0 ≤ u j) (j : ℕ) :
    0 ≤ runningMax u j := (h j).trans (runningMax_self_le u j)

theorem runningMax_le {u : ℕ → ℝ} {R : ℝ} (h : ∀ j, u j ≤ R) (j : ℕ) :
    runningMax u j ≤ R := by
  induction j with
  | zero => exact h 0
  | succ j ih => exact max_le ih (h (j+1))

 

theorem runningMax_power_exchange {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j)
    {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ((p:ℝ)-1)*(runningMax u N)^p ≤
      (p:ℝ)*(runningMax u N)^(p-1)*u N -
        (p:ℝ)*∑ j ∈ Finset.range N, (runningMax u j)^(p-1)*(u (j+1)-u j) := by
  have he (x : ℝ) : x^(p-1)*x = x^p := by rw [← pow_succ, Nat.sub_add_cancel hp]
  induction N with
  | zero =>
    simp only [runningMax, Finset.sum_range_zero, mul_zero, sub_zero, mul_assoc, he]
    nlinarith [pow_nonneg (hu 0) p]
  | succ N ih =>
    have hy := integer_young (runningMax_nonneg hu N) (runningMax_nonneg hu (N+1)) hp
    have hc : ((runningMax u (N+1))^(p-1)-(runningMax u N)^(p-1))*u (N+1) =
        ((runningMax u (N+1))^(p-1)-(runningMax u N)^(p-1))*runningMax u (N+1) := by
      by_cases h : u (N+1) ≤ runningMax u N
      · simp only [runningMax, max_eq_left h, sub_self, zero_mul]
      · simp only [runningMax, max_eq_right (le_of_not_ge h)]
    have hh : ((p:ℝ)-1)*((runningMax u (N+1))^p-(runningMax u N)^p) ≤
        (p:ℝ)*((runningMax u (N+1))^(p-1))*u (N+1) -
          (p:ℝ)*((runningMax u N)^(p-1))*u N -
          (p:ℝ)*((runningMax u N)^(p-1))*(u (N+1)-u N) := by
      have hmul := congrArg (fun z : ℝ => (p:ℝ)*z) hc
      simp only [sub_mul, he] at hmul
      nlinarith
    rw [Finset.sum_range_succ]
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {U : ℕ → Ω → ℝ}

omit [IsFiniteMeasure μ] in
theorem runningMax_adapted (hU : StronglyAdapted 𝒢 U) (j : ℕ) :
    StronglyMeasurable[𝒢 j] (fun ω => runningMax (fun k => U k ω) j) := by
  induction j with
  | zero => exact hU 0
  | succ j ih => exact ((ih.mono (𝒢.mono (Nat.le_succ j))).measurable.max (hU (j+1)).measurable).stronglyMeasurable

theorem runningMax_power_integrable (hU : StronglyAdapted 𝒢 U)
    {R : ℝ} (hU0 : ∀ j ω, 0 ≤ U j ω) (hR : ∀ j ω, U j ω ≤ R) (j p : ℕ) :
    Integrable (fun ω => (runningMax (fun k => U k ω) j)^p) μ := by
  apply Integrable.of_bound (((runningMax_adapted hU j).mono (𝒢.le j)).pow p).aestronglyMeasurable (R^p)
  exact Eventually.of_forall fun ω => by
    simp only [Pi.pow_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (runningMax_nonneg (fun k => hU0 k ω) j) p)]
    exact pow_le_pow_left₀ (runningMax_nonneg (fun k => hU0 k ω) j) (runningMax_le (fun k => hR k ω) j) p

 theorem submartingale_runningMax_power_exchange (hU : Submartingale U 𝒢 μ)
    (hU0 : ∀ j ω, 0 ≤ U j ω) {R : ℝ} (hR : ∀ j ω, U j ω ≤ R)
    {p : ℕ} (hp : 0 < p) (N : ℕ) :
    ((p:ℝ)-1)*(∫ ω, (runningMax (fun k => U k ω) N)^p ∂μ) ≤
      (p:ℝ)*∫ ω, (runningMax (fun k => U k ω) N)^(p-1)*U N ω ∂μ := by
  let M : ℕ → Ω → ℝ := fun j ω => runningMax (fun k => U k ω) j
  let W : ℕ → Ω → ℝ := fun j ω => M j ω^(p-1)
  have hW j : StronglyMeasurable[𝒢 j] (W j) := (runningMax_adapted hU.stronglyAdapted j).pow (p-1)
  have hb j : ∀ᵐ ω ∂μ, ‖W j ω‖ ≤ R^(p-1) := Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (runningMax_nonneg (fun k => hU0 k ω) j) _)]
    exact pow_le_pow_left₀ (runningMax_nonneg (fun k => hU0 k ω) j) (runningMax_le (fun k => hR k ω) j) _
  have hprod j : Integrable (fun ω => W j ω*(U (j+1) ω-U j ω)) μ :=
    ((hU.integrable (j+1)).sub (hU.integrable j)).bdd_mul
      ((hW j).mono (𝒢.le j)).aestronglyMeasurable (hb j)
  have hI : Integrable (fun ω => W N ω*U N ω) μ :=
    (hU.integrable N).bdd_mul ((hW N).mono (𝒢.le N)).aestronglyMeasurable (hb N)
  have hpositive j : 0 ≤ ∫ ω, W j ω*(U (j+1) ω-U j ω) ∂μ := by
    have hce := condExp_mul_of_stronglyMeasurable_left (hW j) (hprod j)
      ((hU.integrable (j+1)).sub (hU.integrable j))
    rw [← integral_condExp (𝒢.le j)]
    change 0 ≤ ∫ ω, μ[W j * (fun ω => U (j+1) ω-U j ω) | 𝒢 j] ω ∂μ
    rw [integral_congr_ae hce]
    apply integral_nonneg_of_ae
    filter_upwards [hU.condExp_sub_nonneg (Nat.le_succ j)] with ω hω
    exact mul_nonneg (pow_nonneg (runningMax_nonneg (fun k => hU0 k ω) j) _) hω
  have hsum : 0 ≤ ∫ ω, ∑ j ∈ Finset.range N, W j ω*(U (j+1) ω-U j ω) ∂μ := by
    rw [integral_finsetSum _ (fun j _ => hprod j)]
    exact Finset.sum_nonneg fun j _ => hpositive j
  have H := integral_mono
    ((runningMax_power_integrable hU.stronglyAdapted hU0 hR N p).const_mul ((p:ℝ)-1))
    ((hI.const_mul (p:ℝ)).sub ((integrable_finsetSum (Finset.range N) (fun j _ => hprod j)).const_mul (p:ℝ)))
    (fun ω => by simpa only [W, M, Pi.sub_apply, mul_assoc] using
      runningMax_power_exchange (fun j => hU0 j ω) hp N)
  simp only [Pi.sub_apply, integral_sub (hI.const_mul (p:ℝ))
    ((integrable_finsetSum (Finset.range N) (fun j _ => hprod j)).const_mul (p:ℝ)), integral_const_mul] at H
  exact H.trans (sub_le_self _ (mul_nonneg (Nat.cast_nonneg p) hsum))

 

theorem boundedSubmartingale_runningMax_moment (hU : Submartingale U 𝒢 μ)
    (hU0 : ∀ j ω, 0 ≤ U j ω) {R : ℝ} (hR : ∀ j ω, U j ω ≤ R)
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    (∫ ω, (runningMax (fun k => U k ω) N)^p ∂μ) ≤
      (4:ℝ)^p*∫ ω, U N ω^p ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp
  let M : Ω → ℝ := fun ω => runningMax (fun k => U k ω) N
  have hM := runningMax_power_integrable (μ := μ) hU.stronglyAdapted hU0 hR N p
  have hW : Integrable (fun ω => M ω^(p-1)*U N ω) μ := by
    apply (hU.integrable N).bdd_mul
      ((((runningMax_adapted hU.stronglyAdapted N).mono (𝒢.le N)).pow (p-1)).aestronglyMeasurable)
      (c := R^(p-1))
    exact Eventually.of_forall fun ω => by
      simp only [Pi.pow_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (runningMax_nonneg (fun k => hU0 k ω) N) _)]
      exact pow_le_pow_left₀ (runningMax_nonneg (fun k => hU0 k ω) N) (runningMax_le (fun k => hR k ω) N) _
  have hP : Integrable (fun ω => U N ω^p) μ := by
    apply Integrable.of_bound (((hU.stronglyAdapted N).mono (𝒢.le N)).pow p).aestronglyMeasurable (R^p)
    exact Eventually.of_forall fun ω => by
      simp only [Pi.pow_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hU0 N ω) _)]
      exact pow_le_pow_left₀ (hU0 N ω) (hR N ω) _
  have H := submartingale_runningMax_power_exchange hU hU0 hR hp0 N
  have Hy : 4*(p:ℝ)*(∫ ω, M ω^(p-1)*U N ω ∂μ) ≤
      ((p:ℝ)-1)*(∫ ω, M ω^p ∂μ)+(4:ℝ)^p*(∫ ω, U N ω^p ∂μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hM.const_mul _) (hP.const_mul _)]
    apply integral_mono (hW.const_mul _) ((hM.const_mul _).add (hP.const_mul _))
    intro ω
    have h := integer_young (runningMax_nonneg (fun k => hU0 k ω) N)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (hU0 N ω)) hp0
    simpa only [M, Pi.add_apply, mul_pow, mul_assoc, mul_left_comm, mul_comm] using h
  have hMp : 0 ≤ ∫ ω, M ω^p ∂μ := integral_nonneg fun ω =>
    pow_nonneg (runningMax_nonneg (fun k => hU0 k ω) N) _
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp
  change ((p:ℝ)-1)*(∫ ω, M ω^p ∂μ) ≤ _ at H
  nlinarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem boundedMartingale_runningMax_square_moment
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) {R : ℝ} (hR : ∀ j ω, ‖X j ω‖ ≤ R)
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    (∫ ω, (runningMax (fun j => ‖X j ω‖^2) N)^p ∂μ) ≤
      (4:ℝ)^p*∫ ω, ‖X N ω‖^(2*p) ∂μ := by
  have h := boundedSubmartingale_runningMax_moment
    (boundedMartingale_sq_submartingale hX (fun j => Eventually.of_forall (hR j)))
    (fun j ω => sq_nonneg ‖X j ω‖)
    (fun j ω => pow_le_pow_left₀ (norm_nonneg _) (hR j ω) 2) hp N
  simpa only [← pow_mul] using h

theorem boundedMartingale_runningMax_square_Lp
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) {R : ℝ} (hR : ∀ j ω, ‖X j ω‖ ≤ R)
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    (∫ ω, (runningMax (fun j => ‖X j ω‖^2) N)^p ∂μ)^((p:ℝ)⁻¹) ≤
      4*(∫ ω, ‖X N ω‖^(2*p) ∂μ)^((p:ℝ)⁻¹) := by
  have h := boundedMartingale_runningMax_square_moment hX hR hp N
  have hA : 0 ≤ ∫ ω, (runningMax (fun j => ‖X j ω‖^2) N)^p ∂μ :=
    integral_nonneg fun ω => pow_nonneg (runningMax_nonneg (fun j => sq_nonneg ‖X j ω‖) N) _
  have hN : 0 ≤ ∫ ω, ‖X N ω‖^(2*p) ∂μ := integral_nonneg fun ω => pow_nonneg (norm_nonneg _) _
  have hh := Real.rpow_le_rpow hA h (inv_nonneg.mpr (Nat.cast_nonneg p))
  rw [Real.mul_rpow (by positivity) hN,
    Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ) ≤ 4) (by omega : p ≠ 0)] at hh
  exact hh

end SKFluctuations.Hierarchy
namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators

def actualPathMaxSquare (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (τ : ℕ → ℕ) (N : ℕ)
    (q : P × ForwardPath (FeatureIndex n → ℝ) (Spin n) steps.length) : ℝ :=
  runningMax (fun j => ‖actualSpinPath n steps x (τ j) q‖^2) N

 

theorem actualPathMaxSquare_Lp (n : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (τ : ℕ → ℕ) (hτ : Monotone τ) {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    (∫ q, actualPathMaxSquare n steps x τ N q^p
      ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) ≤
      4*(∫ q, ‖actualSpinPath n steps x (τ N) q‖^(2*p)
        ∂(μ ⊗ₘ (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap x hx))^((p:ℝ)⁻¹) := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps ha
  exact boundedMartingale_runningMax_square_Lp
    (martingale_sampled (actualSpinPath_martingale n steps ha μ x hx) τ hτ)
    (fun j => actualSpinPath_norm_le n steps ha x (τ j)) hp N

end SKFluctuations

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

 

theorem integral_pow_le_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hi : Integrable f μ)
    {p : ℕ} (hp : 0 < p) (hip : Integrable (fun ω => f ω^p) μ) :
    (∫ ω, f ω ∂μ)^p ≤ (μ.real univ)^(p-1)*∫ ω, f ω^p ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ, hp.ne']
  have : NeZero μ := ⟨hμ⟩
  have hmass : 0 < μ.real univ := ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top _ _)
  have h := (convexOn_pow p).map_average_le (continuous_pow p).continuousOn
    isClosed_Ici hf hi hip
  rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul] at h
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg hmass.le p)
  have he1 : (μ.real univ)^p*((μ.real univ)⁻¹*∫ ω, f ω ∂μ)^p = (∫ ω, f ω ∂μ)^p := by
    rw [← mul_pow, mul_inv_cancel_left₀ hmass.ne']
  have he2 : (μ.real univ)^p*((μ.real univ)⁻¹*∫ ω, f ω^p ∂μ) =
      (μ.real univ)^(p-1)*∫ ω, f ω^p ∂μ := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
    field_simp
  simpa only [he1,he2] using hh

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω}
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}

 

def conditionalBlockSquare (μ : Measure Ω) (𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → E) (i j : ℕ) : Ω → ℝ := μ[fun ω => ‖X j ω-X i ω‖^2 | 𝒢 i]

theorem conditionalBlockSquare_measurable (i j : ℕ) :
    Measurable (conditionalBlockSquare μ 𝒢 X i j) :=
  (stronglyMeasurable_condExp.mono (𝒢.le i)).measurable

theorem conditionalBlockSquare_joint {Ξ : Type*} [MeasurableSpace Ξ]
    {i j : Ξ → ℕ} (hi : Measurable i) (hj : Measurable j) :
    Measurable (fun z : Ξ × Ω => conditionalBlockSquare μ 𝒢 X (i z.1) (j z.1) z.2) := by
  have h : Measurable (fun z : (ℕ × ℕ) × Ω => conditionalBlockSquare μ 𝒢 X z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_right fun k => conditionalBlockSquare_measurable k.1 k.2
  exact h.comp ((hi.prodMk hj).comp measurable_fst |>.prodMk measurable_snd)

 

theorem conditionalBlockSquare_uniform_bounds
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i j, 0 ≤ conditionalBlockSquare μ 𝒢 X i j ω ∧
      conditionalBlockSquare μ 𝒢 X i j ω ≤ (2*R)^2 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hb : ∀ᵐ ω ∂μ, ‖‖X j ω-X i ω‖^2‖ ≤ (2*R)^2 := by
    filter_upwards [hR i,hR j] with ω hi hj
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) 2
  have hlow := condExp_nonneg (m := 𝒢 i) (μ := μ)
    (Eventually.of_forall fun ω => sq_nonneg ‖X j ω-X i ω‖)
  have hhi := ae_bdd_norm_condExp_of_ae_bdd_norm (m := 𝒢 i) hb
  filter_upwards [hlow,hhi] with ω hω hω'
  refine ⟨hω, ?_⟩
  exact (le_abs_self _).trans hω'

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators

 

theorem parameter_integral_power_bound {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (ν : Measure Ξ) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {f : Ξ → Ω → ℝ} (hf : Measurable (Function.uncurry f))
    {R : ℝ} (hb : ∀ᵐ ω ∂μ, ∀ ξ, 0 ≤ f ξ ω ∧ f ξ ω ≤ R)
    {p : ℕ} (hp : 0 < p) {M : ℝ}
    (hm : ∀ᵐ ξ ∂ν, (∫ ω, f ξ ω^p ∂μ) ≤ M) :
    (∫ ω, (∫ ξ, f ξ ω ∂ν)^p ∂μ) ≤ (ν.real univ)^p*M := by
  have hprod : ∀ᵐ z ∂ν.prod μ, 0 ≤ f z.1 z.2 ∧ f z.1 z.2 ≤ R := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_le measurable_const hf).inter (measurableSet_le hf measurable_const))).mpr
    exact Eventually.of_forall fun ξ => hb.mono fun ω hω => hω ξ
  have hi : Integrable (Function.uncurry f) (ν.prod μ) :=
    Integrable.of_bound hf.aestronglyMeasurable R (hprod.mono fun z hz => by
      change ‖f z.1 z.2‖ ≤ R
      simpa only [Real.norm_eq_abs,abs_of_nonneg hz.1] using hz.2)
  have hip : Integrable (fun z : Ξ × Ω => f z.1 z.2^p) (ν.prod μ) :=
    Integrable.of_bound (hf.pow_const p).aestronglyMeasurable (R^p) (hprod.mono fun z hz => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hz.1 p)]
      exact pow_le_pow_left₀ hz.1 hz.2 p)
  have hamb : ∀ᵐ ω ∂μ, ‖∫ ξ, f ξ ω ∂ν‖ ≤ (ν.real univ)*R := by
    filter_upwards [hb] with ω hω
    simpa only [mul_comm] using (norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hω ξ).1]
      exact (hω ξ).2))
  have hamp : Integrable (fun ω => (∫ ξ, f ξ ω ∂ν)^p) μ := by
    apply Integrable.of_bound (hi.integral_prod_right.aestronglyMeasurable.pow p) ((ν.real univ*R)^p)
    filter_upwards [hamb] with ω hω
    change ‖(∫ ξ, f ξ ω ∂ν)^p‖ ≤ _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hω p
  have hj : (∫ ω, (∫ ξ, f ξ ω ∂ν)^p ∂μ) ≤
      ∫ ω, (ν.real univ)^(p-1)*(∫ ξ, f ξ ω^p ∂ν) ∂μ := by
    apply integral_mono_ae hamp (hip.integral_prod_right.const_mul _)
    filter_upwards [hb,hi.prod_left_ae,hip.prod_left_ae] with ω hω hiω hipω
    exact integral_pow_le_mass ν (Eventually.of_forall fun ξ => (hω ξ).1) hiω hp hipω
  rw [integral_const_mul, ← integral_integral_swap hip] at hj
  calc
    _ ≤ (ν.real univ)^(p-1)*(∫ ξ, ∫ ω, f ξ ω^p ∂μ ∂ν) := hj
    _ ≤ (ν.real univ)^(p-1)*(ν.real univ*M) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (measureReal_nonneg) _)
      simpa only [integral_const,smul_eq_mul] using
        integral_mono_ae hip.integral_prod_left (integrable_const M) hm
    _ = _ := by rw [← mul_assoc,← pow_succ,Nat.sub_add_cancel hp]

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Ω)} {X : ℕ → Ω → E}

theorem boundedMartingale_cut_moment_mono (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {k : ℕ} (hk : 0 < k)
    {i j : ℕ} (hij : i ≤ j) :
    (∫ ω, ‖X i ω‖^k ∂μ) ≤ ∫ ω, ‖X j ω‖^k ∂μ := by
  have hInt : Integrable (fun ω => ‖X j ω‖^k) μ :=
    Integrable.of_bound (((hX.stronglyMeasurable j).mono (𝒢.le j)).norm.pow k).aestronglyMeasurable (R^k)
      ((hR j).mono fun ω hω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hω _)
  have hc := integral_norm_condExp_rpow_le (m := 𝒢 i)
    (show (1:ℝ) ≤ k by exact_mod_cast hk) (by simpa only [Real.rpow_natCast] using hInt)
  have he : (∫ ω, ‖(μ[X j | 𝒢 i]) ω‖^(k:ℝ) ∂μ) = ∫ ω, ‖X i ω‖^k ∂μ := by
    apply integral_congr_ae
    filter_upwards [hX.condExp_ae_eq hij] with ω hω
    simp only [hω,Real.rpow_natCast]
  rw [← he]
  simpa only [Real.rpow_natCast] using hc

end SKFluctuations.Hierarchy

end

end OAI
