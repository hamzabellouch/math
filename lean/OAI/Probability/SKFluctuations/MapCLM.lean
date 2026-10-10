import Mathlib
import OAI.Probability.SKFluctuations.HierarchyPenalty

namespace OAI

/-! Map C L M. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]

theorem ExponentialIncrement.mapCLM {ν : Measure D} (hν : ExponentialIncrement ν)
    (L : D →L[ℝ] E) : ExponentialIncrement (ν.map L) := by
  intro c
  apply (integrable_map_measure (Real.continuous_exp.comp (continuous_norm.const_mul c)).aestronglyMeasurable
    L.measurable.aemeasurable).mpr
  apply (hν (|c| *‖L‖)).mono'
    ((Real.continuous_exp.comp ((continuous_norm.comp L.continuous).const_mul c)).aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖Real.exp (c*‖L z‖)‖ ≤ Real.exp (|c| *‖L‖*‖z‖)
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_exp]
    exact (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_left (L.le_opNorm z) (abs_nonneg c)).trans_eq (by ring))

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
theorem BddSmooth.affine_zero {A : E → ℝ} {n : ℕ} (hA : BddSmooth n A)
    (L : D →L[ℝ] E) (x : E) : BddSmooth 0 (fun z => A (x+L z)) := by
  obtain ⟨B,hB,hb⟩ := hA.bound
  exact ⟨hA.continuous.comp (continuous_const.add L.continuous),B,hB,fun z => hb _⟩

variable {ι : Type*} [Fintype ι]

 

def linearGaussian (L : (ι → ℝ) →L[ℝ] E) (t : ℝ≥0) : Measure E :=
  (Measure.pi fun _ : ι => gaussianReal 0 t).map L

instance linearGaussian_probability (L : (ι → ℝ) →L[ℝ] E) (t : ℝ≥0) :
    IsProbabilityMeasure (linearGaussian L t) := by
  unfold linearGaussian
  infer_instance

theorem exponentialIncrement_linearGaussian (L : (ι → ℝ) →L[ℝ] E) (t : ℝ≥0) :
    ExponentialIncrement (linearGaussian L t) :=
  (exponentialIncrement_gaussian (fun _ => t)).mapCLM L

def linearClockContinuation (L : (ι → ℝ) →L[ℝ] E) (m : ℝ) (F : E → ℝ) (t : ℝ) : E → ℝ :=
  shiftedContinuation (linearGaussian L (Real.toNNReal t)) m F

def linearClockTest (L : (ι → ℝ) →L[ℝ] E) (m : ℝ) (F A : E → ℝ) (t : ℝ) : E → ℝ :=
  shiftedMean (linearGaussian L (Real.toNNReal t)) m F A

def linearClockRoot (L : (ι → ℝ) →L[ℝ] E) (F : E → ℝ) (t : ℝ) : E → ℝ :=
  zeroContinuation (linearGaussian L (Real.toNNReal t)) F

theorem linearClockContinuation_eq (L : (ι → ℝ) →L[ℝ] E) {F : E → ℝ}
    (hF : Continuous F) (m t : ℝ) (x : E) :
    linearClockContinuation L m F t x = clockContinuation m (fun z => F (x+L z)) t 0 := by
  have hi := integral_map_of_stronglyMeasurable (μ := Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t))
    L.measurable (Real.continuous_exp.comp ((hF.comp ((continuous_const : Continuous (fun _ : E => x)).add continuous_id)).const_mul m)).stronglyMeasurable
  change Real.log (∫ z, Real.exp (m*F (x+z)) ∂linearGaussian L (Real.toNNReal t))/m = _
  dsimp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, id_eq] at hi
  rw [linearGaussian,hi]
  simp only [clockContinuation,shiftedContinuation,zero_add]

theorem linearClockTest_eq (L : (ι → ℝ) →L[ℝ] E) {F A : E → ℝ}
    (hF : Continuous F) (hA : Continuous A) (m t : ℝ) (x : E) :
    linearClockTest L m F A t x = clockTest m (fun z => F (x+L z)) (fun z => A (x+L z)) t 0 := by
  have hn := integral_map_of_stronglyMeasurable (μ := Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t))
    L.measurable (((hA.comp ((continuous_const : Continuous (fun _ : E => x)).add continuous_id)).mul
      (Real.continuous_exp.comp ((hF.comp ((continuous_const : Continuous (fun _ : E => x)).add continuous_id)).const_mul m)))).stronglyMeasurable
  have hd := integral_map_of_stronglyMeasurable (μ := Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t))
    L.measurable (Real.continuous_exp.comp ((hF.comp ((continuous_const : Continuous (fun _ : E => x)).add continuous_id)).const_mul m)).stronglyMeasurable
  change (∫ z, A (x+z)*Real.exp (m*F (x+z)) ∂linearGaussian L (Real.toNNReal t)) /
    (∫ z, Real.exp (m*F (x+z)) ∂linearGaussian L (Real.toNNReal t)) = _
  dsimp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, id_eq] at hn hd
  rw [linearGaussian,hn,hd]
  simp only [clockTest,shiftedMean,tiltedMean,zero_add]

theorem linearClockRoot_eq (L : (ι → ℝ) →L[ℝ] E) {F : E → ℝ}
    (hF : Continuous F) (t : ℝ) (x : E) :
    linearClockRoot L F t x = clockRoot (fun z => F (x+L z)) t 0 := by
  have hi := integral_map_of_stronglyMeasurable (μ := Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t))
    L.measurable (hF.comp ((continuous_const : Continuous (fun _ : E => x)).add continuous_id)).stronglyMeasurable
  change (∫ z, F (x+z) ∂linearGaussian L (Real.toNNReal t)) = _
  dsimp only [Function.comp_def, Pi.add_apply, Pi.mul_apply, id_eq] at hi
  rw [linearGaussian,hi]
  simp only [clockRoot,zeroContinuation,zero_add]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Nonempty S]

 
theorem gaussianHierarchyMean_linear_components [DecidableEq κ] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps)
    (v : κ → ℝ) (x : ι → ℝ) :
    gaussianHierarchyMean w φ (fun σ => φ σ (L v)) steps x =
      ∑ i, v i*gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) steps x := by
  have hv : v = ∑ i, v i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  have hφ : (fun σ => φ σ (L v)) = fun σ => ∑ i, v i*φ σ (L (Pi.single i 1)) := by
    funext σ
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul,smul_eq_mul]
  rw [hφ,gaussianHierarchyMean_sum hw φ steps ha Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussianHierarchyMean_const_mul_ordered hw φ _ steps ha]

theorem gaussianHierarchy_linear_feature_derivatives [DecidableEq κ] {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (∀ y v t, HasDerivAt (fun s : ℝ => gaussianHierarchy w φ steps (x+L (y+s • v)))
      (∑ i, v i*gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) steps (x+L (y+t • v))) t) ∧
    (∀ i y t, HasDerivAt (fun s : ℝ => gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1)))
        steps (x+L (y+s • Pi.single i 1)))
      (gaussianHierarchyResponse w φ (fun σ => φ σ (L (Pi.single i 1))) (L (Pi.single i 1))
        steps (x+L (y+t • Pi.single i 1))) t) := by
  constructor
  · intro y v t
    rw [← gaussianHierarchyMean_linear_components hw φ L steps ha v]
    simpa only [map_add,map_smul,add_assoc] using
      gaussianHierarchy_hasDerivAt hw φ steps ha (x+L y) (L v) t
  · intro i y t
    simpa only [map_add,map_smul,add_assoc] using
      gaussianHierarchyMean_hasDerivAt hw φ (fun σ => φ σ (L (Pi.single i 1))) steps ha
        (x+L y) (L (Pi.single i 1)) t

 
def linearFeaturePenalty [DecidableEq κ] (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (a : ℝ) (steps : List (GaussianStep ι)) (x : ι → ℝ) : ℝ :=
  ∑ i, hierarchyPenalty w φ (L (Pi.single i 1)) a steps x

theorem linearFeaturePenalty_smooth [DecidableEq κ] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ))
    {a : ℝ} (steps : List (GaussianStep ι)) (ha : OrderedSteps a steps) (r : ℕ) :
    BddSmooth r (linearFeaturePenalty w φ L a steps) :=
  BddSmooth.sum Finset.univ (fun i _ => hierarchyPenalty_smooth hw φ (L (Pi.single i 1)) steps ha r)

theorem linear_feature_trace_telescope [DecidableEq κ] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) {q a : ℝ}
    (hq : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = q)
    (steps : List (GaussianStep ι)) (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (∑ i, gaussianHierarchyResponse w φ (fun σ => φ σ (L (Pi.single i 1))) (L (Pi.single i 1)) steps x) +
      a*(∑ i, (gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) steps x)^2) =
      q-linearFeaturePenalty w φ L a steps x := by
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  simp_rw [gaussianHierarchyResponse_mass_telescope hw φ _ steps ha]
  rw [Finset.sum_sub_distrib]
  have he := congrFun (gaussianHierarchyMean_sum hw φ steps ha Finset.univ
    (fun i σ => (φ σ (L (Pi.single i 1)))^2)) x
  simp_rw [hq] at he
  rw [gaussianHierarchyMean_const hw φ steps ha q x] at he
  rw [← he]
  rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι] {n : ℕ}

def linearClockDerivative (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) (m : ℝ)
    (F : (ι → ℝ) → ℝ) (G H : Fin (n+1) → (ι → ℝ) → ℝ) (t : ℝ) (x : ι → ℝ) : ℝ :=
  (1/2:ℝ)*((∑ i, linearClockTest L m F (H i) t x) + m *
    ∑ i, linearClockTest L m F (fun y => (G i y)^2) t x)

 

theorem parametric_linear_clock (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {F : (ι → ℝ) → ℝ} {G H : Fin (n+1) → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x y v t, HasDerivAt (fun s : ℝ => F (x+L (y+s • v)))
      (∑ i, v i*G i (x+L (y+t • v))) t)
    (hd₁ : ∀ x i y t, HasDerivAt (fun s : ℝ => G i (x+L (y+s • Pi.single i 1)))
      (H i (x+L (y+t • Pi.single i 1))) t)
    {m : ℝ} (hm : 0 < m) :
    ∃ K, ∀ r, ParametricRegular 0 r K (linearClockContinuation L m F) (linearClockDerivative L m F G H) := by
  have hGs (i) : BddSmooth 0 (fun y => (G i y)^2) := by
    simpa only [pow_two] using (hG i).mul (hG i)
  choose BH hBH bH using fun i => (hH i).bound
  choose BG hBG bG using fun i => (hGs i).bound
  let K : ℝ := (1/2)*((∑ i, BH i)+m*(∑ i, BG i))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num) (add_nonneg (Finset.sum_nonneg fun i _ => hBH i)
      (mul_nonneg hm.le (Finset.sum_nonneg fun i _ => hBG i)))
  have hi (t : ℝ) (x : ι → ℝ) :
      Integrable (fun z => Real.exp (m*F (x+z))) (linearGaussian L (Real.toNNReal t)) :=
    (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF m x
  refine ⟨K, fun r => ⟨hK, ?_, ?_, ?_, ?_⟩⟩
  · intro t _
    exact ⟨C,lipschitzWith_shiftedContinuation hF hm (hi t)⟩
  · intro t _
    apply Continuous.const_mul
    apply Continuous.add
    · exact continuous_finsetSum _ (fun i _ => continuous_shiftedMean hF (hH i).continuous
        (hBH i) (bH i) (hi t))
    · exact (continuous_finsetSum _ (fun i _ => continuous_shiftedMean hF (hGs i).continuous
        (hBG i) (bG i) (hi t))).const_mul m
  · intro t _ x
    have hBH' (i) : |linearClockTest L m F (H i) t x| ≤ BH i :=
      abs_tiltedMean_le ((hH i).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi t x) (fun z => bH i (x+z))
    have hBG' (i) : |linearClockTest L m F (fun y => (G i y)^2) t x| ≤ BG i :=
      abs_tiltedMean_le ((hGs i).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi t x) (fun z => bG i (x+z))
    dsimp [linearClockDerivative,K]
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_pos hm]
    exact add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hBH' i))
      (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hBG' i)) hm.le)
  · intro t ht x
    have hFx := hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)
    obtain ⟨Kx,hKx⟩ := parametric_clock hFx (fun i => (hG i).affine_zero L x)
      (fun i => (hH i).affine_zero L x) (hd x) (hd₁ x) hm
    have hh := (hKx r).derivative t ht 0
    have he (s : ℝ) := linearClockContinuation_eq L hF.continuous m s x
    have hde : linearClockDerivative L m F G H t x =
        clockDerivative m (fun z => F (x+L z)) (fun i z => G i (x+L z))
          (fun i z => H i (x+L z)) t 0 := by
      simp only [linearClockDerivative,clockDerivative,linearClockTest_eq L hF.continuous (hH _).continuous,
        linearClockTest_eq L hF.continuous (hGs _).continuous]
    rw [hde]
    exact hh.congr_of_eventuallyEq (Eventually.of_forall he)

 
theorem parametric_continuous_linear_clock (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    {F A : (ι → ℝ) → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F) (hA : BddSmooth 0 A)
    {m : ℝ} (hm : 0 < m) :
    ∃ K, ParametricContinuous (Ici 0) C K (linearClockContinuation L m F) (linearClockTest L m F A) := by
  obtain ⟨K,hK,hb⟩ := hA.bound
  have hi (t x) := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF m x
  refine ⟨K,⟨hK,?_,?_,?_,?_,?_⟩⟩
  · intro t _
    exact lipschitzWith_shiftedContinuation hF hm (hi t)
  · intro t _
    exact continuous_shiftedMean hF hA.continuous hK hb (hi t)
  · intro t _ x
    exact abs_tiltedMean_le (hA.continuous.comp (continuous_const.add continuous_id)).measurable
      (hi t x) (fun z => hb (x+z))
  · intro x
    have hh := clockContinuation_continuousOn (hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)) m 0
    exact hh.congr (fun t _ => linearClockContinuation_eq L hF.continuous m t x)
  · intro x
    have hh := clockTest_continuousOn (hF.comp ((isometry_add_left x).lipschitzWith.comp L.lipschitzWith)) (hA.affine_zero L x) m 0
    exact hh.congr (fun t _ => linearClockTest_eq L hF.continuous hA.continuous m t x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S] {n : ℕ}

theorem linearClockDerivative_feature_trace {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {Q m : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q) (tail : List (GaussianStep ι))
    (ha : OrderedSteps m tail) (t : ℝ) (x : ι → ℝ) :
    linearClockDerivative L m (gaussianHierarchy w φ tail)
      (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) tail)
      (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (L (Pi.single i 1))) (L (Pi.single i 1)) tail) t x =
      (1/2:ℝ)*(Q-linearClockTest L m (gaussianHierarchy w φ tail) (linearFeaturePenalty w φ L m tail) t x) := by
  let ν := linearGaussian L (Real.toNNReal t)
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF m x
  have hH (i) := gaussianHierarchyResponse_smooth hw φ (fun σ => φ σ (L (Pi.single i 1)))
    (L (Pi.single i 1)) tail ha 0
  have hG (i) : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) tail y)^2) := by
    simpa only [pow_two] using (gaussianHierarchyMean_smooth hw φ (fun σ => φ σ (L (Pi.single i 1))) tail ha 0).mul
      (gaussianHierarchyMean_smooth hw φ (fun σ => φ σ (L (Pi.single i 1))) tail ha 0)
  have he := funext fun y => linear_feature_trace_telescope hw φ L hQ tail ha y
  have hn := congrArg (fun A => shiftedMean ν m (gaussianHierarchy w φ tail) A x) he
  rw [shiftedMean_add (BddSmooth.sum Finset.univ (fun i _ => hH i))
      ((BddSmooth.sum Finset.univ (fun i _ => hG i)).const_mul m) hi,
    shiftedMean_const_mul,shiftedMean_sum hH hi,shiftedMean_sum hG hi] at hn
  have hc : shiftedMean ν m (gaussianHierarchy w φ tail) (fun _ => Q) x = Q := by
    simp only [shiftedMean,tiltedMean,integral_const_mul]
    exact mul_div_cancel_right₀ Q (partition_pos m hi).ne'
  rw [shiftedMean_sub (BddSmooth.const 0 Q) (linearFeaturePenalty_smooth hw φ L tail ha 0) hi,hc] at hn
  exact congrArg (fun z : ℝ => (1/2)*z) hn

 

theorem rootedHierarchy_linear_clock {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ))
    (front tail : List (GaussianStep ι)) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : ι → ℝ≥0) {t : ℝ} (ht : 0 < t) (x : ι → ℝ) :
    HasDerivAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixContinuation front (linearClockContinuation L m (gaussianHierarchy w φ tail) s)) x)
      (zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (linearClockContinuation L m (gaussianHierarchy w φ tail) t)
          (linearClockDerivative L m (gaussianHierarchy w φ tail)
            (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) tail)
            (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (L (Pi.single i 1)))
              (L (Pi.single i 1)) tail) t)) x) t := by
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  obtain ⟨K,hK⟩ := parametric_linear_clock L hC
    (fun i => gaussianHierarchyMean_smooth hw φ _ tail ha 0)
    (fun i => gaussianHierarchyResponse_smooth hw φ _ _ tail ha 0)
    (fun y => (gaussianHierarchy_linear_feature_derivatives hw φ L tail ha y).1)
    (fun y => (gaussianHierarchy_linear_feature_derivatives hw φ L tail ha y).2) hm
  exact (((hK (t+1)).prefix front hfront).root q₀).derivative t ⟨ht,by linarith⟩ x

theorem rootedHierarchy_corrected_linear_clock {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {Q : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (front tail : List (GaussianStep ι)) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : ι → ℝ≥0) {t : ℝ} (ht : 0 < t) (x : ι → ℝ) :
    HasDerivAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixContinuation front (linearClockContinuation L m (gaussianHierarchy w φ tail) s)) x-Q*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (linearClockContinuation L m (gaussianHierarchy w φ tail) t)
          (linearClockTest L m (gaussianHierarchy w φ tail) (linearFeaturePenalty w φ L m tail) t)) x) t := by
  have hh := (rootedHierarchy_linear_clock hw φ L front tail hm ha hfront q₀ ht x).sub
    (((hasDerivAt_id t).const_mul Q).div_const 2)
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  have hi := (exponentialIncrement_linearGaussian L (Real.toNNReal t)).integrable_shift hF m
  have hP : BddSmooth 0 (linearClockTest L m (gaussianHierarchy w φ tail) (linearFeaturePenalty w φ L m tail) t) :=
    (linearFeaturePenalty_smooth hw φ L tail ha 0).shiftedMean (gaussianHierarchy_regular hw φ tail ha 0) hi
  have hC : LipschitzWith C (linearClockContinuation L m (gaussianHierarchy w φ tail) t) :=
    lipschitzWith_shiftedContinuation hF hm hi
  have hPT := prefixTest_smooth0 hC hP front hfront
  have he : linearClockDerivative L m (gaussianHierarchy w φ tail)
      (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (L (Pi.single i 1))) tail)
      (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (L (Pi.single i 1))) (L (Pi.single i 1)) tail) t =
      fun y => Q/2+(-(1/2:ℝ))*linearClockTest L m (gaussianHierarchy w φ tail) (linearFeaturePenalty w φ L m tail) t y := by
    funext y
    rw [linearClockDerivative_feature_trace hw φ L hQ tail ha t y]
    ring
  rw [he] at hh
  have he' := funext (prefixTest_affine hC hP front hfront (Q/2) (-(1/2:ℝ)))
  rw [he',zeroContinuation_affine hPT q₀ (Q/2) (-(1/2:ℝ)) x] at hh
  exact hh.congr_deriv (by ring)

 

theorem rootedHierarchy_corrected_linear_clock_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (Fin (n+1) → ℝ) →L[ℝ] (ι → ℝ)) {Q : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (front tail : List (GaussianStep ι)) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : ι → ℝ≥0) {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    HasDerivWithinAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixContinuation front (linearClockContinuation L m (gaussianHierarchy w φ tail) s)) x-Q*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (linearClockContinuation L m (gaussianHierarchy w φ tail) t)
          (linearClockTest L m (gaussianHierarchy w φ tail) (linearFeaturePenalty w φ L m tail) t)) x) (Ici 0) t := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
    obtain ⟨K,hK⟩ := parametric_continuous_linear_clock L hC (linearFeaturePenalty_smooth hw φ L tail ha 0) hm
    have hc := (hK.prefix front hfront).root q₀
    have hp := (hc.potential x).sub ((continuous_id.const_mul Q).div_const 2).continuousOn
    have hd := (hc.tested x).const_mul (-(1/2:ℝ))
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioi 0)
    · intro s hs
      exact (rootedHierarchy_corrected_linear_clock hw φ L hQ front tail hm ha hfront q₀ hs x).differentiableAt.differentiableWithinAt
    · exact (hp 0 (by simp)).mono Ioi_subset_Ici_self
    · exact self_mem_nhdsWithin
    · have hlim := (hd 0 (by simp)).tendsto.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (rootedHierarchy_corrected_linear_clock hw φ L hQ front tail hm ha hfront q₀ hs x).deriv.symm
  · exact (rootedHierarchy_corrected_linear_clock hw φ L hQ front tail hm ha hfront q₀ ht x).hasDerivWithinAt

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι κ S : Type*} [Fintype ι] [Fintype κ] [Fintype S] [Nonempty S]

 theorem hierarchyPenalty_upper {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) :
    hierarchyPenalty w φ v a steps x ≤
      (1-a)*gaussianHierarchyMean w φ (fun σ => (φ σ v)^2) steps x := by
  obtain ⟨T,_,hM,hQ⟩ := gaussianHierarchy_source hw φ v steps ha
  have hd := gaussianHierarchyMean_hasDerivAt hw φ (fun σ => φ σ v) steps ha x v 0
  rw [← hM] at hd
  have he : gaussianHierarchyResponse w φ (fun σ => φ σ v) v steps x = T.hessian x := by
    simpa only [zero_smul,add_zero] using hd.unique (T.second x 0)
  have ht := gaussianHierarchyResponse_mass_telescope hw φ v steps ha x
  rw [he,← hM,← hQ] at ht
  rw [← hQ]
  linarith [T.lower x]

 theorem linearFeaturePenalty_bounds [DecidableEq κ] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) {Q a : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (steps : List (GaussianStep ι)) (ha : OrderedSteps a steps) (x : ι → ℝ) :
    0 ≤ linearFeaturePenalty w φ L a steps x ∧
      linearFeaturePenalty w φ L a steps x ≤ (1-a)*Q := by
  constructor
  · exact Finset.sum_nonneg fun i _ => hierarchyPenalty_nonneg hw φ _ steps ha x
  · calc
      linearFeaturePenalty w φ L a steps x ≤
          ∑ i, (1-a)*gaussianHierarchyMean w φ (fun σ => (φ σ (L (Pi.single i 1)))^2) steps x :=
        Finset.sum_le_sum fun i _ => hierarchyPenalty_upper hw φ _ steps ha x
      _ = (1-a)*Q := by
        rw [← Finset.mul_sum]
        have hh := congrFun (gaussianHierarchyMean_sum hw φ steps ha Finset.univ
          (fun i σ => (φ σ (L (Pi.single i 1)))^2)) x
        simp_rw [hQ] at hh
        rw [gaussianHierarchyMean_const hw φ steps ha Q x] at hh
        rw [← hh]

 theorem linearFeaturePenalty_abs_le [DecidableEq κ] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) {Q a : ℝ}
    (hQ : ∀ σ, ∑ i, (φ σ (L (Pi.single i 1)))^2 = Q)
    (steps : List (GaussianStep ι)) (ha : OrderedSteps a steps) (x : ι → ℝ) :
    |linearFeaturePenalty w φ L a steps x| ≤ Q := by
  obtain ⟨hp,hb⟩ := linearFeaturePenalty_bounds hw φ L hQ steps ha x
  rw [abs_of_nonneg hp]
  have hQ0 : 0 ≤ Q := by
    obtain ⟨σ⟩ := ‹Nonempty S›
    rw [← hQ σ]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha0 : 0 ≤ a := by cases steps with | nil => exact ha.1 | cons st tail => exact ha.1
  exact hb.trans (by nlinarith)

 theorem prefixTest_abs_le {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) {K : ℝ} (hb : ∀ x, |A x| ≤ K)
    (front : List (GaussianStep ι)) (hm : ∀ st ∈ front, 0 < st.1) (x : ι → ℝ) :
    |prefixTest front F A x| ≤ K := by
  induction front generalizing x with
  | nil => exact hb x
  | cons st tail ih =>
    rcases st with ⟨m,q⟩
    have htail := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    exact abs_tiltedMean_le
      ((prefixTest_smooth0 hF hA tail htail).continuous.comp (continuous_const.add continuous_id)).measurable
      ((exponentialIncrement_gaussian q).integrable_shift (prefixContinuation_lipschitz hF tail htail) m x)
      (fun z => ih htail (x+z))

 theorem zeroContinuation_abs_le {A : (ι → ℝ) → ℝ} {K : ℝ}
    (hb : ∀ x, |A x| ≤ K) (q : ι → ℝ≥0) (x : ι → ℝ) :
    |zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) A x| ≤ K := by
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun z => A (x+z))
    (Eventually.of_forall fun z => hb (x+z))
  simpa [zeroContinuation,ν] using h

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem BddSmooth.prod {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq κ] {r : ℕ} (s : Finset κ) {A : κ → E → ℝ}
    (h : ∀ i ∈ s, BddSmooth r (A i)) : BddSmooth r (fun x => ∏ i ∈ s, A i x) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using BddSmooth.const r 1
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      (h i (Finset.mem_insert_self i s)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

universe uT vT

 

inductive ProductTree (ι : Type uT) (S : Type vT) : List (GaussianStep ι) → Type (max uT vT) where
  | leaf (A : S → ℝ) : ProductTree ι S []
  | node (st : GaussianStep ι) {tail : List (GaussianStep ι)} (k : ℕ)
      (child : Fin (k+1) → ProductTree ι S tail) : ProductTree ι S (st::tail)

 def ProductTree.leaves : {steps : List (GaussianStep ι)} → ProductTree ι S steps → ℕ
  | _, .leaf _ => 1
  | _, .node _ _ child => ∑ i, (child i).leaves

 
noncomputable def ProductTree.mean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    {steps : List (GaussianStep ι)} → ProductTree ι S steps → (ι → ℝ) → ℝ
  | [], .leaf A => gaussianHierarchyMean w φ A []
  | (m,q)::tail, .node _ _ child => fun x => ∏ i,
      shiftedMean (Measure.pi fun j => gaussianReal 0 (q j)) m (gaussianHierarchy w φ tail)
        ((child i).mean w φ) x

 

noncomputable def ProductTree.row (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    {steps : List (GaussianStep ι)} → ProductTree ι S steps → ℝ → (ι → ℝ) → ℝ
  | [], .leaf A, a => fun x => gaussianHierarchyMean w φ (fun σ => A σ*φ σ v) [] x +
      (a-1)*gaussianHierarchyMean w φ A [] x*gaussianHierarchyMean w φ (fun σ => φ σ v) [] x
  | (m,q)::tail, .node _ k child, a => fun x =>
      let ν := Measure.pi fun j => gaussianReal 0 (q j)
      let F := gaussianHierarchy w φ tail
      let M := gaussianHierarchyMean w φ (fun σ => φ σ v) ((m,q)::tail)
      (a-(k+1:ℝ)*m)*(∏ i, shiftedMean ν m F ((child i).mean w φ) x)*M x +
        ∑ i, shiftedMean ν m F ((child i).row w φ v m) x *
          ∏ j ∈ Finset.univ.erase i, shiftedMean ν m F ((child j).mean w φ) x

 theorem ProductTree.mean_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {steps : List (GaussianStep ι)} (T : ProductTree ι S steps)
    {a : ℝ} (ha : OrderedSteps a steps) (r : ℕ) : BddSmooth r (T.mean w φ) := by
  induction T generalizing a with
  | leaf A => exact gaussianHierarchyMean_smooth hw φ A [] ha r
  | @node st tail k child ih =>
    rcases st with ⟨m,q⟩
    exact BddSmooth.prod Finset.univ (fun i _ =>
      (ih i ha.2.2.2).shiftedMean (gaussianHierarchy_regular hw φ tail ha.2.2.2 r)
        (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q))

 theorem ProductTree.row_smooth {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) {steps : List (GaussianStep ι)}
    (T : ProductTree ι S steps) {b : ℝ} (hb : OrderedSteps b steps) (a : ℝ) (r : ℕ) :
    BddSmooth r (T.row w φ v a) := by
  induction T generalizing a b with
  | leaf A =>
    exact (gaussianHierarchyMean_smooth hw φ _ [] hb r).add
      (((gaussianHierarchyMean_smooth hw φ A [] hb r).const_mul (a-1)).mul
        (gaussianHierarchyMean_smooth hw φ _ [] hb r))
  | @node st tail k child ih =>
    rcases st with ⟨m,q⟩
    have hR := gaussianHierarchy_regular hw φ tail hb.2.2.2 r
    have hi := gaussianHierarchy_integrable hw φ tail hb.2.2.2 m q
    have hA (i) := ((child i).mean_smooth hw φ hb.2.2.2 r).shiftedMean hR hi
    have hD (i) := (ih i hb.2.2.2 m).shiftedMean hR hi
    exact (((BddSmooth.prod Finset.univ (fun i _ => hA i)).const_mul (a-(k+1:ℝ)*m)).mul
      (gaussianHierarchyMean_smooth hw φ _ ((m,q)::tail) hb r)).add
      (BddSmooth.sum Finset.univ (fun i _ => (hD i).mul
        (BddSmooth.prod (Finset.univ.erase i) (fun j _ => hA j))))

 

 theorem sum_product_fork {κ : Type*} [Fintype κ] [DecidableEq κ] (A R : κ → ℝ) (m M : ℝ) :
    (∑ i, (R i-m*A i*M)*(∏ j ∈ Finset.univ.erase i, A j)) =
      (∑ i, R i*(∏ j ∈ Finset.univ.erase i, A j)) - (Fintype.card κ:ℝ)*m*(∏ i, A i)*M := by
  have he (i : κ) : A i*(∏ j ∈ Finset.univ.erase i, A j) = ∏ j, A j :=
    Finset.mul_prod_erase Finset.univ A (Finset.mem_univ i)
  simp_rw [sub_mul,Finset.sum_sub_distrib]
  congr 1
  simp_rw [show ∀ i, m*A i*M*(∏ j ∈ Finset.univ.erase i, A j) = m*(∏ j, A j)*M by
    intro i; rw [show m*A i*M*(∏ j ∈ Finset.univ.erase i, A j) =
      m*(A i*(∏ j ∈ Finset.univ.erase i, A j))*M by ring, he i]]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

 

 theorem ProductTree.hasDerivAt_mean {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) {steps : List (GaussianStep ι)}
    (T : ProductTree ι S steps) {b : ℝ} (hb : OrderedSteps b steps) (a : ℝ)
    (x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => T.mean w φ (x+s • v))
      (T.row w φ v a (x+t • v) -
        a*T.mean w φ (x+t • v)*gaussianHierarchyMean w φ (fun σ => φ σ v) steps (x+t • v)) t := by
  induction T generalizing a b x t with
  | leaf A =>
    apply (gaussianHierarchyMean_hasDerivAt hw φ A [] hb x v t).congr_deriv
    have he : (∑ σ, spinWeight w φ (x+t • v) σ*A σ*φ σ v) =
        ∑ σ, spinWeight w φ (x+t • v) σ*(A σ*φ σ v) := by
      apply Finset.sum_congr rfl
      intro σ _
      ring
    simp only [ProductTree.row,ProductTree.mean,gaussianHierarchyResponse,he]
    change _ = (∑ σ, spinWeight w φ (x+t • v) σ*(A σ*φ σ v))+_ - _
    ring
  | @node st tail k child ih =>
    rcases st with ⟨m,q⟩
    let ν := Measure.pi fun j => gaussianReal 0 (q j)
    let F := gaussianHierarchy w φ tail
    let M := gaussianHierarchyMean w φ (fun σ => φ σ v) tail
    let A (i) := (child i).mean w φ
    let R (i) := (child i).row w φ v m
    have hi := gaussianHierarchy_integrable hw φ tail hb.2.2.2 m q
    have hF := gaussianHierarchy_regular hw φ tail hb.2.2.2 0
    have hM := gaussianHierarchyMean_smooth hw φ (fun σ => φ σ v) tail hb.2.2.2 0
    have hA (i) := (child i).mean_smooth hw φ hb.2.2.2 0
    have hR (i) := (child i).row_smooth hw φ v hb.2.2.2 m 0
    have hD (i) : BddSmooth 0 (fun y => R i y-m*A i y*M y) :=
      (hR i).sub (((hA i).const_mul m).mul hM)
    have hd (i) : HasDerivAt (fun s => shiftedMean ν m F (A i) (x+s • v))
        (shiftedMean ν m F (R i) (x+t • v) - m*shiftedMean ν m F (A i) (x+t • v)*
          shiftedMean ν m F M (x+t • v)) t := by
      obtain ⟨B,hB,hbM⟩ := hM.bound
      obtain ⟨C,hC,hbA⟩ := (hA i).bound
      obtain ⟨D,hD0,hbD⟩ := (hD i).bound
      obtain ⟨K,hK⟩ := hF.1
      have hd := hasDerivAt_shiftedMean hB (add_nonneg hC hD0) hK.continuous hM.continuous
        (hA i).continuous (hD i).continuous
        (fun y s => gaussianHierarchy_hasDerivAt hw φ tail hb.2.2.2 y v s)
        (ih i hb.2.2.2 m) hbM (fun y => (hbA y).trans (by linarith))
        (fun y => (hbD y).trans (by linarith)) hi x t
      apply hd.congr_deriv
      have he : (fun y => R i y-m*A i y*M y) = fun y => R i y-m*(A i y*M y) := by funext y; ring
      rw [he,shiftedMean_sub (hR i) (((hA i).mul hM).const_mul m) (hi (x+t • v)),
        shiftedMean_const_mul]
      ring
    have hp := HasDerivAt.fun_finsetProd (fun i (_ : i ∈ (Finset.univ : Finset (Fin (k+1)))) => hd i)
    apply hp.congr_deriv
    simp only [smul_eq_mul]
    rw [show (∑ i, (∏ j ∈ Finset.univ.erase i, shiftedMean ν m F (A j) (x+t • v))*
        (shiftedMean ν m F (R i) (x+t • v)-m*shiftedMean ν m F (A i) (x+t • v)*shiftedMean ν m F M (x+t • v))) =
      ∑ i, (shiftedMean ν m F (R i) (x+t • v)-m*shiftedMean ν m F (A i) (x+t • v)*shiftedMean ν m F M (x+t • v))*
        (∏ j ∈ Finset.univ.erase i, shiftedMean ν m F (A j) (x+t • v)) by
      apply Finset.sum_congr rfl; intro i _; ring]
    rw [sum_product_fork]
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,ProductTree.row,ProductTree.mean,
      gaussianHierarchyMean]
    change _ = (a-(k+1:ℝ)*m)*(∏ i, shiftedMean ν m F (A i) (x+t • v))*shiftedMean ν m F M (x+t • v) +
      (∑ i, shiftedMean ν m F (R i) (x+t • v)*∏ j ∈ Finset.univ.erase i, shiftedMean ν m F (A j) (x+t • v)) -
      a*(∏ i, shiftedMean ν m F (A i) (x+t • v))*shiftedMean ν m F M (x+t • v)
    ring

end SKFluctuations.Hierarchy

end

end OAI
