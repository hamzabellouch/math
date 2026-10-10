import Mathlib
import OAI.Probability.SKFluctuations.Diagonal

namespace OAI

/-! Weighted Feature Trace Telescope. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 

theorem weighted_feature_trace_telescope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (d : ι → ℝ) {Q a : ℝ}
    (hQ : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = Q)
    (steps : List (GaussianStep ι)) (ha : OrderedSteps a steps) (x : ι → ℝ) :
    (∑ i, d i*(gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1))
      (Pi.single i 1) steps x+a*(gaussianHierarchyMean w φ
        (fun σ => φ σ (Pi.single i 1)) steps x)^2)) =
      Q-∑ i, d i*hierarchyPenalty w φ (Pi.single i 1) a steps x := by
  simp_rw [gaussianHierarchyResponse_mass_telescope hw φ _ steps ha,mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  have he := congrFun (gaussianHierarchyMean_sum hw φ steps ha Finset.univ
    (fun i σ => d i*(φ σ (Pi.single i 1))^2)) x
  simp_rw [hQ,gaussianHierarchyMean_const_mul_ordered hw φ _ steps ha] at he
  rw [gaussianHierarchyMean_const hw φ steps ha Q x] at he
  exact he.symm

 

theorem signedVarianceDerivative_feature_trace {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (d q : ι → ℝ) {Q m : ℝ}
    (hQ : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = Q)
    (tail : List (GaussianStep ι)) (ha : OrderedSteps m tail) (x : ι → ℝ) :
    signedVarianceDerivative m (gaussianHierarchy w φ tail)
      (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail)
      (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1))
        (Pi.single i 1) tail) d q x =
    Q/2-(1/2:ℝ)*varianceTest m (gaussianHierarchy w φ tail)
      (fun y => ∑ i, d i*hierarchyPenalty w φ (Pi.single i 1) m tail y) q x := by
  let ν := Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q i))
  have hi := gaussianHierarchy_integrable hw φ tail ha m (fun i => Real.toNNReal (q i)) x
  have hH (i) := gaussianHierarchyResponse_smooth hw φ (fun σ => φ σ (Pi.single i 1))
    (Pi.single i 1) tail ha 0
  have hG (i) : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ
      (fun σ => φ σ (Pi.single i 1)) tail y)^2) := by
    simpa only [pow_two] using (gaussianHierarchyMean_smooth hw φ _ tail ha 0).mul
      (gaussianHierarchyMean_smooth hw φ _ tail ha 0)
  have hP := BddSmooth.sum Finset.univ (fun i _ =>
    (hierarchyPenalty_smooth hw φ (Pi.single i 1) tail ha 0).const_mul (d i))
  have he := funext fun y => weighted_feature_trace_telescope hw φ d hQ tail ha y
  have hn := congrArg (fun A => shiftedMean ν m (gaussianHierarchy w φ tail) A x) he
  rw [shiftedMean_sum (fun i => ((hH i).add ((hG i).const_mul m)).const_mul (d i)) hi,
    shiftedMean_sub (BddSmooth.const 0 Q) hP hi] at hn
  simp_rw [shiftedMean_const_mul,shiftedMean_add (hH _) ((hG _).const_mul m) hi,
    shiftedMean_const_mul] at hn
  have hc : shiftedMean ν m (gaussianHierarchy w φ tail) (fun _ => Q) x = Q := by
    simp only [shiftedMean,tiltedMean,integral_const_mul]
    exact mul_div_cancel_right₀ Q (partition_pos m hi).ne'
  rw [hc] at hn
  unfold signedVarianceDerivative varianceTest
  change (∑ i, (d i/2)*(_+m*_)) = Q/2-(1/2:ℝ)*shiftedMean ν m _ _ x
  calc
    _ = (1/2:ℝ)*(∑ i, d i*(shiftedMean ν m (gaussianHierarchy w φ tail)
        (gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1) tail) x+
          m*shiftedMean ν m (gaussianHierarchy w φ tail)
            (fun y => (gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail y)^2) x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hn]; ring

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S]

 

theorem rootedHierarchy_signed_variance {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) (q d : Fin (n+1) → ℝ) {l r t : ℝ}
    (hq : ∀ s ∈ Ioo l r, ∀ i, 0 < q i+s*d i) (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (gaussianHierarchy w φ (front ++ (m,fun i => Real.toNNReal (q i+s*d i))::tail)) x)
      (zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (varianceContinuation m (gaussianHierarchy w φ tail) (fun i => q i+t*d i))
          (signedVarianceDerivative m (gaussianHierarchy w φ tail)
            (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail)
            (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1))
              (Pi.single i 1) tail) d (fun i => q i+t*d i))) x) t := by
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  obtain ⟨K,hK⟩ := parametric_signed_variance hC
    (fun i => gaussianHierarchyMean_smooth hw φ _ tail ha 0)
    (fun i => gaussianHierarchyResponse_smooth hw φ _ _ tail ha 0)
    (fun y v s => by
      rw [← gaussianHierarchyMean_feature_components hw φ tail ha v (y+s • v)]
      exact gaussianHierarchy_hasDerivAt hw φ tail ha y v s)
    (fun i y s => gaussianHierarchyMean_hasDerivAt hw φ _ tail ha y _ s) q d hm
  have hh := (((hK l r hq).prefix front hfront).root q₀).derivative t ht x
  have he (s : ℝ) : prefixContinuation front
      (varianceContinuation m (gaussianHierarchy w φ tail) (fun i => q i+s*d i)) =
      gaussianHierarchy w φ (front ++ (m,fun i => Real.toNNReal (q i+s*d i))::tail) :=
    prefixContinuation_hierarchy w φ front ((m,fun i => Real.toNNReal (q i+s*d i))::tail)
  simp_rw [he] at hh
  exact hh

 

theorem rootedHierarchy_corrected_signed_variance {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (q d : Fin (n+1) → ℝ) {Q : ℝ}
    (hQ : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = Q)
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) {l r t : ℝ}
    (hq : ∀ s ∈ Ioo l r, ∀ i, 0 < q i+s*d i) (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    HasDerivAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (gaussianHierarchy w φ (front ++ (m,fun i => Real.toNNReal (q i+s*d i))::tail)) x-Q*s/2)
      (-(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (varianceContinuation m (gaussianHierarchy w φ tail) (fun i => q i+t*d i))
          (varianceTest m (gaussianHierarchy w φ tail)
            (fun y => ∑ i, d i*hierarchyPenalty w φ (Pi.single i 1) m tail y)
            (fun i => q i+t*d i))) x) t := by
  have hh := (rootedHierarchy_signed_variance hw φ front tail hm ha hfront q₀ q d hq ht x).sub
    (((hasDerivAt_id t).const_mul Q).div_const 2)
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  have hi := gaussianHierarchy_integrable hw φ tail ha m (fun i => Real.toNNReal (q i+t*d i))
  have hP₀ := BddSmooth.sum Finset.univ (fun i _ =>
    (hierarchyPenalty_smooth hw φ (Pi.single i 1) tail ha 0).const_mul (d i))
  have hP : BddSmooth 0 (varianceTest m (gaussianHierarchy w φ tail)
      (fun y => ∑ i, d i*hierarchyPenalty w φ (Pi.single i 1) m tail y) (fun i => q i+t*d i)) :=
    hP₀.shiftedMean (gaussianHierarchy_regular hw φ tail ha 0) hi
  have hC : LipschitzWith C (varianceContinuation m (gaussianHierarchy w φ tail) (fun i => q i+t*d i)) :=
    lipschitzWith_shiftedContinuation hF hm hi
  have hPT := prefixTest_smooth0 hC hP front hfront
  have he : signedVarianceDerivative m (gaussianHierarchy w φ tail)
      (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail)
      (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1)) (Pi.single i 1) tail)
      d (fun i => q i+t*d i) = fun y => Q/2+(-(1/2:ℝ))*varianceTest m (gaussianHierarchy w φ tail)
        (fun y => ∑ i, d i*hierarchyPenalty w φ (Pi.single i 1) m tail y) (fun i => q i+t*d i) y := by
    funext y
    rw [signedVarianceDerivative_feature_trace hw φ d _ hQ tail ha y]
    ring
  rw [he] at hh
  have he' := funext (prefixTest_affine hC hP front hfront (Q/2) (-(1/2:ℝ)))
  rw [he',zeroContinuation_affine hPT q₀ (Q/2) (-(1/2:ℝ)) x] at hh
  exact hh.congr_deriv (by ring)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

theorem prefixContinuation_append (front tail : List (GaussianStep ι)) (F : (ι → ℝ) → ℝ) :
    prefixContinuation (front++tail) F = prefixContinuation front (prefixContinuation tail F) := by
  induction front with
  | nil => rfl
  | cons st front ih => simp only [List.cons_append,prefixContinuation,ih]

theorem prefixTest_append (front tail : List (GaussianStep ι)) (F A : (ι → ℝ) → ℝ) :
    prefixTest (front++tail) F A = prefixTest front (prefixContinuation tail F) (prefixTest tail F A) := by
  induction front with
  | nil => rfl
  | cons st front ih => simp only [List.cons_append,prefixTest,prefixContinuation_append,ih]

theorem rootedPrefixTest_const_mul {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (front : List (GaussianStep ι))
    (hf : ∀ st ∈ front, 0 < st.1) (q₀ : ι → ℝ≥0) (c : ℝ) (x : ι → ℝ) :
    zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
      (prefixTest front F (fun y => c*A y)) x =
    c*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i)) (prefixTest front F A) x := by
  have he := funext (prefixTest_affine hF hA front hf 0 c)
  simp only [zero_add] at he
  rw [he]
  have hh := zeroContinuation_affine (prefixTest_smooth0 hF hA front hf) q₀ 0 c x
  simpa only [zero_add] using hh

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq ι]

 

theorem signedPenalty_observed_bound {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (d q : ι → ℝ) {m B : ℝ}
    (hm : 0 < m) (front tail : List (GaussianStep ι)) (ha : OrderedSteps m tail)
    (hf : ∀ st ∈ front, 0 < st.1) (q₀ : ι → ℝ≥0)
    (hB : ∀ σ τ, -B ≤ ∑ i, d i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1)) (x : ι → ℝ) :
    -(1/2:ℝ)*zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
      (prefixTest front (varianceContinuation m (gaussianHierarchy w φ tail) q)
        (varianceTest m (gaussianHierarchy w φ tail)
          (fun y => ∑ i, d i*hierarchyPenalty w φ (Pi.single i 1) m tail y) q)) x ≤ (1-m)*B/2 := by
  obtain ⟨C,hF⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  have hP := BddSmooth.sum Finset.univ (fun i _ =>
    (hierarchyPenalty_smooth hw φ (Pi.single i 1) tail ha 0).const_mul (d i))
  let more := front++[(m,fun i => Real.toNNReal (q i))]
  have hmore : ∀ st ∈ more, 0 < st.1 := by
    intro st hs
    rcases List.mem_append.mp hs with hs|hs
    · exact hf st hs
    · rcases List.mem_singleton.mp hs with rfl
      exact hm
  have hb (y) : -(1/2:ℝ)*(∑ i, d i*hierarchyPenalty w φ (Pi.single i 1) m tail y) ≤ (1-m)*B/2 := by
    rw [← kernelPenalty_weighted_features hw φ (fun i => Pi.single i 1) d tail ha]
    exact kernelPenalty_lower_bound hw φ _ tail ha hB y
  have hh := rootedPrefixTest_le_const hF (hP.const_mul (-(1/2:ℝ))) more hmore hb q₀ x
  rw [rootedPrefixTest_const_mul hF hP more hmore q₀ (-(1/2:ℝ)) x] at hh
  dsimp [more] at hh
  rw [prefixTest_append] at hh
  exact hh

 

theorem rootedHierarchy_signed_derivative_bound {n : ℕ} {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (q d : Fin (n+1) → ℝ) {Q B : ℝ}
    (hQ : ∀ σ, ∑ i, d i*(φ σ (Pi.single i 1))^2 = Q)
    (hB : ∀ σ τ, -B ≤ ∑ i, d i*φ σ (Pi.single i 1)*φ τ (Pi.single i 1))
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hf : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) {l r t : ℝ}
    (hq : ∀ s ∈ Ioo l r, ∀ i, 0 < q i+s*d i) (ht : t ∈ Ioo l r) (x : Fin (n+1) → ℝ) :
    deriv (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
      (gaussianHierarchy w φ (front ++ (m,fun i => Real.toNNReal (q i+s*d i))::tail)) x-Q*s/2) t ≤
      (1-m)*B/2 := by
  rw [(rootedHierarchy_corrected_signed_variance hw φ q d hQ front tail hm ha hf q₀ hq ht x).deriv]
  exact signedPenalty_observed_bound hw φ d _ hm front tail ha hf q₀ hB x

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

 
theorem ExpNormBounded.continuous_integral_diagonal {f : (ι → ℝ) → ℝ}
    (hf : ExpNormBounded f) {ν : Measure (ι → ℝ)} (hν : ExponentialIncrement ν) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => ∫ z, f (p.2+p.1*z) ∂ν) := by
  obtain ⟨C,c,hC,hc,hb⟩ := hf.2
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated
    (bound := fun z => C*Real.exp (c*(‖p.2‖+1))*Real.exp (c*(‖p.1‖+1)*‖z‖))
  · exact Eventually.of_forall fun q =>
      (hf.1.comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [(prod_mem_nhds (Metric.ball_mem_nhds p.1 (by norm_num : (0:ℝ)<1))
      (Metric.ball_mem_nhds p.2 (by norm_num : (0:ℝ)<1)))] with q hq
    refine Eventually.of_forall fun z => ?_
    have hn {a b : ι → ℝ} (h : dist a b < 1) : ‖a‖ ≤ ‖b‖+1 := by
      calc ‖a‖ = ‖a-b+b‖ := by rw [sub_add_cancel]
        _ ≤ ‖a-b‖+‖b‖ := norm_add_le _ _
        _ ≤ ‖b‖+1 := by rw [← dist_eq_norm]; linarith
    change |f (q.2+q.1*z)| ≤ _
    calc
      _ ≤ C*Real.exp (c*‖q.2+q.1*z‖) := hb _
      _ ≤ C*Real.exp (c*((‖p.2‖+1)+(‖p.1‖+1)*‖z‖)) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (hn hq.2)
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hn hq.1) (norm_nonneg _))))
      _ = _ := by rw [mul_add,Real.exp_add]; ring_nf
  · exact (hν (c*(‖p.1‖+1))).const_mul _
  · exact Eventually.of_forall fun z =>
      (hf.1.comp (continuous_snd.add (continuous_fst.mul continuous_const))).continuousAt

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

theorem varianceContinuation_eq_all {F : (ι → ℝ) → ℝ} (hF : Continuous F)
    (m : ℝ) (q x : ι → ℝ) :
    varianceContinuation m F q x = Real.log (∫ z, Real.exp (m*F (x+(fun i => Real.sqrt (q i))*z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1)/m := by
  have hi := integral_diagonalGaussian (fun i => Real.toNNReal (q i))
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  simp only [sqrt_coe_toNNReal] at hi
  exact congrArg (fun z => Real.log z/m) hi.symm

theorem varianceTest_eq_all {F A : (ι → ℝ) → ℝ} (hF : Continuous F) (hA : Continuous A)
    (m : ℝ) (q x : ι → ℝ) :
    varianceTest m F A q x = tiltedMean (Measure.pi fun _ : ι => gaussianReal 0 1) m
      (fun z => F (x+(fun i => Real.sqrt (q i))*z)) (fun z => A (x+(fun i => Real.sqrt (q i))*z)) := by
  have hn := integral_diagonalGaussian (fun i => Real.toNNReal (q i))
    (f := fun z => A (x+z)*Real.exp (m*F (x+z))) (by fun_prop)
  have hd := integral_diagonalGaussian (fun i => Real.toNNReal (q i))
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  simp only [sqrt_coe_toNNReal] at hn hd
  exact congrArg₂ (· / ·) hn.symm hd.symm

theorem varianceContinuation_continuous {F : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => varianceContinuation m F p.1 p.2) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have he := ExpNormBounded.exp_lipschitz hF m
  have hd := he.continuous_integral_diagonal hν
  have hc : Continuous (fun p : (ι → ℝ) × (ι → ℝ) => Real.log
      (∫ z, Real.exp (m*F (p.2+(fun i => Real.sqrt (p.1 i))*z)) ∂ν)/m) := by
    exact ((hd.log (fun q => (partition_pos m (he.diagonal_integrable hν q.2 q.1)).ne')).div_const m).comp
      ((continuous_pi fun i => Real.continuous_sqrt.comp ((continuous_apply i).comp continuous_fst)).prodMk continuous_snd)
  exact hc.congr fun p => (varianceContinuation_eq_all hF.continuous m p.1 p.2).symm

theorem varianceTest_continuous {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (m : ℝ) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => varianceTest m F A p.1 p.2) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have he := ExpNormBounded.exp_lipschitz hF m
  have hn := (he.bdd_mul hA).continuous_integral_diagonal hν
  have hd := he.continuous_integral_diagonal hν
  have hc : Continuous (fun p : (ι → ℝ) × (ι → ℝ) =>
      tiltedMean ν m (fun z => F (p.2+(fun i => Real.sqrt (p.1 i))*z))
        (fun z => A (p.2+(fun i => Real.sqrt (p.1 i))*z))) := by
    exact (hn.div hd (fun q => (partition_pos m (he.diagonal_integrable hν q.2 q.1)).ne')).comp
      ((continuous_pi fun i => Real.continuous_sqrt.comp ((continuous_apply i).comp continuous_fst)).prodMk continuous_snd)
  exact hc.congr fun p => (varianceTest_eq_all hF.continuous hA.continuous m p.1 p.2).symm

theorem parametric_continuous_variance {F A : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) {m : ℝ} (hm : 0 < m)
    {q : ℝ → (ι → ℝ)} (hq : Continuous q) :
    ∃ K, ParametricContinuous univ C K (fun t => varianceContinuation m F (q t))
      (fun t => varianceTest m F A (q t)) := by
  obtain ⟨K,hK,hb⟩ := hA.bound
  have hi (t : ℝ) (x : ι → ℝ) :=
    (exponentialIncrement_gaussian (fun i => Real.toNNReal (q t i))).integrable_shift hF m x
  exact ⟨K,hK,fun t _ => lipschitzWith_shiftedContinuation hF hm (hi t),
    fun t _ => continuous_shiftedMean hF hA.continuous hK hb (hi t),
    fun t _ x => abs_tiltedMean_le (hA.continuous.comp (continuous_const.add continuous_id)).measurable
      (hi t x) (fun z => hb (x+z)),
    fun x => ((varianceContinuation_continuous hF m).comp (hq.prodMk continuous_const)).continuousOn,
    fun x => ((varianceTest_continuous hF hA m).comp (hq.prodMk continuous_const)).continuousOn⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal
variable {ι P : Type*} [Fintype ι] [TopologicalSpace P] [FirstCountableTopology P]

 

theorem dynamic_diagonalPartition_continuous {F A : P → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ p y, |A p y| ≤ K) (m : ℝ) {a x : P → (ι → ℝ)} (ha : Continuous a) (hx : Continuous x) :
    Continuous (fun p => ∫ z, A p (x p+a p*z)*Real.exp (m*F p (x p+a p*z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1) := by
  let ν := Measure.pi fun _ : ι => gaussianReal 0 1
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := |F p (x p)|+1
  let Q := ‖a p‖+1
  have hcbase : Continuous (fun q => F q (x q)) := hcF.comp (continuous_id.prodMk hx)
  have hbase : ∀ᶠ q in 𝓝 p, |F q (x q)| < B := hcbase.abs.continuousAt.eventually
    (eventually_lt_nhds (by dsimp [B]; linarith))
  have hscale : ∀ᶠ q in 𝓝 p, ‖a q‖ < Q := ha.norm.continuousAt.eventually
    (eventually_lt_nhds (by dsimp [Q]; linarith))
  apply continuousAt_of_dominated
    (bound := fun z => K*Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖))
  · exact Eventually.of_forall fun q => by
      have hmap : Continuous (fun z : ι → ℝ => (q,x q+a q*z)) := by fun_prop
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).aestronglyMeasurable
  · filter_upwards [hbase,hscale] with q hq hq'
    exact Eventually.of_forall fun z => by
      have hK : 0 ≤ K := (abs_nonneg (A q (x q))).trans (hb q (x q))
      have hdiff : |F q (x q+a q*z)-F q (x q)| ≤ (C:ℝ)*‖a q‖*‖z‖ := by
        have hh := (hF q).dist_le_mul (x q+a q*z) (x q)
        simp only [dist_eq_norm,add_sub_cancel_left,Real.norm_eq_abs] at hh
        exact hh.trans ((mul_le_mul_of_nonneg_left (norm_mul_le (a q) z) C.coe_nonneg).trans_eq (by ring))
      have hale : |F q (x q+a q*z)| ≤ B+(C:ℝ)*Q*‖z‖ := by
        have hh := abs_add_le (F q (x q+a q*z)-F q (x q)) (F q (x q))
        rw [sub_add_cancel] at hh
        have hcomp : (C:ℝ)*‖a q‖*‖z‖ ≤ (C:ℝ)*Q*‖z‖ := by gcongr
        linarith
      have hexp : Real.exp (m*F q (x q+a q*z)) ≤ Real.exp (|m| *B)*Real.exp (|m| *C*Q*‖z‖) := by
        rw [← Real.exp_add,Real.exp_le_exp]
        have h1 := (le_abs_self (m*F q (x q+a q*z))).trans_eq (abs_mul m _)
        have h2 := mul_le_mul_of_nonneg_left hale (abs_nonneg m)
        nlinarith
      change |A q (x q+a q*z)*Real.exp (m*F q (x q+a q*z))| ≤ _
      rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul (hb q _) hexp (Real.exp_nonneg _) hK).trans_eq (by ring)
  · exact (hν (|m| *C*Q)).const_mul _
  · exact Eventually.of_forall fun z => by
      have hmap : Continuous (fun q => (q,x q+a q*z)) := continuous_id.prodMk (hx.add (ha.mul continuous_const))
      exact ((hcA.comp hmap).mul (((hcF.comp hmap).const_mul m).rexp)).continuousAt

theorem dynamic_varianceTest_continuous {F A : P → (ι → ℝ) → ℝ} {C : ℝ≥0} {K : ℝ}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (hcA : Continuous (fun p : P × (ι → ℝ) => A p.1 p.2))
    (hb : ∀ p y, |A p y| ≤ K) (m : ℝ) {q x : P → (ι → ℝ)} (hq : Continuous q) (hx : Continuous x) :
    Continuous (fun p => varianceTest m (F p) (A p) (q p) (x p)) := by
  have hs : Continuous (fun p i => Real.sqrt (q p i)) := continuous_pi fun i =>
    Real.continuous_sqrt.comp ((continuous_apply i).comp hq)
  have hn := dynamic_diagonalPartition_continuous hF hcF hcA hb m hs hx
  have hd := dynamic_diagonalPartition_continuous (A := fun _ _ => 1) hF hcF continuous_const
    (fun _ _ => le_refl |(1:ℝ)|) m hs hx
  simp only [one_mul] at hd
  have hh := hn.div hd (fun p => (partition_pos m
    ((ExpNormBounded.exp_lipschitz (hF p) m).diagonal_integrable
      (exponentialIncrement_gaussian (fun _ : ι => 1)) (x p) _)).ne')
  exact hh.congr fun p => (varianceTest_eq_all (hF p).continuous
    (hcA.comp (continuous_const.prodMk continuous_id)) m (q p) (x p)).symm

theorem dynamic_varianceContinuation_continuous {F : P → (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : ∀ p, LipschitzWith C (F p))
    (hcF : Continuous (fun p : P × (ι → ℝ) => F p.1 p.2))
    (m : ℝ) {q x : P → (ι → ℝ)} (hq : Continuous q) (hx : Continuous x) :
    Continuous (fun p => varianceContinuation m (F p) (q p) (x p)) := by
  have hs : Continuous (fun p i => Real.sqrt (q p i)) := continuous_pi fun i =>
    Real.continuous_sqrt.comp ((continuous_apply i).comp hq)
  have hd := dynamic_diagonalPartition_continuous (A := fun _ _ => 1) hF hcF continuous_const
    (fun _ _ => le_refl |(1:ℝ)|) m hs hx
  simp only [one_mul] at hd
  have hh := (hd.log (fun p => (partition_pos m
    ((ExpNormBounded.exp_lipschitz (hF p) m).diagonal_integrable
      (exponentialIncrement_gaussian (fun _ : ι => 1)) (x p) _)).ne')).div_const m
  exact hh.congr fun p => (varianceContinuation_eq_all (hF p).continuous m (q p) (x p)).symm

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι P S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

def covarianceSteps (ss : List (ℝ × (P → ι → ℝ))) (p : P) : List (GaussianStep ι) :=
  ss.map fun s => (s.1, fun i => Real.toNNReal (s.2 p i))

omit [Fintype ι] in
@[simp] theorem covarianceSteps_nil (p : P) : covarianceSteps ([] : List (ℝ × (P → ι → ℝ))) p = [] := rfl
omit [Fintype ι] in
@[simp] theorem covarianceSteps_cons (st : ℝ × (P → ι → ℝ)) (ss : List (ℝ × (P → ι → ℝ))) (p : P) :
    covarianceSteps (st::ss) p = (st.1,fun i => Real.toNNReal (st.2 p i))::covarianceSteps ss p := rfl

omit [Nonempty S] in
theorem covarianceFamily_lipschitz {w : S → ℝ}
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {C : ℝ≥0} (hF : LipschitzWith C (spinLogPartition w φ))
    (ss : List (ℝ × (P → ι → ℝ))) (hm : ∀ st ∈ ss, 0 < st.1) (p : P) :
    LipschitzWith C (gaussianHierarchy w φ (covarianceSteps ss p)) := by
  induction ss with
  | nil => exact hF
  | cons st ss ih =>
    have htail := ih (fun s hs => hm s (List.mem_cons_of_mem _ hs))
    exact lipschitzWith_shiftedContinuation htail (hm st (List.mem_cons_self))
      (fun x => (exponentialIncrement_gaussian _).integrable_shift htail st.1 x)

variable [TopologicalSpace P] [FirstCountableTopology P]

theorem covarianceFamily_potential_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ss : List (ℝ × (P → ι → ℝ)))
    (hm : ∀ st ∈ ss, 0 < st.1) (hc : ∀ st ∈ ss, Continuous st.2) :
    Continuous (fun p : P × (ι → ℝ) => gaussianHierarchy w φ (covarianceSteps ss p.1) p.2) := by
  obtain ⟨C,hF⟩ := (potentialRegularity_spinLogPartition hw φ 0).1
  induction ss with
  | nil => exact hF.continuous.comp continuous_snd
  | cons st ss ih =>
    have hm' : ∀ s ∈ ss, 0 < s.1 := fun s hs => hm s (List.mem_cons_of_mem _ hs)
    have hc' : ∀ s ∈ ss, Continuous s.2 := fun s hs => hc s (List.mem_cons_of_mem _ hs)
    have ht := ih hm' hc'
    exact dynamic_varianceContinuation_continuous
      (fun p : P × (ι → ℝ) => covarianceFamily_lipschitz φ hF ss hm' p.1)
      (ht.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)) st.1
      ((hc st List.mem_cons_self).comp continuous_fst) continuous_snd

theorem covarianceFamily_mean_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (ss : List (ℝ × (P → ι → ℝ)))
    {a : ℝ} (ha : ∀ p, OrderedSteps a (covarianceSteps ss p))
    (hm : ∀ st ∈ ss, 0 < st.1) (hc : ∀ st ∈ ss, Continuous st.2) :
    Continuous (fun p : P × (ι → ℝ) => gaussianHierarchyMean w φ A (covarianceSteps ss p.1) p.2) := by
  obtain ⟨C,hF⟩ := (potentialRegularity_spinLogPartition hw φ 0).1
  let K := ∑ σ, |A σ|
  have hK : ∀ σ, |A σ| ≤ K := fun σ => Finset.single_le_sum (fun τ _ => abs_nonneg (A τ)) (Finset.mem_univ σ)
  induction ss generalizing a with
  | nil =>
    exact (gaussianHierarchyMean_smooth hw φ A [] (a := 0) ⟨le_rfl,by norm_num⟩ 0).continuous.comp continuous_snd
  | cons st ss ih =>
    have hm' : ∀ s ∈ ss, 0 < s.1 := fun s hs => hm s (List.mem_cons_of_mem _ hs)
    have hc' : ∀ s ∈ ss, Continuous s.2 := fun s hs => hc s (List.mem_cons_of_mem _ hs)
    have ha' : ∀ p, OrderedSteps st.1 (covarianceSteps ss p) := fun p => (ha p).2.2.2
    have ht := ih ha' hm' hc'
    have hFc := covarianceFamily_potential_continuous hw φ ss hm' hc'
    exact dynamic_varianceTest_continuous
      (fun p : P × (ι → ℝ) => covarianceFamily_lipschitz φ hF ss hm' p.1)
      (hFc.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (ht.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      (fun p y => gaussianHierarchyMean_abs_le hw φ hK _ (ha' p.1) y) st.1
      ((hc st List.mem_cons_self).comp continuous_fst) continuous_snd

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι P S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

theorem gaussianHierarchyHessian_abs_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) {K : ℝ}
    (hK : ∀ σ, |φ σ v| ≤ K) (ss : List (GaussianStep ι)) {a : ℝ}
    (ha : OrderedSteps a ss) (x : ι → ℝ) :
    |gaussianHierarchyHessian w φ ss x v v| ≤ K^2 := by
  rw [abs_of_nonneg (gaussianHierarchyHessian_nonneg hw φ ss ha x v)]
  have hb : ∀ σ, |(φ σ v)^2| ≤ K^2 := by
    intro σ
    rw [abs_sq]
    have he := (sq_le_sq₀ (abs_nonneg (φ σ v)) ((abs_nonneg _).trans (hK σ))).mpr (hK σ)
    simpa only [sq_abs] using he
  have hM := gaussianHierarchyMean_abs_le hw φ hb ss ha x
  have hU := (gaussianHierarchyHessian_bounds hw φ ss ha x v).2
  have hL := le_abs_self (gaussianHierarchyMean w φ (fun σ => (φ σ v)^2) ss x)
  nlinarith [sq_nonneg (gaussianHierarchyMean w φ (fun σ => φ σ v) ss x)]

variable [TopologicalSpace P] [FirstCountableTopology P]

 

theorem covarianceFamily_hessian_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (ss : List (ℝ × (P → ι → ℝ)))
    {a : ℝ} (ha : ∀ p, OrderedSteps a (covarianceSteps ss p))
    (hm : ∀ st ∈ ss, 0 < st.1) (hc : ∀ st ∈ ss, Continuous st.2) :
    Continuous (fun p : P × (ι → ℝ) => gaussianHierarchyHessian w φ (covarianceSteps ss p.1) p.2 v v) := by
  obtain ⟨C,hF⟩ := (potentialRegularity_spinLogPartition hw φ 0).1
  let K := ∑ σ, |φ σ v|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun σ _ => abs_nonneg _)
  have hb : ∀ σ, |φ σ v| ≤ K := fun σ => Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ v)) (Finset.mem_univ σ)
  induction ss generalizing a with
  | nil =>
    exact (gaussianHierarchyResponse_smooth hw φ (fun σ => φ σ v) v [] (a := 0)
      ⟨le_rfl,by norm_num⟩ 0).continuous.comp continuous_snd
  | cons st ss ih =>
    have hm' : ∀ s ∈ ss, 0 < s.1 := fun s hs => hm s (List.mem_cons_of_mem _ hs)
    have hc' : ∀ s ∈ ss, Continuous s.2 := fun s hs => hc s (List.mem_cons_of_mem _ hs)
    have ha' : ∀ p, OrderedSteps st.1 (covarianceSteps ss p) := fun p => (ha p).2.2.2
    have hch := ih ha' hm' hc'
    have hcg := covarianceFamily_mean_continuous hw φ (fun σ => φ σ v) ss ha' hm' hc'
    have hcout := covarianceFamily_mean_continuous hw φ (fun σ => φ σ v) (st::ss) ha hm hc
    have hFc := covarianceFamily_potential_continuous hw φ ss hm' hc'
    have h1 : Continuous (fun p : P × (ι → ℝ) => varianceTest st.1
        (gaussianHierarchy w φ (covarianceSteps ss p.1))
        (fun y => gaussianHierarchyHessian w φ (covarianceSteps ss p.1) y v v) (st.2 p.1) p.2) :=
      dynamic_varianceTest_continuous
        (fun p : P × (ι → ℝ) => covarianceFamily_lipschitz φ hF ss hm' p.1)
        (hFc.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
        (hch.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
        (fun p y => gaussianHierarchyHessian_abs_le hw φ v hb _ (ha' p.1) y) st.1
        ((hc st List.mem_cons_self).comp continuous_fst) continuous_snd
    have h2 : Continuous (fun p : P × (ι → ℝ) => varianceTest st.1
        (gaussianHierarchy w φ (covarianceSteps ss p.1))
        (fun y => (gaussianHierarchyMean w φ (fun σ => φ σ v) (covarianceSteps ss p.1) y)^2) (st.2 p.1) p.2) :=
      dynamic_varianceTest_continuous (K := K^2)
        (fun p : P × (ι → ℝ) => covarianceFamily_lipschitz φ hF ss hm' p.1)
        (hFc.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
        ((hcg.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).pow 2)
        (fun p y => by
          have h := gaussianHierarchyMean_abs_le hw φ hb _ (ha' p.1) y
          rw [abs_sq]
          have he := (sq_le_sq₀ (abs_nonneg _) hK).mpr h
          simpa only [sq_abs] using he) st.1
        ((hc st List.mem_cons_self).comp continuous_fst) continuous_snd
    convert h1.add ((h2.sub (hcout.pow 2)).const_mul st.1) using 1
    funext p
    simp only [gaussianHierarchyHessian,gaussianHierarchyResponse,covarianceSteps_cons,varianceTest,
      pow_two,Pi.add_apply,Pi.sub_apply,Pi.mul_apply]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

abbrev SignedStep (ι : Type*) := ℝ × (ι → ℝ) × (ι → ℝ)

def affineCovariances (ss : List (SignedStep ι)) : List (ℝ × (ℝ → ι → ℝ)) :=
  ss.map fun st => (st.1, fun t i => st.2.1 i+t*st.2.2 i)

def affineSteps (ss : List (SignedStep ι)) (t : ℝ) : List (GaussianStep ι) :=
  covarianceSteps (affineCovariances ss) t

omit [Fintype ι] in
@[simp] theorem affineSteps_nil (t : ℝ) : affineSteps ([] : List (SignedStep ι)) t = [] := rfl
omit [Fintype ι] in
@[simp] theorem affineSteps_cons (st : SignedStep ι) (ss : List (SignedStep ι)) (t : ℝ) :
    affineSteps (st::ss) t = (st.1,fun i => Real.toNNReal (st.2.1 i+t*st.2.2 i))::affineSteps ss t := rfl

omit [Fintype ι] in
theorem affineSteps_ordered (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) (t : ℝ) : OrderedSteps a (affineSteps ss t) := by
  induction ss generalizing a with
  | nil => exact ha
  | cons st ss ih => exact ⟨ha.1,ha.2.1,ha.2.2.1,ih ha.2.2.2⟩

omit [Fintype ι] in
theorem affineCovariances_positive (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) : ∀ st ∈ affineCovariances ss, 0 < st.1 := by
  induction ss generalizing a with
  | nil => simp [affineCovariances]
  | cons st ss ih =>
    intro s hs
    change s ∈ (st.1,fun t i => st.2.1 i+t*st.2.2 i)::affineCovariances ss at hs
    rcases List.mem_cons.mp hs with rfl|hs
    · exact ha.2.2.1
    · exact ih ha.2.2.2 s hs

omit [Fintype ι] in
theorem affineCovariances_continuous (ss : List (SignedStep ι)) :
    ∀ st ∈ affineCovariances ss, Continuous st.2 := by
  intro st hs
  change st ∈ ss.map (fun st => (st.1,fun t i => st.2.1 i+t*st.2.2 i)) at hs
  simp only [List.mem_map] at hs
  obtain ⟨s,_,hst⟩ := hs
  subst st
  exact continuous_pi fun i => continuous_const.add (continuous_id.mul continuous_const)

theorem affineHierarchy_lipschitz {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) : ∃ C, ∀ (ss : List (SignedStep ι)) {a : ℝ},
    OrderedSteps a (affineSteps ss 0) → ∀ t, LipschitzWith C (gaussianHierarchy w φ (affineSteps ss t)) := by
  obtain ⟨C,hF⟩ := (potentialRegularity_spinLogPartition hw φ 0).1
  exact ⟨C,fun ss _ ha t => covarianceFamily_lipschitz φ hF _ (affineCovariances_positive ss ha) t⟩

theorem affineHierarchy_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) :
    Continuous (fun p : ℝ × (ι → ℝ) => gaussianHierarchy w φ (affineSteps ss p.1) p.2) :=
  covarianceFamily_potential_continuous hw φ _ (affineCovariances_positive ss ha) (affineCovariances_continuous ss)

theorem affineHierarchyMean_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) :
    Continuous (fun p : ℝ × (ι → ℝ) => gaussianHierarchyMean w φ A (affineSteps ss p.1) p.2) :=
  covarianceFamily_mean_continuous hw φ A _ (affineSteps_ordered ss ha)
    (affineCovariances_positive ss ha) (affineCovariances_continuous ss)

theorem affineHierarchyMean_absBounded {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) :
    AbsBounded (fun p : ℝ × (ι → ℝ) => gaussianHierarchyMean w φ A (affineSteps ss p.1) p.2) := by
  refine ⟨∑ σ, |A σ|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),fun p => ?_⟩
  exact gaussianHierarchyMean_abs_le hw φ
    (fun σ => Finset.single_le_sum (fun τ _ => abs_nonneg (A τ)) (Finset.mem_univ σ))
    _ (affineSteps_ordered ss ha p.1) p.2

theorem affineHierarchyHessian_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) :
    Continuous (fun p : ℝ × (ι → ℝ) => gaussianHierarchyHessian w φ (affineSteps ss p.1) p.2 v v) :=
  covarianceFamily_hessian_continuous hw φ v _ (affineSteps_ordered ss ha)
    (affineCovariances_positive ss ha) (affineCovariances_continuous ss)

theorem affineHierarchyHessian_absBounded {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) (ss : List (SignedStep ι)) {a : ℝ}
    (ha : OrderedSteps a (affineSteps ss 0)) :
    AbsBounded (fun p : ℝ × (ι → ℝ) => gaussianHierarchyHessian w φ (affineSteps ss p.1) p.2 v v) := by
  refine ⟨(∑ σ, |φ σ v|)^2,sq_nonneg _,fun p => ?_⟩
  exact gaussianHierarchyHessian_abs_le hw φ v
    (fun σ => Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ v)) (Finset.mem_univ σ))
    _ (affineSteps_ordered ss ha p.1) p.2

end SKFluctuations.Hierarchy

end

end OAI
