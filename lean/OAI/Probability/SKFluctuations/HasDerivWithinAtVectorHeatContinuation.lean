import Mathlib
import OAI.Probability.SKFluctuations.EventuallyNatPos
import OAI.Probability.SKFluctuations.LineDerivativesSignEquivVolume

namespace OAI

/-! Has Deriv Within At Vector Heat Continuation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Hierarchy Filter
open scoped Topology NNReal BigOperators

 

theorem hasDerivWithinAt_vector_heat_continuation {n : ℕ}
    {F : (Fin (n+1) → ℝ) → ℝ} {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v))
      (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1))
      (H i (x+t • Pi.single i 1)) t)
    {m t : ℝ} (hm : m ≠ 0) (ht : 0 ≤ t) (x : Fin (n+1) → ℝ) :
    HasDerivWithinAt (fun s => Real.log (∫ z, Real.exp (m*F (x+Real.sqrt s • z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))/m)
      ((1/2:ℝ)*((∑ i, tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+Real.sqrt t • z)) (fun z => H i (x+Real.sqrt t • z))) + m *
        (∑ i, tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+Real.sqrt t • z)) (fun z => (G i (x+Real.sqrt t • z))^2)))) (Set.Ici 0) t := by
  let P := fun y => Real.exp (m*F y)
  let P₁ := fun i y => m*G i y*P y
  let P₂ := fun i y => (m*H i y + m^2*(G i y)^2)*P y
  let ν := Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)
  have hν : ExponentialIncrement ν := exponentialIncrement_gaussian (fun _ => 1)
  have hP : ExpNormBounded P := ExpNormBounded.exp_lipschitz hF m
  have hB₁ (i) : BddSmooth 0 (fun y => m*G i y) := (hG i).const_mul m
  have hB₂ (i) : BddSmooth 0 (fun y => m*H i y + m^2*(G i y)^2) := by
    simpa only [pow_two] using ((hH i).const_mul m).add (((hG i).mul (hG i)).const_mul (m*m))
  have hdP (y v : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P (y+r • v)) (∑ i, v i*P₁ i (y+s • v)) s := by
    apply (((hd y v s).const_mul m).exp).congr_deriv
    dsimp [P₁,P]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdP₁ (i) (y : Fin (n+1) → ℝ) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P₁ i (y+r • Pi.single i 1))
        (P₂ i (y+s • Pi.single i 1)) s := by
    have hp := hdP y (Pi.single i 1) s
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hp
    apply (((hd₁ i y s).const_mul m).mul hp).congr_deriv
    dsimp [P₂,P₁]
    ring
  have h := hasDerivWithinAt_gaussian_vector_variance hP (fun i => hP.bdd_mul (hB₁ i))
    (fun i => hP.bdd_mul (hB₂ i)) hdP hdP₁ x ht
  have hp : 0 < ∫ z, P (x+Real.sqrt t • z) ∂ν := partition_pos m (hP.affine_integrable hν x _)
  have hGs (i) : BddSmooth 0 (fun y => (G i y)^2) := by
    simpa only [pow_two] using (hG i).mul (hG i)
  have hiH (i) : Integrable (fun z => H i (x+Real.sqrt t • z)*P (x+Real.sqrt t • z)) ν :=
    (hP.bdd_mul (hH i)).affine_integrable hν x _
  have hiGs (i) : Integrable (fun z => (G i (x+Real.sqrt t • z))^2*P (x+Real.sqrt t • z)) ν :=
    (hP.bdd_mul (hGs i)).affine_integrable hν x _
  have he (i) : (∫ z, P₂ i (x+Real.sqrt t • z) ∂ν) =
      m*(∫ z, H i (x+Real.sqrt t • z)*P (x+Real.sqrt t • z) ∂ν) +
      m^2*(∫ z, (G i (x+Real.sqrt t • z))^2*P (x+Real.sqrt t • z) ∂ν) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hiH i).const_mul m) ((hiGs i).const_mul (m^2))]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by dsimp [P₂]; ring
  apply ((h.log hp.ne').div_const m).congr_deriv
  change ((1/2:ℝ)*(∫ z, ∑ i, P₂ i (x+Real.sqrt t • z) ∂ν) /
    (∫ z, P (x+Real.sqrt t • z) ∂ν))/m = _
  rw [integral_finsetSum _ (fun i _ => (hP.bdd_mul (hB₂ i)).affine_integrable hν x _)]
  change ((1/2:ℝ)*(∑ i, ∫ z, P₂ i (x+Real.sqrt t • z) ∂ν) /
    (∫ z, P (x+Real.sqrt t • z) ∂ν))/m = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [tiltedMean, ← Finset.sum_div]
  dsimp [P,ν] at *
  field_simp

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 

theorem gaussianHierarchyMean_sum {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {κ : Type*} (s : Finset κ) (A : κ → S → ℝ) :
    gaussianHierarchyMean w φ (fun σ => ∑ i ∈ s, A i σ) steps =
      fun x => ∑ i ∈ s, gaussianHierarchyMean w φ (A i) steps x := by
  induction steps generalizing a with
  | nil =>
    funext x
    simp only [gaussianHierarchyMean, Finset.mul_sum]
    exact Finset.sum_comm
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    funext x
    simp only [gaussianHierarchyMean, shiftedMean, tiltedMean, ih ha.2.2.2]
    rw [← Finset.sum_div, ← integral_finsetSum s]
    · congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun z => Finset.sum_mul s _ _
    · intro i _
      obtain ⟨B,_,hb⟩ := (gaussianHierarchyMean_smooth hw φ (A i) tail ha.2.2.2 0).bound
      exact integrable_weighted (gaussianHierarchy_integrable hw φ tail ha.2.2.2 m q x)
        ((gaussianHierarchyMean_smooth hw φ (A i) tail ha.2.2.2 0).continuous.comp
          (continuous_const.add continuous_id)).measurable (fun z => hb _)

omit [Nonempty S] in
theorem gaussianHierarchyMean_const_mul_ordered {w : S → ℝ} (_hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : S → ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) :
    gaussianHierarchyMean w φ (fun σ => c*A σ) steps =
      fun x => c*gaussianHierarchyMean w φ A steps x := by
  induction steps generalizing a with
  | nil =>
    funext x
    simp only [gaussianHierarchyMean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    funext x
    simp only [gaussianHierarchyMean, shiftedMean, tiltedMean, ih ha.2.2.2]
    simp_rw [mul_assoc, integral_const_mul, mul_div_assoc]

 

theorem gaussianHierarchyMean_feature_components [DecidableEq ι] {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (v x : ι → ℝ) :
    gaussianHierarchyMean w φ (fun σ => φ σ v) steps x =
      ∑ i, v i*gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) steps x := by
  classical
  have hv : v = ∑ i, v i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  have hφ : (fun σ => φ σ v) = fun σ => ∑ i, v i*φ σ (Pi.single i 1) := by
    funext σ
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hφ, gaussianHierarchyMean_sum hw φ steps ha Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussianHierarchyMean_const_mul_ordered hw φ _ steps ha]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal BigOperators

 

theorem gaussianHierarchy_hasDerivWithinAt_clock {n : ℕ} {S : Type*}
    [Fintype S] [Nonempty S] {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep (Fin (n+1))))
    {a : ℝ} (ha : OrderedSteps a steps) {m t : ℝ} (hm : m ≠ 0) (ht : 0 ≤ t)
    (x : Fin (n+1) → ℝ) :
    HasDerivWithinAt (fun s => Real.log (∫ z, Real.exp (m*gaussianHierarchy w φ steps (x+Real.sqrt s • z))
        ∂Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))/m)
      ((1/2:ℝ)*((∑ i, tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => gaussianHierarchy w φ steps (x+Real.sqrt t • z))
          (fun z => gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1))
            (Pi.single i 1) steps (x+Real.sqrt t • z))) + m *
        (∑ i, tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => gaussianHierarchy w φ steps (x+Real.sqrt t • z))
          (fun z => (gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1))
            steps (x+Real.sqrt t • z))^2)))) (Ici 0) t := by
  obtain ⟨C, hC⟩ := (gaussianHierarchy_regular hw φ steps ha 0).1
  apply GaussianCalculus.hasDerivWithinAt_vector_heat_continuation hC
    (fun i => gaussianHierarchyMean_smooth hw φ _ steps ha 0)
    (fun i => gaussianHierarchyResponse_smooth hw φ _ _ steps ha 0) _ _ hm ht
  · intro y v s
    rw [← gaussianHierarchyMean_feature_components hw φ steps ha v (y+s • v)]
    exact gaussianHierarchy_hasDerivAt hw φ steps ha y v s
  · intro i y s
    exact gaussianHierarchyMean_hasDerivAt hw φ _ steps ha y _ s

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

 

theorem hasDerivAt_continuation_local [IsProbabilityMeasure μ]
    {F D : ℝ → Ω → ℝ} {l r t K m : ℝ}
    (ht : t ∈ Ioo l r) (hK : 0 ≤ K) (hm : m ≠ 0)
    (hF : ∀ s ∈ Ioo l r, Measurable (F s)) (hD : Measurable (D t))
    (hd : ∀ s ∈ Ioo l r, ∀ z, HasDerivAt (fun q => F q z) (D s z) s)
    (hb : ∀ s ∈ Ioo l r, ∀ z, |D s z| ≤ K)
    (hi : Integrable (fun z => Real.exp (m*F t z)) μ) :
    HasDerivAt (continuation μ m F) (tiltedMean μ m (F t) (D t)) t := by
  let ρ := min 1 (min (t-l) (r-t)) / 2
  have hρ : 0 < ρ := by
    have hl : 0 < t-l := sub_pos.mpr ht.1
    have hr : 0 < r-t := sub_pos.mpr ht.2
    dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by dsimp [ρ]; have := min_le_left (1:ℝ) (min (t-l) (r-t)); linarith
  have hball : Metric.ball t ρ ⊆ Ioo l r := by
    intro s hs
    have hs' : |s-t| < ρ := Metric.mem_ball.mp hs
    have hρl : ρ ≤ t-l := by dsimp [ρ]; have := (min_le_right (1:ℝ) (min (t-l) (r-t))).trans (min_le_left _ _); linarith [ht.1]
    have hρr : ρ ≤ r-t := by dsimp [ρ]; have := (min_le_right (1:ℝ) (min (t-l) (r-t))).trans (min_le_right _ _); linarith [ht.2]
    have hs'' := abs_lt.mp hs'
    constructor <;> linarith
  have hLip (s) (hs : s ∈ Metric.ball t ρ) (z : Ω) : |F s z-F t z| ≤ K := by
    have hL : LipschitzOnWith ⟨K,hK⟩ (fun q => F q z) (Ioo l r) :=
      (convex_Ioo l r).lipschitzOnWith_of_nnnorm_deriv_le
        (fun q hq => (hd q hq z).differentiableAt)
        (fun q hq => by
          change ‖deriv (fun q => F q z) q‖ ≤ K
          rw [(hd q hq z).deriv, Real.norm_eq_abs]
          exact hb q hq z)
    have hh := hL.dist_le_mul s (hball hs) t ht
    change |F s z-F t z| ≤ K*|s-t| at hh
    apply hh.trans
    have hst : |s-t| ≤ 1 := (Metric.mem_ball.mp hs).le.trans hρ1
    simpa only [Real.dist_eq, mul_one] using mul_le_mul_of_nonneg_left hst hK
  have hExp (s) (hs : s ∈ Metric.ball t ρ) (z : Ω) :
      Real.exp (m*F s z) ≤ Real.exp (|m| *K)*Real.exp (m*F t z) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_left (hLip s hs z) (abs_nonneg m)
    have h' := le_abs_self (m*(F s z-F t z))
    rw [abs_mul] at h'
    nlinarith
  have hP : HasDerivAt (fun s => ∫ z, Real.exp (m*F s z) ∂μ)
      (∫ z, (m*D t z)*Real.exp (m*F t z) ∂μ) t := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Metric.ball t ρ) (bound := fun z => (|m| *K*Real.exp (|m| *K))*Real.exp (m*F t z)))
      (Metric.ball_mem_nhds t hρ) _ hi _ _ _ _ |>.2
    · filter_upwards [Metric.ball_mem_nhds t hρ] with s hs
      exact (((hF s (hball hs)).const_mul m).exp).aestronglyMeasurable
    · exact ((hD.const_mul m).mul (((hF t ht).const_mul m).exp)).aestronglyMeasurable
    · exact Eventually.of_forall fun z s hs => by
        change |m*D s z*Real.exp (m*F s z)| ≤ _
        rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
        calc
          _ ≤ (|m| *K)*(Real.exp (|m| *K)*Real.exp (m*F t z)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hb s (hball hs) z) (abs_nonneg m))
              (hExp s hs z) (Real.exp_nonneg _) (mul_nonneg (abs_nonneg m) hK)
          _ = _ := by ring
    · exact hi.const_mul _
    · exact Eventually.of_forall fun z s hs =>
        (((hd s (hball hs) z).const_mul m).exp).congr_deriv (by ring)
  apply ((hP.log (partition_pos m hi).ne').div_const m).congr_deriv
  simp_rw [mul_assoc, integral_const_mul]
  dsimp [tiltedMean]
  field_simp

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

 

structure ParametricRegular (l r K : ℝ) (F D : ℝ → (ι → ℝ) → ℝ) : Prop where
  nonneg : 0 ≤ K
  spatial : ∀ t ∈ Ioo l r, ∃ C, LipschitzWith C (F t)
  continuous : ∀ t ∈ Ioo l r, Continuous (D t)
  bounded : ∀ t ∈ Ioo l r, ∀ x, |D t x| ≤ K
  derivative : ∀ t ∈ Ioo l r, ∀ x, HasDerivAt (fun s => F s x) (D t x) t

 
theorem ParametricRegular.step {l r K : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricRegular l r K F D) {m : ℝ} (hm : 0 < m) (q : ι → ℝ≥0) :
    ParametricRegular l r K
      (fun t => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m (F t))
      (fun t => shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m (F t) (D t)) := by
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  have hi (t) (ht : t ∈ Ioo l r) (x : ι → ℝ) :
      Integrable (fun z => Real.exp (m*F t (x+z))) ν := by
    obtain ⟨C,hC⟩ := h.spatial t ht
    exact (exponentialIncrement_gaussian q).integrable_shift hC m x
  refine ⟨h.nonneg, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨C,hC⟩ := h.spatial t ht
    exact ⟨C,lipschitzWith_shiftedContinuation hC hm (hi t ht)⟩
  · intro t ht
    obtain ⟨C,hC⟩ := h.spatial t ht
    exact continuous_shiftedMean hC (h.continuous t ht) h.nonneg (h.bounded t ht) (hi t ht)
  · intro t ht x
    exact abs_tiltedMean_le ((h.continuous t ht).comp (continuous_const.add continuous_id)).measurable
      (hi t ht x) (fun z => h.bounded t ht (x+z))
  · intro t ht x
    exact hasDerivAt_continuation_local ht h.nonneg hm.ne'
      (fun s hs => by
        obtain ⟨C,hC⟩ := h.spatial s hs
        exact (hC.continuous.comp (continuous_const.add continuous_id)).measurable)
      ((h.continuous t ht).comp (continuous_const.add continuous_id)).measurable
      (fun s hs z => h.derivative s hs (x+z)) (fun s hs z => h.bounded s hs (x+z))
      (hi t ht x)

 
def prefixContinuation : List (GaussianStep ι) → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], F => F
  | (m,q)::tail, F => shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) m
      (prefixContinuation tail F)

def prefixTest : List (GaussianStep ι) → ((ι → ℝ) → ℝ) → ((ι → ℝ) → ℝ) → (ι → ℝ) → ℝ
  | [], _, D => D
  | (m,q)::tail, F, D => shiftedMean (Measure.pi fun i => gaussianReal 0 (q i)) m
      (prefixContinuation tail F) (prefixTest tail F D)

theorem ParametricRegular.prefix {l r K : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricRegular l r K F D) (steps : List (GaussianStep ι))
    (hm : ∀ step ∈ steps, 0 < step.1) :
    ParametricRegular l r K (fun t => prefixContinuation steps (F t))
      (fun t => prefixTest steps (F t) (D t)) := by
  induction steps with
  | nil => exact h
  | cons step tail ih =>
    rcases step with ⟨m,q⟩
    exact (ih (fun st hs => hm st (List.mem_cons_of_mem _ hs))).step
      (hm (m,q) List.mem_cons_self) q

 
theorem prefixContinuation_hierarchy {S : Type*} [Fintype S]
    (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (front tail : List (GaussianStep ι)) :
    prefixContinuation front (gaussianHierarchy w φ tail) =
      gaussianHierarchy w φ (front ++ tail) := by
  induction front with
  | nil => rfl
  | cons st front ih =>
    rcases st with ⟨m,q⟩
    simp only [prefixContinuation, List.cons_append, gaussianHierarchy, ih]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 
theorem isotropicGaussian_preserving (t : ℝ≥0) :
    MeasurePreserving (fun z : ι → ℝ => Real.sqrt (t:ℝ) • z)
      (Measure.pi fun _ : ι => gaussianReal 0 1)
      (Measure.pi fun _ : ι => gaussianReal 0 t) := by
  apply measurePreserving_pi (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 t)
  intro i
  change MeasurePreserving (fun z : ℝ => Real.sqrt (t:ℝ)*z) (gaussianReal 0 1) (gaussianReal 0 t)
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.eq
  change Real.sqrt (t:ℝ)^2*1 = (t:ℝ)
  rw [mul_one,Real.sq_sqrt t.coe_nonneg]

theorem integral_isotropicGaussian (t : ℝ≥0) {f : (ι → ℝ) → ℝ} (hf : Continuous f) :
    (∫ z, f (Real.sqrt (t:ℝ) • z) ∂Measure.pi fun _ : ι => gaussianReal 0 1) =
      ∫ z, f z ∂Measure.pi fun _ : ι => gaussianReal 0 t := by
  have hh := integral_map_of_stronglyMeasurable (μ := Measure.pi fun _ : ι => gaussianReal 0 1)
    (isotropicGaussian_preserving t).measurable hf.stronglyMeasurable
  rw [(isotropicGaussian_preserving t).map_eq] at hh
  exact hh.symm

def clockContinuation (m : ℝ) (F : (ι → ℝ) → ℝ) (t : ℝ) : (ι → ℝ) → ℝ :=
  shiftedContinuation (Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t)) m F

def clockTest (m : ℝ) (F A : (ι → ℝ) → ℝ) (t : ℝ) : (ι → ℝ) → ℝ :=
  shiftedMean (Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t)) m F A

theorem clockContinuation_eq {F : (ι → ℝ) → ℝ} (hF : Continuous F)
    (m : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    clockContinuation m F t x = Real.log (∫ z, Real.exp (m*F (x+Real.sqrt t • z))
      ∂Measure.pi fun _ : ι => gaussianReal 0 1)/m := by
  have hi := integral_isotropicGaussian (Real.toNNReal t)
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  rw [Real.coe_toNNReal t ht] at hi
  exact congrArg (fun z => Real.log z/m) hi.symm

theorem clockTest_eq {F A : (ι → ℝ) → ℝ} (hF : Continuous F) (hA : Continuous A)
    (m : ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    clockTest m F A t x = tiltedMean (Measure.pi fun _ : ι => gaussianReal 0 1) m
      (fun z => F (x+Real.sqrt t • z)) (fun z => A (x+Real.sqrt t • z)) := by
  have hn := integral_isotropicGaussian (Real.toNNReal t)
    (f := fun z => A (x+z)*Real.exp (m*F (x+z))) (by fun_prop)
  have hd := integral_isotropicGaussian (Real.toNNReal t)
    (f := fun z => Real.exp (m*F (x+z))) (by fun_prop)
  rw [Real.coe_toNNReal t ht] at hn hd
  exact congrArg₂ (· / ·) hn.symm hd.symm

 
def clockDerivative {n : ℕ} (m : ℝ) (F : (Fin (n+1) → ℝ) → ℝ)
    (G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ) (t : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  (1/2:ℝ)*((∑ i, clockTest m F (H i) t x) + m *
    ∑ i, clockTest m F (fun y => (G i y)^2) t x)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem parametric_clock {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ}
    {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v)) (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1)) (H i (x+t • Pi.single i 1)) t)
    {m : ℝ} (hm : 0 < m) :
    ∃ K, ∀ r, ParametricRegular 0 r K (clockContinuation m F) (clockDerivative m F G H) := by
  have hGs (i) : BddSmooth 0 (fun y => (G i y)^2) := by
    simpa only [pow_two] using (hG i).mul (hG i)
  choose BH hBH bH using fun i => (hH i).bound
  choose BG hBG bG using fun i => (hGs i).bound
  let K : ℝ := (1/2)*((∑ i, BH i)+m*(∑ i, BG i))
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num) (add_nonneg (Finset.sum_nonneg fun i _ => hBH i)
      (mul_nonneg hm.le (Finset.sum_nonneg fun i _ => hBG i)))
  have hi (t : ℝ) (x : Fin (n+1) → ℝ) :
      Integrable (fun z => Real.exp (m*F (x+z)))
        (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 (Real.toNNReal t)) :=
    (exponentialIncrement_gaussian (fun _ => Real.toNNReal t)).integrable_shift hF m x
  refine ⟨K, fun r => ⟨hK, ?_, ?_, ?_, ?_⟩⟩
  · intro t _
    exact ⟨C, lipschitzWith_shiftedContinuation hF hm (hi t)⟩
  · intro t _
    apply Continuous.const_mul
    apply Continuous.add
    · exact continuous_finsetSum _ (fun i _ => continuous_shiftedMean hF (hH i).continuous
        (hBH i) (bH i) (hi t))
    · exact (continuous_finsetSum _ (fun i _ => continuous_shiftedMean hF (hGs i).continuous
        (hBG i) (bG i) (hi t))).const_mul m
  · intro t _ x
    have hBH' (i) : |clockTest m F (H i) t x| ≤ BH i :=
      abs_tiltedMean_le ((hH i).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi t x) (fun z => bH i (x+z))
    have hBG' (i) : |clockTest m F (fun y => (G i y)^2) t x| ≤ BG i :=
      abs_tiltedMean_le ((hGs i).continuous.comp (continuous_const.add continuous_id)).measurable
        (hi t x) (fun z => bG i (x+z))
    dsimp [clockDerivative,K]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_pos hm]
    exact add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hBH' i))
      (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hBG' i)) hm.le)
  · intro t ht x
    have hp := (GaussianCalculus.hasDerivWithinAt_vector_heat_continuation hF hG hH hd hd₁ hm.ne' ht.1.le x).hasDerivAt
      (Ici_mem_nhds ht.1)
    have he : (fun s => clockContinuation m F s x) =ᶠ[𝓝 t]
        (fun s => Real.log (∫ z, Real.exp (m*F (x+Real.sqrt s • z))
          ∂Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1)/m) := by
      filter_upwards [eventually_gt_nhds ht.1] with s hs
      exact clockContinuation_eq hF.continuous m hs.le x
    have hde : clockDerivative m F G H t x =
        ((1/2:ℝ)*((∑ i, tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+Real.sqrt t • z)) (fun z => H i (x+Real.sqrt t • z))) + m *
        (∑ i, tiltedMean (Measure.pi fun _ : Fin (n+1) => gaussianReal 0 1) m
          (fun z => F (x+Real.sqrt t • z)) (fun z => (G i (x+Real.sqrt t • z))^2)))) := by
      simp only [clockDerivative, clockTest_eq hF.continuous (hH _).continuous m ht.1.le,
        clockTest_eq hF.continuous (hGs _).continuous m ht.1.le]
    rw [hde]
    exact hp.congr_of_eventuallyEq he

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {ι : Type*} [Fintype ι]

 

theorem ParametricRegular.root {l r K : ℝ} {F D : ℝ → (ι → ℝ) → ℝ}
    (h : ParametricRegular l r K F D) (q : ι → ℝ≥0) :
    ParametricRegular l r K
      (fun t => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) (F t))
      (fun t => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q i)) (D t)) := by
  let ν := Measure.pi fun i => gaussianReal 0 (q i)
  have hi (t) (ht : t ∈ Ioo l r) (x : ι → ℝ) : Integrable (fun z => F t (x+z)) ν := by
    obtain ⟨C,hC⟩ := h.spatial t ht
    exact (exponentialIncrement_gaussian q).integrable_lipschitz hC x
  refine ⟨h.nonneg, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨C,hC⟩ := h.spatial t ht
    exact ⟨C, zeroContinuation_lipschitz hC (hi t ht)⟩
  · intro t ht
    have hh := continuous_shiftedMean (ν := ν) (m := 0)
      (LipschitzWith.const (0:ℝ)) (h.continuous t ht) h.nonneg (h.bounded t ht)
      (fun x => by simp)
    have he : shiftedMean ν 0 (fun _ : ι → ℝ => (0:ℝ)) (D t) =
        zeroContinuation ν (D t) := funext fun x => shiftedMean_zero _ _ x
    rw [he] at hh
    exact hh
  · intro t ht x
    calc
      |zeroContinuation ν (D t) x| ≤ ∫ z, |D t (x+z)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ _ : ι → ℝ, K ∂ν := integral_mono_of_nonneg
        (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
        (Eventually.of_forall fun z => h.bounded t ht (x+z))
      _ = K := by simp
  · intro t ht x
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := ν) (F := fun s z => F s (x+z)) (F' := fun s z => D s (x+z))
      (s := Ioo l r) (bound := fun _ : ι → ℝ => K) (Ioo_mem_nhds ht.1 ht.2)
      _ (hi t ht x) _ _ (integrable_const _) _).2
    · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      obtain ⟨C,hC⟩ := h.spatial s hs
      exact (hC.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    · exact ((h.continuous t ht).comp (continuous_const.add continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun z s hs => by
        simpa only [Real.norm_eq_abs] using h.bounded s hs (x+z)
    · exact Eventually.of_forall fun z s hs => h.derivative s hs (x+z)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

theorem rootedHierarchy_inserted_clock {n : ℕ} {S : Type*} [Fintype S] [Nonempty S]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (front tail : List (GaussianStep (Fin (n+1)))) {m : ℝ} (hm : 0 < m)
    (ha : OrderedSteps m tail) (hfront : ∀ st ∈ front, 0 < st.1)
    (q₀ : Fin (n+1) → ℝ≥0) {t : ℝ} (ht : 0 < t) (x : Fin (n+1) → ℝ) :
    HasDerivAt
      (fun s => zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (gaussianHierarchy w φ (front ++ (m,fun _ => Real.toNNReal s)::tail)) x)
      (zeroContinuation (Measure.pi fun i => gaussianReal 0 (q₀ i))
        (prefixTest front (clockContinuation m (gaussianHierarchy w φ tail) t)
          (clockDerivative m (gaussianHierarchy w φ tail)
            (fun i => gaussianHierarchyMean w φ (fun σ => φ σ (Pi.single i 1)) tail)
            (fun i => gaussianHierarchyResponse w φ (fun σ => φ σ (Pi.single i 1))
              (Pi.single i 1) tail) t)) x) t := by
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail ha 0).1
  obtain ⟨K,hK⟩ := parametric_clock hC
    (fun i => gaussianHierarchyMean_smooth hw φ _ tail ha 0)
    (fun i => gaussianHierarchyResponse_smooth hw φ _ _ tail ha 0)
    (fun y v s => by
      rw [← gaussianHierarchyMean_feature_components hw φ tail ha v (y+s • v)]
      exact gaussianHierarchy_hasDerivAt hw φ tail ha y v s)
    (fun i y s => gaussianHierarchyMean_hasDerivAt hw φ _ tail ha y _ s) hm
  have hh := (((hK (t+1)).prefix front hfront).root q₀).derivative t ⟨ht, by linarith⟩ x
  have he (s : ℝ) : prefixContinuation front (clockContinuation m (gaussianHierarchy w φ tail) s) =
      gaussianHierarchy w φ (front ++ (m,fun _ => Real.toNNReal s)::tail) :=
    prefixContinuation_hierarchy w φ front ((m,fun _ => Real.toNNReal s)::tail)
  simp_rw [he] at hh
  exact hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.GaussianCalculus
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem ExpNormBounded.lipschitz {f : E → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ExpNormBounded f := by
  refine ⟨hf.continuous, (C:ℝ)+|f 0|, 1, by positivity, by norm_num, ?_⟩
  intro x
  have hh : |f x-f 0| ≤ (C:ℝ)*‖x‖ := by
    simpa only [Real.dist_eq,dist_zero_right] using hf.dist_le_mul x 0
  have hnorm : ‖x‖ ≤ Real.exp ‖x‖ := by linarith [Real.add_one_le_exp ‖x‖]
  have hone : 1 ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg _)
  have hf0 := mul_le_mul_of_nonneg_left hone (abs_nonneg (f 0))
  have hC := mul_le_mul_of_nonneg_left hnorm C.coe_nonneg
  have hab := abs_add_le (f x-f 0) (f 0)
  rw [sub_add_cancel] at hab
  simp only [one_mul]
  nlinarith

theorem ExpNormBounded.bddSmooth {f : E → ℝ} (hf : BddSmooth 0 f) : ExpNormBounded f := by
  obtain ⟨B,hB,hb⟩ := hf.bound
  exact ⟨hf.continuous,B,0,hB,le_rfl,fun x => by simpa using hb x⟩

end SKFluctuations.GaussianCalculus

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 
def clockRoot (F : (ι → ℝ) → ℝ) (t : ℝ) : (ι → ℝ) → ℝ :=
  zeroContinuation (Measure.pi fun _ : ι => gaussianReal 0 (Real.toNNReal t)) F

theorem clockRoot_eq {F : (ι → ℝ) → ℝ} (hF : Continuous F)
    {t : ℝ} (ht : 0 ≤ t) (x : ι → ℝ) :
    clockRoot F t x = ∫ z, F (x+Real.sqrt t • z) ∂Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hh := integral_isotropicGaussian (Real.toNNReal t) (f := fun z => F (x+z)) (by fun_prop)
  rw [Real.coe_toNNReal t ht] at hh
  exact hh.symm

 

theorem hasDerivWithinAt_clockRoot {n : ℕ} {F : (Fin (n+1) → ℝ) → ℝ}
    {G H : Fin (n+1) → (Fin (n+1) → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hG : ∀ i, BddSmooth 0 (G i)) (hH : ∀ i, BddSmooth 0 (H i))
    (hd : ∀ x v t, HasDerivAt (fun s : ℝ => F (x+s • v)) (∑ i, v i*G i (x+t • v)) t)
    (hd₁ : ∀ i x t, HasDerivAt (fun s : ℝ => G i (x+s • Pi.single i 1)) (H i (x+t • Pi.single i 1)) t)
    {t : ℝ} (ht : 0 ≤ t) (x : Fin (n+1) → ℝ) :
    HasDerivWithinAt (fun s => clockRoot F s x)
      ((1/2:ℝ)*clockRoot (fun y => ∑ i, H i y) t x) (Ici 0) t := by
  have hh := GaussianCalculus.hasDerivWithinAt_gaussian_vector_variance
    (GaussianCalculus.ExpNormBounded.lipschitz hF)
    (fun i => GaussianCalculus.ExpNormBounded.bddSmooth (hG i))
    (fun i => GaussianCalculus.ExpNormBounded.bddSmooth (hH i)) hd hd₁ x ht
  have hc : Continuous (fun y => ∑ i, H i y) := continuous_finsetSum _ fun i _ => (hH i).continuous
  rw [clockRoot_eq hc ht x]
  exact hh.congr (fun s hs => clockRoot_eq hF.continuous hs x) (clockRoot_eq hF.continuous ht x)

end SKFluctuations.Hierarchy

end

end OAI
