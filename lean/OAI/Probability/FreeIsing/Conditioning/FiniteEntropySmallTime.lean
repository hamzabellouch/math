import OAI.Probability.FreeIsing.Brownian.EntropyEnergy
import OAI.Probability.FreeIsing.Brownian.PosteriorField
import OAI.Probability.FreeIsing.Gaussian.SiteInformation
import OAI.Probability.FreeIsing.Stochastic.FiniteIsingBrownianPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteEntropySmallTimeNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

theorem gaussian_channel_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S G : Ω → ℝ} (hS : AEMeasurable S P)
    (hSb : ∀ᵐ p ∂P, |S p| ≤ 1) {t : ℝ≥0}
    (hG : HasLaw G (gaussianReal 0 t) P) (ht : (t : ℝ) ≤ 1) :
    Integrable (fun p => |(t : ℝ) * S p + G p| ^ 4) P ∧
    (∫ p, |(t : ℝ) * S p + G p| ^ 4 ∂P) ≤
      (8 * (1 + Real.exp 32)) * (t : ℝ) := by
  have ht0 := t.coe_nonneg
  have hG4 := integrable_abs_pow_of_gaussianLaw hG 4
  have hdom : Integrable (fun p => (8 : ℝ) * ((t : ℝ) ^ 4 + |G p| ^ 4)) P :=
    ((integrable_const _).add hG4).const_mul 8
  have hbound : ∀ᵐ p ∂P, |(t : ℝ) * S p + G p| ^ 4 ≤
      8 * ((t : ℝ) ^ 4 + |G p| ^ 4) := by
    filter_upwards [hSb] with p hp
    have hb : |(t : ℝ) * S p + G p| ≤ (t : ℝ) + |G p| := by
      calc
        _ ≤ |(t : ℝ) * S p| + |G p| := abs_add_le _ _
        _ ≤ (t : ℝ) + |G p| := by
          rw [abs_mul, abs_of_nonneg ht0]
          gcongr
          simpa using mul_le_mul_of_nonneg_left hp ht0
    exact (pow_le_pow_left₀ (abs_nonneg _) hb 4).trans
      (by convert add_pow_le ht0 (abs_nonneg (G p)) 4 using 1; norm_num)
  have hi : Integrable (fun p => |(t : ℝ) * S p + G p| ^ 4) P := by
    apply hdom.mono' (((hS.const_mul (t : ℝ)).add hG.aemeasurable).abs.pow_const 4).aestronglyMeasurable
    filter_upwards [hbound] with p hp
    change ‖|(t : ℝ) * S p + G p| ^ 4‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hp
  have hstd : (∫ x : ℝ, |x| ^ 4 ∂gaussianReal 0 1) ≤ Real.exp 32 := by
    calc
      _ ≤ ∫ x : ℝ, (1 + |x|) ^ 4 ∂gaussianReal 0 1 :=
        integral_mono (integrable_standardGaussian_abs_pow 4)
          (integrable_one_add_abs_pow_gaussian 4)
          (fun x => pow_le_pow_left₀ (abs_nonneg x) (by linarith) 4)
      _ ≤ _ := by
        convert integral_one_add_abs_pow_gaussian_le (p := 4) (by decide) using 1; norm_num
  have hnoise : (∫ p, |G p| ^ 4 ∂P) ≤ (t : ℝ) ^ 2 * Real.exp 32 := by
    have heq := hG.integral_comp (f := fun x : ℝ => |x| ^ 4) (by fun_prop)
    change (∫ p, |G p| ^ 4 ∂P) = _ at heq
    rw [heq, integral_gaussianReal_abs_pow]
    have hs : Real.sqrt (t : ℝ) ^ 4 = (t : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt ht0]
    rw [hs]
    exact mul_le_mul_of_nonneg_left hstd (sq_nonneg _)
  have ht2 : (t : ℝ) ^ 2 ≤ (t : ℝ) := by nlinarith
  have ht4 : (t : ℝ) ^ 4 ≤ (t : ℝ) := by
    have h := pow_le_pow_left₀ (sq_nonneg (t : ℝ)) ht2 2
    nlinarith
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ p, (8 : ℝ) * ((t : ℝ) ^ 4 + |G p| ^ 4) ∂P :=
      integral_mono_ae hi hdom hbound
    _ = 8 * ((t : ℝ) ^ 4 + ∫ p, |G p| ^ 4 ∂P) := by
      rw [integral_const_mul, integral_add (integrable_const _) hG4]
      simp
    _ ≤ 8 * ((t : ℝ) + (t : ℝ) * Real.exp 32) := by
      gcongr
      exact hnoise.trans (mul_le_mul_of_nonneg_right ht2 (Real.exp_nonneg _))
    _ = _ := by ring

theorem finiteIsingBrownianEntropy_le_information
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hbeta : 0 ≤ beta) (μ : Measure (TreeVertex d → IsingSpin))
    [IsProbabilityMeasure μ] (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) :
    (∫ p, finiteIsingBrownianEntropy beta D v B t p
      ∂μ.prod (Measure.infinitePi ν)) ≤
    2 * Real.sqrt
      (Real.cosh ((d : ℝ) * beta + 1) ^ 2 *
        (∫ p, finiteIsingBrownianMean beta D v B t p ^ 2
          ∂μ.prod (Measure.infinitePi ν)) +
        (16 * (1 + ((d : ℝ) * beta) ^ 2) * (1 + Real.exp 32)) * (t : ℝ)) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := μ.prod (Measure.infinitePi ν)
  let M := finiteIsingBrownianMean beta D v B (t : ℝ)
  let H := fun p => Real.artanh (M p)
  let G := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) => B v t (p.2 v)
  let S := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) => spinSign (p.1 v)
  let X := fun p => (t : ℝ) * S p + G p
  have hcoord := (measurePreserving_eval_infinitePi ν (v : TreeVertex d)).comp
    (measurePreserving_snd (μ := μ) (ν := Measure.infinitePi ν))
  have hG : HasLaw G (gaussianReal 0 t) P :=
    (hB v).hasLaw_eval t |>.comp ⟨hcoord.measurable.aemeasurable, hcoord.map_eq⟩
  have hS : Measurable S := (measurable_of_finite spinSign).comp
    ((measurable_pi_apply (v : TreeVertex d)).comp measurable_fst)
  have hSb : ∀ᵐ p ∂P, |S p| ≤ 1 := Eventually.of_forall fun p => by
    cases hp : p.1 v <;> simp [S, hp, spinSign]
  have hX4 := gaussian_channel_fourth_moment hS.aemeasurable hSb hG ht
  have hspin (eta : D → IsingSpin) : spinSign (eta v) = -1 ∨ spinSign (eta v) = 1 := by
    cases eta v <;> simp [spinSign]
  have hneg : ∃ eta : D → IsingSpin, spinSign (eta v) = -1 := ⟨fun _ => .neg, rfl⟩
  have hpos : ∃ eta : D → IsingSpin, spinSign (eta v) = 1 := ⟨fun _ => .pos, rfl⟩
  have hm : Measurable M :=
    (FinitePosterior.continuous_fieldMean _ _ _).measurable.comp
      (measurable_finiteIsingBrownianObservation hmB D t)
  have hart : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hH : AEMeasurable H P := (hart.comp hm).aemeasurable
  have hinterior (p) : M p ∈ Ioo (-1 : ℝ) 1 :=
    FinitePosterior.fieldMean_spin_mem_Ioo _ _ _ _ hspin hneg hpos
  have htan (p) : Real.tanh (H p) = M p := Real.tanh_artanh (hinterior p)
  have hfield : ∀ᵐ p ∂P, |H p - X p| ≤ (d : ℝ) * beta := by
    apply Eventually.of_forall
    intro p
    have hb := finite_tree_gibbs_field_uniform_bound D hbeta
      (finiteIsingBrownianObservation B D t p) v
    change |H p - finiteIsingBrownianObservation B D t p v| ≤
      (d : ℝ) * beta at hb
    simpa only [X, S, G, finiteIsingBrownianObservation, Real.toNNReal_coe] using hb
  have hsecond := integral_sq_le_tanh_sq_add_fourth
    (by positivity : 0 ≤ (d : ℝ) * beta) hH hX4.1 hfield
  simp_rw [htan] at hsecond
  have hH2 : MemLp H 2 P :=
    (memLp_two_iff_integrable_sq hH.aestronglyMeasurable).mpr hsecond.1
  have hinfo : (∫ p, H p ^ 2 ∂P) ≤
      Real.cosh ((d : ℝ) * beta + 1) ^ 2 * (∫ p, M p ^ 2 ∂P) +
      (16 * (1 + ((d : ℝ) * beta) ^ 2) * (1 + Real.exp 32)) * (t : ℝ) := by
    apply hsecond.2.trans
    have hb := mul_le_mul_of_nonneg_left hX4.2
      (by positivity : 0 ≤ 2 * (1 + ((d : ℝ) * beta) ^ 2))
    nlinarith
  have hE := (finiteIsingBrownianEntropy_moment hbeta μ ν hB hmB D v t).1
  calc
    _ ≤ ∫ p, 2 * |H p| ∂P := by
      apply integral_mono hE ((hH2.integrable (by norm_num)).abs.const_mul 2)
      intro p
      exact FinitePosterior.fieldEntropy_le_abs_field _ _ _ _ hspin hneg hpos
    _ = 2 * ∫ p, |H p| ∂P := integral_const_mul _ _
    _ ≤ 2 * Real.sqrt (∫ p, H p ^ 2 ∂P) :=
      mul_le_mul_of_nonneg_left (integral_abs_le_sqrt_integral_sq hH hsecond.1) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinfo) (by norm_num)

theorem brownianTerminal_information_eq_gaussian
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (t : ℝ≥0) (v : TreeVertex d) :
    (∫ p, ((μ.prod (Measure.infinitePi ν))[fun z => spinSign (z.1 v) |
      brownianTerminalSigma B t] p) ^ 2 ∂μ.prod (Measure.infinitePi ν)) =
    ∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) :=
    fun p => (p.1, fun i => B i t (p.2 i))
  have hT : MeasurePreserving T (μ.prod (Measure.infinitePi ν))
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) :=
    (MeasurePreserving.id μ).prod (brownian_array_eval_measurePreserving ν hB hmB t)
  have hspin : Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      spinSign (z.1 v)) := (measurable_of_finite spinSign).comp
    ((measurable_pi_apply v).comp measurable_fst)
  have hpull := condExp_comp_measurePreserving_comap hT hspin.stronglyMeasurable
    (PlantedSymmetry.integrable_plantedSpin _ v)
    (PlantedSymmetry.observationSigma_le (TreeVertex d) t)
  have hsame : (PlantedSymmetry.observationSigma (TreeVertex d) (t : ℝ)).comap T =
      brownianTerminalSigma B t := by
    rw [PlantedSymmetry.observationSigma, MeasurableSpace.comap_comp]
    change MeasurableSpace.comap
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
        fun i => (t : ℝ) * spinSign (p.1 i) + B i t (p.2 i)) inferInstance = _
    simp only [brownianTerminalSigma, Real.toNNReal_coe]
  rw [hsame] at hpull
  calc
    _ = ∫ p, (PlantedSymmetry.posteriorMagnetization
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t v (T p)) ^ 2
        ∂μ.prod (Measure.infinitePi ν) := by
      apply integral_congr_ae
      filter_upwards [hpull] with p hp
      exact congrArg (fun x : ℝ => x ^ 2) hp
    _ = _ := hT.hasLaw.integral_comp
      (((stronglyMeasurable_condExp).mono
        (PlantedSymmetry.observationSigma_le (TreeVertex d) t)).pow 2).aestronglyMeasurable

theorem HasFreeIsingLaw.finiteIsingBrownian_critical_information_upper
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) :
    (∫ p, finiteIsingBrownianMean beta D v B t p ^ 2
      ∂μ.prod (Measure.infinitePi ν)) ≤
      ((1 + (Real.tanh beta) ^ 2) *
        Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4))) *
          Real.sqrt (t : ℝ) := by
  let := hμ.isProbabilityMeasure
  have h := hμ.finiteIsingBrownian_information_le ν hB hmB D hD v t
  dsimp only at h
  rw [brownianTerminal_information_eq_gaussian μ ν hB hmB t v] at h
  exact h.trans (hμ.gaussian_site_critical_information_upper hd hb hcritical t ht v)

def criticalEntropyEnvelope (d : ℕ) (beta t : ℝ) : ℝ :=
  2 * Real.sqrt
    (Real.cosh ((d : ℝ) * beta + 1) ^ 2 *
      (((1 + (Real.tanh beta) ^ 2) *
        Real.sqrt (1 / ((1 - (Real.tanh beta) ^ 2) * (Real.tanh beta) ^ 4))) *
          Real.sqrt t) +
      (16 * (1 + ((d : ℝ) * beta) ^ 2) * (1 + Real.exp 32)) * t)

theorem HasFreeIsingLaw.finiteIsingBrownianEntropy_le_criticalEnvelope
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) :
    (∫ p, finiteIsingBrownianEntropy beta D v B t p
      ∂μ.prod (Measure.infinitePi ν)) ≤ criticalEntropyEnvelope d beta t := by
  let := hμ.isProbabilityMeasure
  apply (finiteIsingBrownianEntropy_le_information hb μ ν hB hmB D v t ht).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left
    (hμ.finiteIsingBrownian_critical_information_upper hd hb hcritical ν hB hmB D hD v t ht)
    (sq_nonneg _)

@[simp] theorem criticalEntropyEnvelope_zero (d : ℕ) (beta : ℝ) :
    criticalEntropyEnvelope d beta 0 = 0 := by simp [criticalEntropyEnvelope]

theorem continuous_criticalEntropyEnvelope (d : ℕ) (beta : ℝ) :
    Continuous (criticalEntropyEnvelope d beta) := by
  unfold criticalEntropyEnvelope
  fun_prop

end Problem367

end

end OAI
