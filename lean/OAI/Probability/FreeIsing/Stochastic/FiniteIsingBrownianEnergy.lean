import OAI.Probability.FreeIsing.Gaussian.FiniteIsingGaussianEnergy
import OAI.Probability.FreeIsing.Posterior.GaussianEnergyIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Problem367

local instance finiteIsingBrownianEnergyNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

theorem finiteBrownianNoise_restrict_measurePreserving
    {ι Ω : Type*} [MeasurableSpace Ω]
    (ν : ι → Measure Ω) {B : ι → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t)) (D : Finset ι) (t : ℝ≥0) :
    MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.infinitePi ν) (Measure.pi (fun _ : D => gaussianReal 0 t)) := by
  have (i : ι) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hr : MeasurePreserving (D.restrict : (ι → Ω) → D → Ω)
      (Measure.infinitePi ν) (Measure.pi fun v : D => ν v) :=
    ⟨D.measurable_restrict, Measure.infinitePi_map_restrict ν⟩
  have he : MeasurePreserving (fun ω (v : D) => B v t (ω v))
      (Measure.pi fun v : D => ν v) (Measure.pi fun _ : D => gaussianReal 0 t) := by
    refine ⟨Measurable.of_eval (fun vertex => (hmB vertex t).comp
      (measurable_pi_apply vertex)), ?_⟩
    rw [Measure.pi_map_pi (μ := fun v : D => ν v)
      (f := fun v ω => B v t ω) (fun v => (hmB v t).aemeasurable)]
    congr 1
    funext v
    exact (hB v).hasLaw_eval t |>.map_eq
  exact he.comp hr

theorem integral_finiteIsingBrownian_observation_eq_standard
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (t : ℝ≥0)
    (f : (D → ℝ) → ℝ) (hf : Measurable f) :
    (∫ p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω),
      f (fun v : D => (t : ℝ) * spinSign (p.1 v) + B v t (p.2 v))
      ∂μ.prod (Measure.infinitePi ν)) =
    ∫ p : (D → IsingSpin) × (D → ℝ),
      f (FinitePosterior.finiteStandardObservation
        (fun eta v => spinSign (eta v)) t p)
      ∂(μ.map D.restrict).prod (Measure.pi fun _ : D => gaussianReal 0 1) := by
  have (i : TreeVertex d) : IsProbabilityMeasure (ν i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := inferInstance
  let Y : (D → IsingSpin) × (D → ℝ) → D → ℝ :=
    fun p v => (t : ℝ) * spinSign (p.1 v) + p.2 v
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro v
    exact (measurable_const.mul
      ((measurable_of_finite (fun eta : D → IsingSpin => spinSign (eta v))).comp
        measurable_fst)).add ((measurable_pi_apply v).comp measurable_snd)
  have hr : MeasurePreserving D.restrict μ π := ⟨D.measurable_restrict, rfl⟩
  have hp := hr.prod (finiteBrownianNoise_restrict_measurePreserving ν hB hmB D t)
  have hs : MeasurePreserving (fun z : D → ℝ => fun v => Real.sqrt (t : ℝ) * z v)
      (Measure.pi fun _ : D => gaussianReal 0 1)
      (Measure.pi fun _ : D => gaussianReal 0 t) := by
    refine ⟨by fun_prop, ?_⟩
    exact gaussianPi_map_sqrt (t : ℝ) t.property
  have hps := (MeasurePreserving.id π).prod hs
  have hleft := integral_map (μ := μ.prod (Measure.infinitePi ν)) hp.measurable.aemeasurable
    (hf.comp hY).aestronglyMeasurable
  have hright := integral_map (μ := π.prod (Measure.pi fun _ : D => gaussianReal 0 1))
    hps.measurable.aemeasurable
    (hf.comp hY).aestronglyMeasurable
  rw [hp.map_eq] at hleft
  rw [hps.map_eq] at hright
  exact hleft.symm.trans hright

def finiteIsingBrownianObservation {d : ℕ} {Ω : Type*}
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (D : Finset (TreeVertex d))
    (t : ℝ) (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : D → ℝ :=
  fun v => t * spinSign (p.1 v) + B v t.toNNReal (p.2 v)

def finiteIsingBrownianMean {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun eta u => spinSign (eta u)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p)

def finiteIsingBrownianCovariance {d : ℕ} {Ω : Type*}
    (beta : ℝ) (D : Finset (TreeVertex d)) (v u : D)
    (B : TreeVertex d → ℝ≥0 → Ω → ℝ) (t : ℝ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω)) : ℝ :=
  FinitePosterior.fieldCovariance (finiteIsingEnergy beta D)
    (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v))
    (finiteIsingBrownianObservation B D t p) u

theorem HasFreeIsingLaw.integral_finiteIsingBrownianEnergy
    {d : ℕ} {beta : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω)
    {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D)
    {T : ℝ} (hT : 0 ≤ T) :
    let ρ := μ.prod (Measure.infinitePi ν)
    let E : ℝ → ℝ := fun t => ∫ p,
      ∑ u : D, finiteIsingBrownianCovariance beta D v u B t p ^ 2 ∂ρ
    IntervalIntegrable E volume 0 T ∧
      (∫ t in 0..T, E t) =
        (∫ p, finiteIsingBrownianMean beta D v B T p ^ 2 ∂ρ) ∧
      0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ 1 := by
  classical
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let π := μ.map D.restrict
  let : IsProbabilityMeasure π := inferInstance
  let spin : (D → IsingSpin) → D → ℝ := fun eta u => spinSign (eta u)
  let q : (D → IsingSpin) → ℝ := fun eta => spinSign (eta v)
  let F : (D → ℝ) → ℝ := FinitePosterior.fieldMean (finiteIsingEnergy beta D) spin q
  let C : (D → ℝ) → D → ℝ :=
    FinitePosterior.fieldCovariance (finiteIsingEnergy beta D) spin q
  let ρ := μ.prod (Measure.infinitePi ν)
  let ρG := π.prod (Measure.pi fun _ : D => gaussianReal 0 1)
  let EG : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, C (FinitePosterior.finiteStandardObservation spin t p) u ^ 2 ∂ρG
  let MG : ℝ → ℝ := fun t => ∫ p,
    F (FinitePosterior.finiteStandardObservation spin t p) ^ 2 ∂ρG
  let E : ℝ → ℝ := fun t => ∫ p,
    ∑ u : D, finiteIsingBrownianCovariance beta D v u B t p ^ 2 ∂ρ
  let M : ℝ → ℝ := fun t => ∫ p,
    finiteIsingBrownianMean beta D v B t p ^ 2 ∂ρ
  have hfm : Measurable (fun y => F y ^ 2) :=
    ((FinitePosterior.continuous_fieldMean _ _ _).pow 2).measurable
  have hcm : Measurable (fun y => ∑ u : D, C y u ^ 2) := by
    apply Finset.measurable_sum
    intro u _
    exact ((FinitePosterior.continuous_fieldCovariance _ _ _ u).pow 2).measurable
  have hE (t : ℝ) (ht : 0 ≤ t) : E t = EG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => ∑ u : D, C y u ^ 2) hcm
    unfold E EG finiteIsingBrownianCovariance finiteIsingBrownianObservation
    simpa only [C, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hM (t : ℝ) (ht : 0 ≤ t) : M t = MG t := by
    have h := integral_finiteIsingBrownian_observation_eq_standard μ ν hB hmB D
      t.toNNReal (fun y => F y ^ 2) hfm
    unfold M MG finiteIsingBrownianMean finiteIsingBrownianObservation
    simpa only [F, spin, q, ρ, ρG, π, Real.coe_toNNReal t ht] using h
  have hcoords (eta : D → IsingSpin) (u : D) : spin eta u = -1 ∨ spin eta u = 1 := by
    dsimp only [spin]
    cases eta u <;> simp [spinSign]
  have hbound (eta : D → IsingSpin) : |q eta| ≤ 1 := by
    dsimp only [q]
    cases eta v <;> simp [spinSign]
  have hstd := FinitePosterior.integral_finiteStandardEnergy π
    (finiteIsingEnergy beta D) (hμ.restrict_real_eq_normalized_exp D hD)
    spin q 1 hbound hcoords hT
  change IntervalIntegrable EG volume 0 T ∧
    (∫ t in 0..T, EG t) = MG T - F 0 ^ 2 ∧
    0 ≤ (∫ t in 0..T, EG t) ∧ (∫ t in 0..T, EG t) ≤ (1 : ℝ) ^ 2 at hstd
  have hzero : F 0 = 0 := finiteIsingPosterior_spin_zero beta D v
  have hEq : EqOn EG E (uIcc 0 T) := by
    intro t ht
    exact (hE t (by simpa only [min_eq_left hT] using ht.1)).symm
  have hInt : (∫ t in 0..T, EG t) = ∫ t in 0..T, E t :=
    intervalIntegral.integral_congr hEq
  change IntervalIntegrable E volume 0 T ∧
    (∫ t in 0..T, E t) = M T ∧
    0 ≤ (∫ t in 0..T, E t) ∧ (∫ t in 0..T, E t) ≤ 1
  refine ⟨hstd.1.congr (fun t ht => hEq (uIoc_subset_uIcc ht)), ?_, ?_, ?_⟩
  · rw [← hInt, hstd.2.1, hzero, zero_pow (by decide), sub_zero, hM T hT]
  · simpa only [hInt] using hstd.2.2.1
  · simpa only [hInt, one_pow] using hstd.2.2.2

end Problem367

end

end OAI
