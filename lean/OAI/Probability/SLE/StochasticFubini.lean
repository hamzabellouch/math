import Mathlib
import OAI.Probability.SLE.ExponentialMartingales

namespace OAI

/-! Stochastic Fubini for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField
theorem clipped_spatial_green_window_exponential
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q)
    (R : ℝ) (hR : 0 ≤ R) (T : ℝ≥0)
    (σ τ : Z × Ω → ℝ≥0) (hσm : Measurable σ) (hτm : Measurable τ)
    (hστ : ∀ p, σ p ≤ τ p)
    (hσa : ∀ t : ℝ≥0, @MeasurableSet (Z × Ω)
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))
      {p | t < σ p})
    (hσs : ∀ z, IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (σ (z, ω) : WithTop ℝ≥0)))
    (hτa : ∀ t : ℝ≥0, @MeasurableSet (Z × Ω)
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))
      {p | t < τ p})
    (hτs : ∀ z, IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ (z, ω) : WithTop ℝ≥0)))
    (hτb : ∀ z ω, τ (z,ω) ≤ T)
    (hinside : ∀ z ω t, t ≤ τ (z,ω) →
      ‖((c (q z)).Q t ω, B t ω)‖ ≤ R ∧
        lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi)
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, greenLogDensity κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) -
        greenLogDensity κ ((c (q z)).Q (σ (z,ω)) ω) (B (σ (z,ω)) ω) ∂ν) -
      θ^2 * (∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) / 2)) ∂P) ≤ 1 := by
  classical
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_green_field κ R hR
  let ψ := spatialPartial φ 1
  have hψc : Continuous ψ := (spatialPartial_smooth φ hφ 1).continuous
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz ψ
    (spatialPartial_smooth φ hφ 1) (spatialPartial_compact φ hφc 1)
  have hψeq (q' : ℂ × ℝ) (x : ℝ) (hb : ‖(q',x)‖ ≤ R) :
      ψ (q',x) = greenLogCoefficient κ q' x := by
    rw [show ψ (q',x) = deriv (fun y => φ (q',y)) x by
      simp only [ψ, spatialPartial_eq_iteratedDeriv φ hφ, iteratedDeriv_one]]
    rw [deriv_fiber_fderiv φ (hφ.differentiable (by simp)), hφD q' x hb,
      ← deriv_fiber_fderiv _ ((greenLogDensity_contDiff κ).differentiable (by simp))]
    exact (greenLogDensity_spatial_derivative κ q' x).deriv
  let F (p : ℝ × (Z × Ω)) := ψ ((c (q p.2.1)).Q p.1.toNNReal p.2.2, B p.1.toNNReal p.2.2)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hBc hm
  have hQm := clipped_family_joint_measurable c
  have hFm : Measurable F := hψc.measurable.comp
    ((hQm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((hq.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))).prodMk
    (hBm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))))
  have hFc (z : Z) (ω : Ω) : Continuous (fun t : ℝ => F (t,(z,ω))) :=
    hψc.comp ((((c (q z)).lipschitz ω).continuous.comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).prodMk
      ((hBc ω).comp continuous_real_toNNReal))
  have hFb (t : ℝ) (z : Z) (ω : Ω) : |F (t,(z,ω))| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK ((c (q z)).Q t.toNNReal ω, B t.toNNReal ω)
  let C (n i : ℕ) (p : Z × Ω) := if σ p ≤ dyadicTime T n i ∧ dyadicTime T n i < τ p then
    F (dyadicTime T n i,p) else 0
  have hCa (n i : ℕ) : @Measurable (Z × Ω) ℝ
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) (dyadicTime T n i)))
      (borel ℝ) (C n i) := by
    have hQ := clipped_family_past_measurable c (dyadicTime T n i)
    have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted (dyadicTime T n i)
    let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) (dyadicTime T n i)
    have hh := hψc.measurable.comp
      ((hQ.comp ((hq.comp measurable_fst).prodMk measurable_snd)).prodMk (hBa.comp measurable_snd))
    change Measurable (C n i)
    dsimp only [C, F]
    simp only [Real.toNNReal_coe]
    have hsa : MeasurableSet {p : Z × Ω | σ p ≤ dyadicTime T n i} := by
      simpa only [Set.compl_ofPred, not_lt] using (hσa (dyadicTime T n i)).compl
    exact hh.ite (hsa.inter (hτa (dyadicTime T n i))) measurable_const
  have hCm (n i : ℕ) : Measurable (C n i) :=
    (hCa n i).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (Filtration.le _ _))) le_rfl
  have hCb (n i : ℕ) (z : Z) (ω : Ω) : |C n i (z,ω)| ≤ K := by
    dsimp only [C]
    split_ifs
    · exact hFb _ _ _
    · simp
  let Y (p : Z × Ω) := greenLogDensity κ ((c (q p.1)).Q (τ p) p.2) (B (τ p) p.2) -
    greenLogDensity κ ((c (q p.1)).Q (σ p) p.2) (B (σ p) p.2)
  have hYm : Measurable Y :=
    (((greenLogDensity_contDiff κ).continuous.measurable.comp
      ((hQm.comp (hτm.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))).prodMk
        (hBm.comp (hτm.prodMk measurable_snd))))).sub
      ((greenLogDensity_contDiff κ).continuous.measurable.comp
        ((hQm.comp (hσm.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))).prodMk
          (hBm.comp (hσm.prodMk measurable_snd))))
  have hlim (z : Z) : ∀ᵐ ω ∂P, Tendsto
      (fun n => driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z,ω)) (2^n) ω)
      atTop (𝓝 (Y (z,ω))) := by
    have hτlim := (c (q z)).stopped_green_ito hB hBc hκ hκ8 R hR T
      (fun ω => τ (z,ω)) (hτs z) (hτb z) (hinside z)
    have hσlim := (c (q z)).stopped_green_ito hB hBc hκ hκ8 R hR T
      (fun ω => σ (z,ω)) (hσs z) (fun ω => (hστ (z,ω)).trans (hτb z ω))
      (fun ω t ht => hinside z ω t (ht.trans (hστ (z,ω))))
    filter_upwards [hτlim, hσlim] with ω hτl hσl
    have he (n i : ℕ) : C n i (z,ω) =
        (if dyadicTime T n i < τ (z,ω) then
          greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) -
        (if dyadicTime T n i < σ (z,ω) then
          greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) := by
      dsimp only [C, F]
      rw [Real.toNNReal_coe]
      by_cases ht : dyadicTime T n i < τ (z,ω)
      · rw [hψeq _ _ (hinside z ω _ ht.le).1]
        by_cases hs : σ (z,ω) ≤ dyadicTime T n i
        · simp [ht, hs, not_lt.mpr hs]
        · simp [ht, hs, lt_of_not_ge hs]
      · have hs : ¬ dyadicTime T n i < σ (z,ω) := fun h => ht (h.trans_le (hστ (z,ω)))
        simp [ht, hs]
    have hs (n : ℕ) : driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z,ω)) (2^n) ω =
        (∑ i ∈ Finset.range (2^n),
          (if dyadicTime T n i < τ (z,ω) then
            greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) *
            (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) -
        (∑ i ∈ Finset.range (2^n),
          (if dyadicTime T n i < σ (z,ω) then
            greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0) *
            (B (dyadicTime T n (i+1)) ω - B (dyadicTime T n i) ω)) := by
      simp only [driverPredictableSum, he, sub_mul, Finset.sum_sub_distrib]
    simpa only [hs, Y, sub_sub_sub_cancel_right] using hτl.sub hσl
  let Q (ω : Ω) := ∫ t in (0 : ℝ)..(T : ℝ),
    (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then F (t,(z,ω)) else 0 ∂ν)^2
  have hE : ∀ᵐ ω ∂P, Tendsto (fun n => driverPredictableEnergy (dyadicTime T n)
      (fun i ω => ∫ z, C n i (z,ω) ∂ν) (2^n) ω) atTop (𝓝 (Q ω)) := by
    apply Eventually.of_forall
    intro ω
    have hfm : Measurable (fun p : ℝ × Z => F (p.1,(p.2,ω))) :=
      hFm.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
    have hsm := hσm.comp (measurable_id.prodMk (measurable_const (a := ω)))
    have htm := hτm.comp (measurable_id.prodMk (measurable_const (a := ω)))
    have hh := area_window_pair_energy_tendsto (ν := ν) hfm (fun z => hFc z ω) hsm htm T
      (fun z => hτb z ω) K K.coe_nonneg (fun t z => hFb t z ω)
    rw [area_window_energy_identity hfm hsm htm T (fun z => hτb z ω) K K.coe_nonneg
      (fun t z => hFb t z ω)] at hh
    simpa only [driverPredictableEnergy, dyadicTime_step, C, areaWindowSample, Q, Function.comp_def, id_eq] using hh
  have hh := brownian_area_exponential_limit hB hm T C hCm hCa K K.coe_nonneg hCb Y hYm hlim Q hE θ
  have hQeq (ω : Ω) : Q ω = ∫ t in (0 : ℝ)..(T : ℝ),
      (∫ z, if (σ (z,ω) : ℝ) ≤ t ∧ t < (τ (z,ω) : ℝ) then
        greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le T.coe_nonneg] at ht
    dsimp only []
    apply congrArg (fun x : ℝ => x^2)
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only []
    split_ifs with htτ
    · have htn : t.toNNReal ≤ τ (z,ω) := Real.toNNReal_le_iff_le_coe.mpr htτ.2.le
      dsimp only [F]
      have he := hψeq _ _ (hinside z ω _ htn).1
      simpa only [Real.coe_toNNReal _ ht.1] using he
    · rfl
  simpa only [Y, hQeq] using hh

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable BrownianField

 

theorem clipped_spatial_green_exponential
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {ν : Measure Z} {P : Measure Ω} [IsFiniteMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ lo hi : ℝ) (hle : lo ≤ hi) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q)
    (R : ℝ) (hR : 0 ≤ R) (T : ℝ≥0)
    (τ : Z × Ω → ℝ≥0) (hτm : Measurable τ)
    (hτa : ∀ t : ℝ≥0, @MeasurableSet (Z × Ω)
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) t))
      {p | t < τ p})
    (hτs : ∀ z, IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ (z, ω) : WithTop ℝ≥0)))
    (hτb : ∀ z ω, τ (z,ω) ≤ T)
    (hinside : ∀ z ω t, t ≤ τ (z,ω) →
      ‖((c (q z)).Q t ω, B t ω)‖ ≤ R ∧
        lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi)
    (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, greenLogDensity κ ((c (q z)).Q (τ (z,ω)) ω) (B (τ (z,ω)) ω) -
        greenLogDensity κ (q z) 0 ∂ν) -
      θ^2 * (∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if t < (τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) / 2)) ∂P) ≤ 1 := by
  classical
  obtain ⟨φ, hφ, hφc, hφeq, hφD, hφ2⟩ := exists_compact_green_field κ R hR
  let ψ := spatialPartial φ 1
  have hψc : Continuous ψ := (spatialPartial_smooth φ hφ 1).continuous
  obtain ⟨K, hK, _⟩ := compact_smooth_bounded_lipschitz ψ
    (spatialPartial_smooth φ hφ 1) (spatialPartial_compact φ hφc 1)
  have hψeq (q' : ℂ × ℝ) (x : ℝ) (hb : ‖(q',x)‖ ≤ R) :
      ψ (q',x) = greenLogCoefficient κ q' x := by
    rw [show ψ (q',x) = deriv (fun y => φ (q',y)) x by
      simp only [ψ, spatialPartial_eq_iteratedDeriv φ hφ, iteratedDeriv_one]]
    rw [deriv_fiber_fderiv φ (hφ.differentiable (by simp)), hφD q' x hb,
      ← deriv_fiber_fderiv _ ((greenLogDensity_contDiff κ).differentiable (by simp))]
    exact (greenLogDensity_spatial_derivative κ q' x).deriv
  let F (p : ℝ × (Z × Ω)) := ψ ((c (q p.2.1)).Q p.1.toNNReal p.2.2, B p.1.toNNReal p.2.2)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hBc hm
  have hQm := clipped_family_joint_measurable c
  have hFm : Measurable F := hψc.measurable.comp
    ((hQm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      ((hq.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))).prodMk
    (hBm.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))))
  have hFc (z : Z) (ω : Ω) : Continuous (fun t : ℝ => F (t,(z,ω))) :=
    hψc.comp ((((c (q z)).lipschitz ω).continuous.comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).prodMk
      ((hBc ω).comp continuous_real_toNNReal))
  have hFb (t : ℝ) (z : Z) (ω : Ω) : |F (t,(z,ω))| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK ((c (q z)).Q t.toNNReal ω, B t.toNNReal ω)
  let C (n i : ℕ) (p : Z × Ω) := if dyadicTime T n i < τ p then
    F (dyadicTime T n i,p) else 0
  have hCa (n i : ℕ) : @Measurable (Z × Ω) ℝ
      (mZ.prod (Filtration.natural B (fun s => (hm s).stronglyMeasurable) (dyadicTime T n i)))
      (borel ℝ) (C n i) := by
    have hQ := clipped_family_past_measurable c (dyadicTime T n i)
    have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted (dyadicTime T n i)
    let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) (dyadicTime T n i)
    have hh := hψc.measurable.comp
      ((hQ.comp ((hq.comp measurable_fst).prodMk measurable_snd)).prodMk (hBa.comp measurable_snd))
    change Measurable (C n i)
    dsimp only [C, F]
    simp only [Real.toNNReal_coe]
    exact hh.ite (hτa (dyadicTime T n i)) measurable_const
  have hCm (n i : ℕ) : Measurable (C n i) :=
    (hCa n i).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (Filtration.le _ _))) le_rfl
  have hCb (n i : ℕ) (z : Z) (ω : Ω) : |C n i (z,ω)| ≤ K := by
    dsimp only [C]
    split_ifs
    · exact hFb _ _ _
    · simp
  let Y (p : Z × Ω) := greenLogDensity κ ((c (q p.1)).Q (τ p) p.2) (B (τ p) p.2) -
    greenLogDensity κ (q p.1) 0
  have hYm : Measurable Y :=
    (((greenLogDensity_contDiff κ).continuous.measurable.comp
      ((hQm.comp (hτm.prodMk ((hq.comp measurable_fst).prodMk measurable_snd))).prodMk
        (hBm.comp (hτm.prodMk measurable_snd))))).sub
      ((greenLogDensity_contDiff κ).continuous.measurable.comp ((hq.comp measurable_fst).prodMk measurable_const))
  have hlim (z : Z) : ∀ᵐ ω ∂P, Tendsto
      (fun n => driverPredictableSum B (dyadicTime T n) (fun i ω => C n i (z,ω)) (2^n) ω)
      atTop (𝓝 (Y (z,ω))) := by
    have hh := (c (q z)).stopped_green_ito hB hBc hκ hκ8 R hR T
      (fun ω => τ (z,ω)) (hτs z) (hτb z) (hinside z)
    have he (n i : ℕ) (ω : Ω) : C n i (z,ω) = if dyadicTime T n i < τ (z,ω) then
        greenLogCoefficient κ ((c (q z)).Q (dyadicTime T n i) ω) (B (dyadicTime T n i) ω) else 0 := by
      dsimp only [C, F]
      rw [Real.toNNReal_coe]
      split_ifs with ht
      · exact hψeq _ _ (hinside z ω _ ht.le).1
      · rfl
    simpa only [driverPredictableSum, he, Y] using hh
  let Q (ω : Ω) := ∫ t in (0 : ℝ)..(T : ℝ),
    (∫ z, if t < (τ (z,ω) : ℝ) then F (t,(z,ω)) else 0 ∂ν)^2
  have hE : ∀ᵐ ω ∂P, Tendsto (fun n => driverPredictableEnergy (dyadicTime T n)
      (fun i ω => ∫ z, C n i (z,ω) ∂ν) (2^n) ω) atTop (𝓝 (Q ω)) := by
    apply Eventually.of_forall
    intro ω
    have hfm : Measurable (fun p : ℝ × Z => F (p.1,(p.2,ω))) :=
      hFm.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
    have htm := hτm.comp (measurable_id.prodMk (measurable_const (a := ω)))
    have hh := area_prefix_energy_tendsto (ν := ν) hfm (fun z => hFc z ω) htm T
      (fun z => hτb z ω) K K.coe_nonneg (fun t z => hFb t z ω)
    rw [area_prefix_energy_identity hfm htm T (fun z => hτb z ω) K K.coe_nonneg
      (fun t z => hFb t z ω)] at hh
    simpa only [driverPredictableEnergy, dyadicTime_step, C, areaPrefixSample, Q, Function.comp_def, id_eq] using hh
  have hh := brownian_area_exponential_limit hB hm T C hCm hCa K K.coe_nonneg hCb Y hYm hlim Q hE θ
  have hQeq (ω : Ω) : Q ω = ∫ t in (0 : ℝ)..(T : ℝ),
      (∫ z, if t < (τ (z,ω) : ℝ) then
        greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le T.coe_nonneg] at ht
    dsimp only []
    apply congrArg (fun x : ℝ => x^2)
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    dsimp only []
    split_ifs with htτ
    · have htn : t.toNNReal ≤ τ (z,ω) := Real.toNNReal_le_iff_le_coe.mpr htτ.le
      dsimp only [F]
      have he := hψeq _ _ (hinside z ω _ htn).1
      simpa only [Real.coe_toNNReal _ ht.1] using he
    · rfl
  simpa only [Y, hQeq] using hh

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

def spatialFiltration {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    (f : Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 (mZ.prod mΩ) where
  seq t := mZ.prod (f t)
  mono' _ _ h := sup_le_sup le_rfl (MeasurableSpace.comap_mono (f.mono h))
  le' t := sup_le_sup le_rfl (MeasurableSpace.comap_mono (f.le t))

lemma spatial_stopping_section {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 mΩ} {τ : Z × Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (spatialFiltration (Z := Z) f) τ) (z : Z) :
    IsStoppingTime f (fun ω => τ (z,ω)) := by
  intro t
  have h := hτ t
  let : MeasurableSpace Ω := f t
  exact h.preimage (measurable_const.prodMk measurable_id)

 

structure SpatialLogLocalization
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (R : ℝ) (T : ℝ≥0) where
  τ : Z × Ω → ℝ≥0
  stopping : IsStoppingTime
    (spatialFiltration (Z := Z) (Filtration.natural B (fun s => (hm s).stronglyMeasurable)))
    (fun p => (τ p : WithTop ℝ≥0))
  bound : ∀ p, τ p ≤ T
  inside : ∀ z ω t, t ≤ τ (z,ω) → ‖((c (q z)).Q t ω, B t ω)‖ ≤ R ∧
    lo ≤ ((c (q z)).Q t ω).1.im ∧ ((c (q z)).Q t ω).1.im ≤ hi
  boundary : ∀ z ω, τ (z,ω) < T →
    ‖((c (q z)).Q (τ (z,ω)) ω, B (τ (z,ω)) ω)‖ = R ∨
      ((c (q z)).Q (τ (z,ω)) ω).1.im = lo ∨ ((c (q z)).Q (τ (z,ω)) ω).1.im = hi

 

theorem exists_spatial_log_localization
    {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ lo hi : ℝ) (hle : lo ≤ hi)
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (q : Z → ℂ × ℝ) (hq : Measurable q) (R : ℝ) (T : ℝ≥0)
    (hinit : ∀ z, ‖(q z, (0 : ℝ))‖ ≤ R ∧ lo ≤ (q z).1.im ∧ (q z).1.im ≤ hi) :
    Nonempty (SpatialLogLocalization c q R T) := by
  let f := spatialFiltration (Z := Z) (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
  let D (t : ℝ≥0) (p : Z × Ω) := min (R - ‖((c (q p.1)).Q t p.2, B t p.2)‖)
    (min (((c (q p.1)).Q t p.2).1.im - lo) (hi - ((c (q p.1)).Q t p.2).1.im))
  have hDa : Adapted f D := by
    intro t
    have hQ := clipped_family_past_measurable c t
    have hBa := (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable)).adapted t
    let : MeasurableSpace Ω := Filtration.natural B (fun s => (hm s).stronglyMeasurable) t
    have hc := hQ.comp ((hq.comp measurable_fst).prodMk measurable_snd)
    have hBb := hBa.comp (@measurable_snd Z Ω mZ _)
    exact (measurable_const.sub (hc.prodMk hBb).norm).min
      (((Complex.continuous_im.measurable.comp hc.fst).sub_const lo).min
        (measurable_const.sub (Complex.continuous_im.measurable.comp hc.fst)))
  have hDc (p : Z × Ω) : Continuous (fun t => D t p) := by
    have hc := ((c (q p.1)).lipschitz p.2).continuous.comp NNReal.continuous_coe
    exact (continuous_const.sub (hc.prodMk (hBc p.2)).norm).min
      (((Complex.continuous_im.comp hc.fst).sub continuous_const).min
        (continuous_const.sub (Complex.continuous_im.comp hc.fst)))
  have hD0 (p : Z × Ω) : 0 ≤ D 0 p := by
    simpa only [D, NNReal.coe_zero, (c (q p.1)).initial, hB0, le_min_iff, sub_nonneg]
      using hinit p.1
  obtain ⟨τ, hτ, hb, hin, hpre, hboundary⟩ := first_margin_stopping f D hDa hDc hD0 T
  refine ⟨⟨τ, hτ, hb, ?_, ?_⟩⟩
  · intro z ω t ht
    simpa only [D, le_min_iff, sub_nonneg] using hin (z,ω) t ht
  · intro z ω ht
    have hh := hboundary (z,ω) ht
    have hle' := hin (z,ω) (τ (z,ω)) le_rfl
    dsimp only [D] at hh hle'
    rw [min_eq_iff, min_eq_iff] at hh
    rcases hh with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl (sub_eq_zero.mp h).symm
    · rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h).symm)

namespace SpatialLogLocalization
variable {Z Ω : Type*} [mZ : MeasurableSpace Z] [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ lo hi : ℝ} {hle : lo ≤ hi}
  {c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q}
  {q : Z → ℂ × ℝ} {R : ℝ} {T : ℝ≥0}

lemma measurable (a : SpatialLogLocalization c q R T) : Measurable a.τ :=
  stopping_time_measurable_nnreal a.stopping

lemma exponential {P : Measure Ω} {ν : Measure Z} [IsFiniteMeasure ν]
    (a : SpatialLogLocalization c q R T) (hq : Measurable q)
    (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hκ : 0 < κ) (hκ8 : κ < 8) (hR : 0 ≤ R) (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (θ * (∫ z, greenLogDensity κ ((c (q z)).Q (a.τ (z,ω)) ω) (B (a.τ (z,ω)) ω) -
        greenLogDensity κ (q z) 0 ∂ν) -
      θ^2 * (∫ t in (0 : ℝ)..(T : ℝ),
        (∫ z, if t < (a.τ (z,ω) : ℝ) then
          greenLogCoefficient κ ((c (q z)).Q t ω) (B t.toNNReal ω) else 0 ∂ν)^2) / 2)) ∂P) ≤ 1 := by
  exact clipped_spatial_green_exponential hm hB hBc κ lo hi hle hκ hκ8 c q hq R hR T
    a.τ a.measurable (stopping_before_measurable a.stopping)
    (spatial_stopping_section a.stopping) (fun z ω => a.bound (z,ω)) a.inside θ

end SpatialLogLocalization
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma greenLogCoefficient_logCoordinates
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (κ b : ℝ) (z : ℂ) (t : ℝ≥0) (hz : z ∈ survivingDomain γ t)
    (hUb : U t = Real.sqrt κ * b) :
    greenLogCoefficient κ (logLoewnerCoordinates G z t) b =
      greenBrownianCoefficient κ U γ G t z := by
  rw [greenLogCoefficient, greenLogDensity_logCoordinates hU h κ b z t hz hUb,
    greenLogNormSq_logCoordinates κ b G z t (h.imag_positive t z hz),
    logCoordinates_re, Complex.normSq_eq_norm_sq, greenBrownianCoefficient, hUb]
  simp only [Complex.sub_re, Complex.ofReal_re]
  ring

lemma clipped_chart_identification
    {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    (c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (ω : Ω) (τ : ℝ≥0)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F)
    (hin : ∀ t : ℝ≥0, t ≤ τ →
      lo ≤ ((c (initialLogCoordinates z)).Q t ω).1.im ∧
        ((c (initialLogCoordinates z)).Q t ω).1.im ≤ hi) :
    z ∈ survivingDomain γ τ ∧ ∀ t : ℝ≥0, t ≤ τ →
      (c (initialLogCoordinates z)).Q t ω = logLoewnerCoordinates G z t := by
  let d := c (initialLogCoordinates z)
  have hd (s : ℝ) (hs : s ∈ Icc 0 (τ : ℝ)) := (d.derivative ω s hs.1).mono
    (show Icc (0 : ℝ) (τ : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hb (s : ℝ) (hs : s ∈ Icc 0 (τ : ℝ)) : (d.Q s ω).1.im ∈ Icc lo hi := by
    have hh := hin s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)
    simpa only [Set.mem_Icc, Real.coe_toNNReal _ hs.1] using hh
  obtain ⟨hl, he⟩ := clipped_log_identification ((hBc ω).const_mul _) hw z hz τ
    lo hi hle (fun s => d.Q s ω) (d.initial ω) hd hb
  exact ⟨hl, fun t ht => by simpa only [Real.toNNReal_coe] using he ⟨t.coe_nonneg, ht⟩⟩

lemma SpatialLogLocalization.chart_identification
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    {κ lo hi : ℝ} {hle : lo ≤ hi}
    {c : ∀ q : ℂ × ℝ, ClippedLogSolution B hm κ lo hi hle q}
    {z : Z → ℂ} {R : ℝ} {T : ℝ≥0}
    (a : SpatialLogLocalization c (fun x => initialLogCoordinates (z x)) R T)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (x : Z) (hz : z x ∈ upperHalfPlane) (ω : Ω)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) :
    z x ∈ survivingDomain γ (a.τ (x,ω)) ∧
      ∀ t : ℝ≥0, t ≤ a.τ (x,ω) →
        (c (initialLogCoordinates (z x))).Q t ω = logLoewnerCoordinates G (z x) t := by
  let d := c (initialLogCoordinates (z x))
  have hd (s : ℝ) (hs : s ∈ Icc 0 (a.τ (x,ω) : ℝ)) := (d.derivative ω s hs.1).mono
    (show Icc (0 : ℝ) (a.τ (x,ω) : ℝ) ⊆ Ici 0 from fun _ hx => hx.1)
  have hb (s : ℝ) (hs : s ∈ Icc 0 (a.τ (x,ω) : ℝ)) : (d.Q s ω).1.im ∈ Icc lo hi := by
    have hh := (a.inside x ω s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)).2
    simpa only [Set.mem_Icc, Real.coe_toNNReal _ hs.1] using hh
  obtain ⟨hl, he⟩ := clipped_log_identification ((hBc ω).const_mul _) hw (z x) hz (a.τ (x,ω))
    lo hi hle (fun s => d.Q s ω) (d.initial ω) hd hb
  exact ⟨hl, fun t ht => by simpa only [Real.toNNReal_coe] using he ⟨t.coe_nonneg, ht⟩⟩

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma stopped_difference_max {T E : Type*} [LinearOrder T] [AddGroup E]
    (M : T → E) (s t : T) :
    M t - M (min t s) = M (max s t) - M s := by
  by_cases ht : t ≤ s
  · rw [min_eq_left ht, max_eq_left ht, sub_self, sub_self]
  · rw [min_eq_right (le_of_not_ge ht), max_eq_right (le_of_not_ge ht)]

 

theorem closed_stop_limit_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (𝓕 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → ℝ) (Z W : Ω → ℝ)
    (hZ : Integrable Z μ)
    (hStop : ∀ (ρ : Ω → ℝ≥0) (hρ : IsStoppingTime 𝓕 (fun ω => (ρ ω : WithTop ℝ≥0))),
      (fun ω => M (ρ ω) ω) =ᵐ[μ] μ[Z | hρ.measurableSpace])
    (σ : ℝ≥0 → Ω → ℝ≥0)
    (hσ : ∀ t, IsStoppingTime 𝓕 (fun ω => (σ t ω : WithTop ℝ≥0)))
    (hσle : ∀ t ω, σ t ω ≤ t)
    (hσmin : ∀ s t, s ≤ t → ∀ ω, σ s ω = min (σ t ω) s)
    (K : ℝ) (hbound : ∀ t ω, ‖M t ω‖ ≤ K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (σ n ω) ω) atTop (𝓝 (W ω)))
    (s : ℝ≥0) : (fun ω => M (σ s ω) ω) =ᵐ[μ] μ[W | 𝓕 s] := by
  have hInt (ρ : Ω → ℝ≥0) (hρ : IsStoppingTime 𝓕 (fun ω => (ρ ω : WithTop ℝ≥0))) :
      Integrable (fun ω => M (ρ ω) ω) μ :=
    integrable_condExp.congr (hStop ρ hρ).symm
  have hWi : Integrable W μ := by
    apply Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n : ℕ => (hInt (σ n) (hσ n)).aestronglyMeasurable) hlim) K
    filter_upwards [hlim] with ω hω
    exact le_of_tendsto hω.norm (Eventually.of_forall fun n => hbound (σ n ω) ω)
  have hss : (hσ s).measurableSpace ≤ 𝓕 s :=
    (hσ s).measurableSpace_le_of_le_const (fun ω => by exact_mod_cast hσle s ω)
  have hMs : AEStronglyMeasurable[𝓕 s] (fun ω => M (σ s ω) ω) μ :=
    ((stronglyMeasurable_condExp.mono hss).aestronglyMeasurable).congr (hStop (σ s) (hσ s)).symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hWi
    (fun _ _ _ => (hInt (σ s) (hσ s)).integrableOn) _ hMs
  intro A hA _
  have hI : Tendsto (fun n : ℕ => ∫ ω in A, M (σ n ω) ω ∂μ) atTop (𝓝 (∫ ω in A, W ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hInt (σ n) (hσ n)).integrableOn.aestronglyMeasurable)
      (integrable_const _) _ (ae_restrict_of_ae hlim)
    intro n
    exact Eventually.of_forall fun ω => hbound (σ n ω) ω
  have he : ∀ᶠ n : ℕ in atTop, (∫ ω in A, M (σ n ω) ω ∂μ) =
      ∫ ω in A, M (σ s ω) ω ∂μ := by
    filter_upwards [eventually_ge_atTop (⌈(s : ℝ)⌉₊)] with n hn
    have hsn : s ≤ (n : ℝ≥0) := by
      exact_mod_cast (Nat.le_of_ceil_le hn)
    let ρ (ω : Ω) := max s (σ n ω)
    have hρ : IsStoppingTime 𝓕 (fun ω => (ρ ω : WithTop ℝ≥0)) := by
      simpa only [ρ, WithTop.coe_max] using (isStoppingTime_const 𝓕 s).max (hσ n)
    have hFρ : 𝓕 s ≤ hρ.measurableSpace :=
      hρ.le_measurableSpace_of_const_le (fun ω => by exact_mod_cast (le_max_left s (σ n ω)))
    have hFc : 𝓕 s ≤ (isStoppingTime_const 𝓕 s).measurableSpace :=
      (isStoppingTime_const 𝓕 s).le_measurableSpace_of_const_le (fun _ => le_rfl)
    have hsetρ : (∫ ω in A, M (ρ ω) ω ∂μ) = ∫ ω in A, Z ω ∂μ := by
      rw [integral_congr_ae (ae_restrict_of_ae (hStop ρ hρ))]
      have : IsFiniteMeasure (μ.trim hρ.measurableSpace_le) := isFiniteMeasure_trim _
      exact setIntegral_condExp hρ.measurableSpace_le hZ (hFρ A hA)
    have hsetc : (∫ ω in A, M s ω ∂μ) = ∫ ω in A, Z ω ∂μ := by
      rw [integral_congr_ae (ae_restrict_of_ae (hStop (fun _ => s) (isStoppingTime_const 𝓕 s)))]
      have : IsFiniteMeasure (μ.trim (isStoppingTime_const 𝓕 s).measurableSpace_le) := isFiniteMeasure_trim _
      exact setIntegral_condExp (isStoppingTime_const 𝓕 s).measurableSpace_le hZ (hFc A hA)
    have hid : (∫ ω in A, M (σ n ω) ω - M (σ s ω) ω ∂μ) =
        ∫ ω in A, M (ρ ω) ω - M s ω ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        change M (σ n ω) ω - M (σ s ω) ω = M (ρ ω) ω - M s ω
        rw [hσmin s n hsn ω]
        exact stopped_difference_max (fun t => M t ω) s (σ n ω)
    rw [integral_sub (hInt (σ n) (hσ n)).integrableOn (hInt (σ s) (hσ s)).integrableOn,
      integral_sub (hInt ρ hρ).integrableOn
        (hInt (fun _ => s) (isStoppingTime_const 𝓕 s)).integrableOn, hsetρ, hsetc, sub_self] at hid
    exact sub_eq_zero.mp hid
  have hc : Tendsto (fun n : ℕ => ∫ ω in A, M (σ n ω) ω ∂μ) atTop
      (𝓝 (∫ ω in A, M (σ s ω) ω ∂μ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn using hn.symm
  exact (tendsto_nhds_unique hI hc).symm

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma boundedSpatialHit_le_time (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (t : ℝ≥0) :
    boundedSpatialHit γ z r t ≤ t := by
  apply WithTop.coe_le_coe.mp
  rw [boundedSpatialHit_coe]
  exact min_le_right _ _

lemma boundedSpatialHit_min (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    boundedSpatialHit γ z r s = min (boundedSpatialHit γ z r t) s := by
  apply WithTop.coe_injective
  rw [WithTop.coe_min, boundedSpatialHit_coe, boundedSpatialHit_coe, min_assoc,
    min_eq_right (WithTop.coe_le_coe.mpr hst)]

namespace RegularSLEPresentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialGreen_condExp_of_level [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (hz : z ∈ upperHalfPlane) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im)
    (u : ℝ) (hu : 0 ≤ u) (hlevel : (2 * z.im) * Real.exp (-u) < r)
    (s : ℝ≥0) :
    (fun ω : a.samples => greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r s) z) =ᵐ[P.comap Subtype.val]
      (P.comap Subtype.val)[fun ω : a.samples => spatialGreenWeight κ
        (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r | a.filtration s] := by
  let μ : Measure a.samples := P.comap Subtype.val
  let : IsProbabilityMeasure μ := a.probability
  have hBm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  obtain ⟨M, Z, hM, hZ, hMb, hZb, hClosed, hStop, heq, hNoHit⟩ :=
    exists_physical_green_stopping_regular a.brownian hBm a.continuous_B a.zero_B
      κ hκ hκ8 (γ ∘ Subtype.val) a.G a.F (Eventually.of_forall a.witness) z hz u hu
  let σ (t : ℝ≥0) (ω : a.samples) := boundedSpatialHit (γ ω) z r t
  have hσ (t : ℝ≥0) : IsStoppingTime a.filtration (fun ω => (σ t ω : WithTop ℝ≥0)) :=
    a.boundedSpatialHit_stopping z r t
  dsimp only [filtration] at hσ
  let W (ω : a.samples) := spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
    (γ ω) (a.G ω) z r
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M (σ n ω) ω) atTop (𝓝 (W ω)) := by
    filter_upwards [heq, hNoHit] with ω he hn
    simpa only [he.1, σ, W, Function.comp_apply] using
      (a.witness ω).spatialGreen_limit ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel hn
  have hb (t : ℝ≥0) (ω : a.samples) :
      ‖M t ω‖ ≤ Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hMb t ω).1]
    exact (hMb t ω).2
  have hc := closed_stop_limit_condExp a.filtration M Z W hZ hStop σ hσ
    (fun t ω => boundedSpatialHit_le_time (γ ω) z r t)
    (fun t v htv ω => boundedSpatialHit_min (γ ω) z r t v htv) _ hb hlim s
  refine EventuallyEq.trans ?_ hc
  filter_upwards [heq] with ω he
  rw [he.1]
  exact ((a.witness ω).physicalGreen_eq_before_spatial
    ((a.continuous_B ω).const_mul _) κ z r hr hy u hlevel (σ s ω)
    (boundedSpatialHit_le (γ ω) z r s)).symm

 

theorem spatialGreen_condExp [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ8 : κ < 8)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im) (s : ℝ≥0) :
    (fun ω : a.samples => greenDensity κ (fun t => Real.sqrt κ * a.B t ω)
      (γ ω) (a.G ω) (boundedSpatialHit (γ ω) z r s) z) =ᵐ[P.comap Subtype.val]
      (P.comap Subtype.val)[fun ω : a.samples => spatialGreenWeight κ
        (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r | a.filtration s] := by
  have hz : z ∈ upperHalfPlane := hr.trans_le hy
  let u := Real.log (4 * z.im / r)
  have hratio : 0 < 4 * z.im / r := div_pos (mul_pos (by norm_num) hz) hr
  have hu : 0 ≤ u := Real.log_nonneg ((le_div_iff₀ hr).mpr (by linarith))
  have hlev : (2 * z.im) * Real.exp (-u) = r / 2 := by
    dsimp only [u]
    rw [Real.exp_neg, Real.exp_log hratio]
    field_simp [(show 0 < z.im from hz).ne']
    ring
  exact a.spatialGreen_condExp_of_level hκ hκ8 z hz r hr hy u hu
    (by rw [hlev]; linarith) s

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

end SLEExactGauge
end
end
end
end
end

end OAI
