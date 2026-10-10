import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffEntropyMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.AttenuationGap
import OAI.MathematicalPhysics.Boltzmann.Branching.EnergyCollisionMarginals
import OAI.MathematicalPhysics.Boltzmann.Branching.ExtendedProductionScale
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicFiniteMild
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar

namespace OAI

section

/-! # An L1 density bound on a fixed elastic collision window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def windowPartner (R : ℝ) (q : Velocity × Sphere) : ℝ :=
  (Metric.closedBall (0:Velocity) R).indicator (fun _ => 1) q.1

theorem windowPartner_measurable (R : ℝ) : Measurable (windowPartner R) :=
  (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp measurable_fst

theorem windowPartner_integrable (R : ℝ) :
    Integrable (windowPartner R) ((volume : Measure Velocity).prod sphereArea) := by
  have hi : Integrable ((Metric.closedBall (0:Velocity) R).indicator (fun _ => (1:ℝ))) :=
    (integrableOn_const (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  exact hi.comp_fst sphereArea

theorem singleDensity_window_norm_le {R : ℝ} (hR : 0 ≤ R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) :
    eLpNorm ((collisionWindow R).indicator (fun z => f (z.1.1,z.1.2.1))) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
    eLpNorm f 1 (μ.prod volume)*eLpNorm (windowPartner R) 1
      ((volume : Measure Velocity).prod sphereArea) := by
  let b : ((X × (Velocity × Velocity)) × Sphere) → ℝ := fun z =>
    f (z.1.1,z.1.2.1)*windowPartner R (z.1.2.2,z.2)
  have he : eLpNorm b 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      eLpNorm f 1 (μ.prod volume)*eLpNorm (windowPartner R) 1
        ((volume : Measure Velocity).prod sphereArea) := by
    have hm : AEStronglyMeasurable
        (fun z : (X × Velocity) × (Velocity × Sphere) => f z.1*windowPartner R z.2)
        ((μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea)) :=
      ((hfm.comp measurable_fst).mul ((windowPartner_measurable R).comp measurable_snd)).aestronglyMeasurable
    change eLpNorm ((fun z : (X × Velocity) × (Velocity × Sphere) => f z.1*windowPartner R z.2)
      ∘ collisionGrouping) 1 _ = _
    rw [eLpNorm_comp_measurePreserving hm (collisionGrouping_measurePreserving μ)]
    exact eLpNorm_mul_prod_one hfm (windowPartner_measurable R)
  rw [← he]
  apply eLpNorm_mono (hfm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst) |>.indicator
    (collisionWindow_measurable R)).aestronglyMeasurable
  intro z
  by_cases hz : z ∈ collisionWindow R
  · have hw : z.1.2.2 ∈ Metric.closedBall (0:Velocity) R := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using (collisionWindow_bounds hR hz).2
    simp only [indicator_of_mem hz,b,windowPartner,indicator_of_mem hw,mul_one,Function.comp_apply]
    exact le_rfl
  · simp only [indicator_of_notMem hz,norm_zero]
    exact norm_nonneg _

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The same finite collision window contains all four collision legs -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem mem_collisionWindow_scatter (R : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    scatterTriple z ∈ collisionWindow R ↔ z ∈ collisionWindow R := by
  change (‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2+
    ‖scatterRight z.1.2.1 z.1.2.2 z.2‖^2 ≤ R^2) ↔ _
  rw [scatter_energy _ _ _ (mem_sphere_zero_iff_norm.mp z.2.property)]
  rfl

theorem mem_collisionWindow_particleSwap (R : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    particleSwap z ∈ collisionWindow R ↔ z ∈ collisionWindow R := by
  change (‖z.1.2.2‖^2+‖z.1.2.1‖^2 ≤ R^2) ↔ _
  rw [add_comm]
  rfl

def windowSingleDensity (R : ℝ) (f : X × Velocity → ℝ) :
    ((X × (Velocity × Velocity)) × Sphere) → ℝ :=
  (collisionWindow R).indicator (fun z => f (z.1.1,z.1.2.1))

def windowDensitySum (R : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  windowSingleDensity R f z + windowSingleDensity R f (particleSwap z) +
    windowSingleDensity R f (scatterTriple z) +
    windowSingleDensity R f (particleSwap (scatterTriple z))

theorem windowSingleDensity_measurable (R : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (windowSingleDensity R f) := by
  apply Measurable.indicator _ (collisionWindow_measurable R)
  exact hfm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)

theorem windowDensitySum_measurable (R : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (windowDensitySum R f) := by
  have h := windowSingleDensity_measurable R hfm
  exact ((h.add (h.comp particleSwap.measurable)).add (h.comp scatterTriple_measurable)).add
    ((h.comp particleSwap.measurable).comp scatterTriple_measurable)

theorem windowDensitySum_eq (R : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    windowDensitySum R f z = (collisionWindow R).indicator (fun z =>
      rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
        (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))) z := by
  have hs := mem_collisionWindow_scatter R z
  have hp := mem_collisionWindow_particleSwap R z
  have hps := mem_collisionWindow_particleSwap R (scatterTriple z)
  by_cases hz : z ∈ collisionWindow R
  · have hs' := hs.mpr hz
    have hp' := hp.mpr hz
    have hps' := hps.mpr hs'
    simp only [windowDensitySum,windowSingleDensity,indicator_of_mem hz,
      indicator_of_mem hs',indicator_of_mem hp',indicator_of_mem hps']
    rfl
  · have hs' : scatterTriple z ∉ collisionWindow R := fun h => hz (hs.mp h)
    have hp' : particleSwap z ∉ collisionWindow R := fun h => hz (hp.mp h)
    have hps' : particleSwap (scatterTriple z) ∉ collisionWindow R := fun h => hs' (hps.mp h)
    simp only [windowDensitySum,windowSingleDensity,indicator_of_notMem hz,
      indicator_of_notMem hs',indicator_of_notMem hp',indicator_of_notMem hps',add_zero]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The four collision legs have one common local L1 bound -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
private theorem four_add_norm_le {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (a b c d : Y → ℝ) :
    eLpNorm (((a+b)+c)+d) 1 ν ≤
      ((eLpNorm a 1 ν+eLpNorm b 1 ν)+eLpNorm c 1 ν)+eLpNorm d 1 ν := by
  have h1 : eLpNorm (a+b) 1 ν ≤ eLpNorm a 1 ν+eLpNorm b 1 ν :=
    eLpNorm_add_le (by norm_num)
  have h2 : eLpNorm ((a+b)+c) 1 ν ≤ eLpNorm (a+b) 1 ν+eLpNorm c 1 ν :=
    eLpNorm_add_le (by norm_num)
  have h3 : eLpNorm (((a+b)+c)+d) 1 ν ≤ eLpNorm ((a+b)+c) 1 ν+eLpNorm d 1 ν :=
    eLpNorm_add_le (by norm_num)
  have h2' : eLpNorm ((a+b)+c) 1 ν ≤ (eLpNorm a 1 ν+eLpNorm b 1 ν)+eLpNorm c 1 ν :=
    h2.trans (add_le_add h1 le_rfl)
  exact h3.trans (add_le_add h2' le_rfl)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem windowDensitySum_norm_le {R : ℝ} (hR : 0 ≤ R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) :
    eLpNorm (windowDensitySum R f) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
    4*(eLpNorm f 1 (μ.prod volume)*eLpNorm (windowPartner R) 1
      ((volume : Measure Velocity).prod sphereArea)) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let g := windowSingleDensity R f
  have hgm : Measurable g := windowSingleDensity_measurable R hfm
  have hgs : eLpNorm (g ∘ scatterTriple) 1 ν = eLpNorm g 1 ν :=
    eLpNorm_comp_measurePreserving hgm.aestronglyMeasurable (scatterTriple_measurePreserving μ)
  have hgp : eLpNorm (g ∘ particleSwap) 1 ν = eLpNorm g 1 ν :=
    eLpNorm_comp_measurePreserving hgm.aestronglyMeasurable (particleSwap_measurePreserving μ)
  have hgps : eLpNorm ((g ∘ particleSwap) ∘ scatterTriple) 1 ν = eLpNorm g 1 ν := by
    rw [eLpNorm_comp_measurePreserving (hgm.comp particleSwap.measurable).aestronglyMeasurable
      (scatterTriple_measurePreserving μ),hgp]
  have he : windowDensitySum R f = ((g+(g ∘ particleSwap))+(g ∘ scatterTriple))+
      ((g ∘ particleSwap) ∘ scatterTriple) := rfl
  change eLpNorm (windowDensitySum R f) 1 ν ≤ _
  rw [he]
  calc
    _ ≤ ((eLpNorm g 1 ν+eLpNorm (g ∘ particleSwap) 1 ν)+
        eLpNorm (g ∘ scatterTriple) 1 ν)+eLpNorm ((g ∘ particleSwap) ∘ scatterTriple) 1 ν :=
      four_add_norm_le ν g (g ∘ particleSwap) (g ∘ scatterTriple) ((g ∘ particleSwap) ∘ scatterTriple)
    _ = 4*eLpNorm g 1 ν := by rw [hgp,hgs,hgps]; ring
    _ ≤ _ := mul_le_mul' le_rfl (singleDensity_window_norm_le hR hfm)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Mass, scalar momentum, and energy balances for the full collision operator -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem full_test_collision_invariant {μ : Measure X} [SFinite μ]
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : ∀ z, collisionJump ψ z = 0) :
    (∫ p, ψ p*gainDensity f p ∂μ.prod volume) =
      ∫ p, ψ p*lossDensity f p ∂μ.prod volume := by
  exact (collision_test_marginal (postRate f) ψ hpost).2.trans
    ((full_collision_invariant f ψ hpre hpost hψ).trans
      (collision_test_marginal (preRate f) ψ hpre).2.symm)

theorem energy_collision_balance {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    (∫ p, ‖p.2‖^2*gainDensity f p ∂μ.prod volume) =
      ∫ p, ‖p.2‖^2*lossDensity f p ∂μ.prod volume :=
  full_test_collision_invariant f (fun p => ‖p.2‖^2)
    (preRate_energy_integrable hfm hfn hi) (postRate_energy_integrable hfm hfn hi)
    collisionJump_energy

omit [MeasurableSpace X] in
theorem coordinate_abs_le_energy (v : Velocity) (i : Fin 3) : |v i| ≤ 1+‖v‖^2 := by
  have h := PiLp.norm_apply_le v i
  simp only [Real.norm_eq_abs] at h
  nlinarith [sq_nonneg (‖v‖-1)]

theorem momentum_rate_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (he : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (i : Fin 3) :
    Integrable (fun z => (z.1.2.1 i)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (fun z => (z.1.2.1 i)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hpre := (preRate_integrable hfm hfn hp).add (preRate_energy_integrable hfm hfn he)
  have hpost := (postRate_integrable hfm hfn hp).add (postRate_energy_integrable hfm hfn he)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => z.1.2.1 i) := by
    fun_prop
  constructor
  · apply hpre.mono' (hm.mul (preRate_measurable hfm)).aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Pi.add_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (preRate_nonneg hfn z)]
    exact (mul_le_mul_of_nonneg_right (coordinate_abs_le_energy _ i)
      (preRate_nonneg hfn z)).trans_eq (by ring)
  · apply hpost.mono' (hm.mul ((preRate_measurable hfm).comp scatterTriple_measurable)).aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Pi.add_apply]
    change |(z.1.2.1 i)*postRate f z| ≤ postRate f z+‖z.1.2.1‖^2*postRate f z
    have hz : 0 ≤ postRate f z := preRate_nonneg hfn (scatterTriple z)
    rw [abs_mul,abs_of_nonneg hz]
    exact (mul_le_mul_of_nonneg_right (coordinate_abs_le_energy _ i)
      hz).trans_eq (by ring)

theorem momentum_collision_balance {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (he : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (i : Fin 3) :
    (∫ p : X × Velocity, (p.2 i)*gainDensity f p ∂μ.prod volume) =
      ∫ p : X × Velocity, (p.2 i)*lossDensity f p ∂μ.prod volume :=
  full_test_collision_invariant f (fun p => p.2 i)
    (momentum_rate_integrable hfm hfn hp he i).1
    (momentum_rate_integrable hfm hfn hp he i).2 (collisionJump_momentum i)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The actual attenuation tends to one on every finite collision window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem collisionAttenuation_window_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} (R : ℝ) (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm ((collisionWindow R).indicator
      (fun z => 1-rateMultiplier (N n) (f n) z)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let P := eLpNorm (windowPartner R) 1 ((volume : Measure Velocity).prod sphereArea)
  have hP : P ≠ ⊤ := (memLp_one_iff_integrable.mpr (windowPartner_integrable R)).eLpNorm_ne_top
  have hb n : eLpNorm ((collisionWindow R).indicator
      (fun z => 1-rateMultiplier (N n) (f n) z)) 1 ν ≤
      ENNReal.ofReal (2/N n)*(4*((B:ℝ≥0∞)*P)) := by
    have hm : AEStronglyMeasurable ((collisionWindow R).indicator
        (fun z => 1-rateMultiplier (N n) (f n) z)) ν :=
      (measurable_const.sub (rateMultiplier_measurable (N n) (hfm n))).indicator
        (collisionWindow_measurable R) |>.aestronglyMeasurable
    have he (z : (X × (Velocity × Velocity)) × Sphere) :
        |(collisionWindow R).indicator (fun z => 1-rateMultiplier (N n) (f n) z) z| ≤
        (2/N n)*|windowDensitySum R (f n) z| := by
      rw [windowDensitySum_eq]
      by_cases hz : z ∈ collisionWindow R
      · rw [indicator_of_mem hz,indicator_of_mem hz,
          abs_of_nonneg (rateSum_nonneg (hf n _) (hf n _) (hf n _) (hf n _))]
        exact rateMultiplier_gap_le (hN n) (hf n) z
      · simp only [indicator_of_notMem hz,abs_zero,mul_zero,le_refl]
    have he' := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (g := windowDensitySum R (f n)) (c := 2/N n) hm
      (ae_of_all ν (fun z => by simpa only [Real.norm_eq_abs] using he z)) 1
    exact he'.trans (mul_le_mul' le_rfl ((windowDensitySum_norm_le hR (hfm n)).trans
      (mul_le_mul' le_rfl (mul_le_mul' (hB n) le_rfl))))
  have hs : Tendsto (fun n => ENNReal.ofReal (2/N n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (tendsto_const_nhds.div_atTop hNt : Tendsto (fun n => (2:ℝ)/N n) atTop (𝓝 0))
  have ht := ENNReal.Tendsto.mul_const hs
    (Or.inr (show 4*((B:ℝ≥0∞)*P) ≠ ⊤ from by finiteness))
  simp only [zero_mul] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) hb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The moving cutoff preserves entropy dissipation at the actual weak collision limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def rateDissipation (μ : Measure X) (f : X × Velocity → ℝ) : ℝ≥0∞ :=
  (4:ℝ≥0∞)⁻¹*∫⁻ z, extendedEntropyProduction (postRate f z) (preRate f z)
    ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea

omit [MeasurableSpace X] in
theorem cutoffExtendedProduction_eq_rates (b : ℝ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    cutoffExtendedProduction b f z =
      extendedEntropyProduction (truncatedPostRate b f z) (truncatedPreRate b f z) := by
  by_cases hz : ‖z.1.2.1-z.1.2.2‖ < b
  · simp only [cutoffExtendedProduction,truncatedPostRate,truncatedPreRate,
      Set.indicator_apply,Set.mem_ofPred_eq,hz,↓reduceIte,postRate_formula,preRate]
    simpa only [mul_assoc] using (extendedEntropyProduction_scale
      (collisionKernel_nonneg z.1.2.1 z.1.2.2 z.2)
      (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))).symm
  · simp [cutoffExtendedProduction,truncatedPostRate,truncatedPreRate,hz,extendedEntropyProduction]

theorem rateDissipation_le_liminf_cutoff {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n p, 0 ≤ f n p)
    (hgm : Measurable g) (hgn : ∀ p, 0 ≤ g p)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hfi : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity))))
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    rateDissipation μ g ≤ liminf (fun n => cutoffExtendedDissipation μ (b n) (f n)) atTop := by
  have hr : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => ‖z.1.2.1-z.1.2.2‖) := by
    fun_prop
  have hs n : MeasurableSet {z : (X × (Velocity × Velocity)) × Sphere | ‖z.1.2.1-z.1.2.2‖ < b n} :=
    measurableSet_lt hr measurable_const
  have hpre := (weak_preRate h hfi).moving_cutoff
    (fun n => preRate_integrable (hfm n) (hfn n) (hfi n))
    (fun n z => preRate_nonneg (hfn n) z) hr hb
  have hpost := (weak_postRate hfm hgm h hfi).moving_cutoff
    (fun n => postRate_integrable (hfm n) (hfn n) (hfi n))
    (fun n z => preRate_nonneg (hfn n) (scatterTriple z)) hr hb
  have hi := Published.weak_production_liminf hpost hpre
    (fun n => (postRate_integrable (hfm n) (hfn n) (hfi n)).indicator (hs n))
    (fun n => (preRate_integrable (hfm n) (hfn n) (hfi n)).indicator (hs n))
    (ae_of_all _ (fun z => preRate_nonneg hgn (scatterTriple z)))
    (ae_of_all _ (fun z => preRate_nonneg hgn z))
  have hm := ENNReal.le_liminf_mul (u := fun _ : ℕ => (4:ℝ≥0∞)⁻¹)
    (v := fun n => ∫⁻ z, extendedEntropyProduction
      (truncatedPostRate (b n) (f n) z) (truncatedPreRate (b n) (f n) z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) (f := atTop)
  have hle := (mul_le_mul_right hi (4:ℝ≥0∞)⁻¹).trans (by
    simpa only [liminf_const,Pi.mul_def,truncatedPostRate,truncatedPreRate] using hm)
  simpa only [rateDissipation,cutoffExtendedDissipation,cutoffExtendedProduction_eq_rates _ (hfn _),truncatedPostRate,truncatedPreRate] using hle

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Removing attenuation from actual mass-normalized pre-collision rates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem collisionAttenuation_preRate_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (R : ℝ) (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun z =>
      (collisionWindow R).indicator (fun z => 1-rateMultiplier (N n) (f n) z) z *
        massNormalizedPreRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let S := angularPairBox (X := X) R
  let a (n : ℕ) : ((X × (Velocity × Velocity)) × Sphere) → ℝ :=
    (collisionWindow R).indicator (fun z => 1-rateMultiplier (N n) (f n) z)
  have ham n : Measurable (a n) :=
    (measurable_const.sub (rateMultiplier_measurable (N n) (hfm n))).indicator
      (collisionWindow_measurable R)
  have has : collisionWindow (X := X) R ⊆ S := by
    intro z hz
    have hv := collisionWindow_bounds hR hz
    exact ⟨⟨mem_univ _,by simpa only [Metric.mem_closedBall,dist_zero_right] using hv.1,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hv.2⟩,mem_univ _⟩
  have ha n z : |a n z| ≤ (1:ℝ≥0) := by
    by_cases hz : z ∈ collisionWindow R
    · change |(collisionWindow R).indicator _ z| ≤ 1
      rw [indicator_of_mem hz,abs_of_nonneg (sub_nonneg.mpr (rateMultiplier_bounds (hN n) (hf n) z).2)]
      linarith [(rateMultiplier_bounds (hN n) (hf n) z).1]
    · simp only [a,indicator_of_notMem hz,abs_zero,NNReal.coe_one,zero_le_one]
  have hzero : Tendsto (fun n => eLpNorm (a n) 1 (ν.restrict S)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (collisionAttenuation_window_L1 R hR hfm hf hN hNt B hB)
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure (a n) Measure.restrict_le_self)
  have ht := tendsto_L1_mul_uniformIntegrable
    (massNormalizedPreRate_local_uniformIntegrable R hfm hf hi hb)
    (fun n => massNormalizedPreRate_measurable (hfm n)) ham hzero 1 ha
  have he n : S.indicator (fun z => a n z*massNormalizedPreRate (f n) z) =
      (fun z => a n z*massNormalizedPreRate (f n) z) := by
    funext z
    by_cases hz : z ∈ S
    · exact indicator_of_mem hz _
    · have hw : z ∉ collisionWindow R := fun hw => hz (has hw)
      simp only [indicator_of_notMem hz,a,indicator_of_notMem hw,zero_mul]
  have hmS : MeasurableSet S := angularPairBox_measurable R
  have hn n : eLpNorm (fun z => a n z*massNormalizedPreRate (f n) z) 1 (ν.restrict S) =
      eLpNorm (fun z => a n z*massNormalizedPreRate (f n) z) 1 ν := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hmS,he n]
  change Tendsto (fun n => eLpNorm (fun z => a n z*massNormalizedPreRate (f n) z) 1
    (ν.restrict S)) atTop (𝓝 0) at ht
  simp only [hn] at ht
  exact ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Collision mass cancellation against bounded functions of the base variables -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem base_test_collision_zero {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    {ψ : X → ℝ} (hψm : Measurable ψ) {C : ℝ} (hψb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C) :
    (∫ p, ψ p.1*(gainDensity f p-lossDensity f p) ∂μ.prod volume) = 0 := by
  have hb : ∀ᵐ z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea,
      ‖ψ z.1.1‖ ≤ C :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hψb)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => ψ z.1.1) :=
    hψm.comp measurable_fst.fst
  have hpre := (preRate_integrable hfm hfn hp).bdd_mul hm.aestronglyMeasurable hb
  have hpost := (postRate_integrable hfm hfn hp).bdd_mul hm.aestronglyMeasurable hb
  have hbalance := full_test_collision_invariant f (fun p => ψ p.1) hpre hpost
    (collisionJump_mass ψ)
  have hb' : ∀ᵐ p : X × Velocity ∂μ.prod volume, ‖ψ p.1‖ ≤ C :=
    Measure.quasiMeasurePreserving_fst.ae hψb
  have hi := gainLoss_integrable hfm hfn hp
  have hgi := hi.1.bdd_mul (hψm.comp measurable_fst).aestronglyMeasurable hb'
  have hli := hi.2.bdd_mul (hψm.comp measurable_fst).aestronglyMeasurable hb'
  calc
    _ = ∫ p, ψ p.1*gainDensity f p-ψ p.1*lossDensity f p ∂μ.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => mul_sub _ _ _)
    _ = (∫ p, ψ p.1*gainDensity f p ∂μ.prod volume)-
        ∫ p, ψ p.1*lossDensity f p ∂μ.prod volume := integral_sub hgi hli
    _ = 0 := by rw [hbalance,sub_self]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
