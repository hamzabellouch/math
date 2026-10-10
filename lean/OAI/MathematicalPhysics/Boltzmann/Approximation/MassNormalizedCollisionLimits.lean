import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.RealL1ApproximationLimit
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedCollisionRates
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedGainCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicRenormalizedCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport

namespace OAI

section

/-! # Strong spatial masses remove gain normalization in measure -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem tendstoInMeasure_of_strong_massNormalized
    {f r : ℕ → X → ℝ} {g s : X → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hrm : ∀ n, Measurable (r n))
    (hr0 : ∀ n x, 0 ≤ r n x) (hs0 : ∀ x, 0 ≤ s x)
    (hr : Tendsto (fun n => eLpNorm (fun x => r n x-s x) 1 μ) atTop (𝓝 0))
    (hf : Tendsto (fun n => eLpNorm (fun x =>
      f n x/(1+r n x)-g x/(1+s x)) 1 μ) atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  have hri := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hr
  have hfi := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ℝ≥0∞) ≠ 0) hf
  have hrc := tendstoInMeasure_continuous_comp (fun n => (hrm n).aestronglyMeasurable) hri
    (P := fun x : ℝ => 1+x) (continuous_const.add continuous_id)
  have h := tendstoInMeasure_mul
    (fun n => ((hfm n).div (measurable_const.add (hrm n))).aestronglyMeasurable)
    (fun n => (measurable_const.add (hrm n)).aestronglyMeasurable) hfi hrc
  have he n x : f n x/(1+r n x)*(1+r n x) = f n x :=
    div_mul_cancel₀ _ (by linarith [hr0 n x])
  have heg x : g x/(1+s x)*(1+s x) = g x := div_mul_cancel₀ _ (by linarith [hs0 x])
  change TendstoInMeasure μ (fun n x => f n x/(1+r n x)*(1+r n x)) atTop
    (fun x => g x/(1+s x)*(1+s x)) at h
  simpa only [he,heg] using h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Compact temporal support of the complete local-mass integrand -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness

theorem MassTest.exists_time_cutoff (φ : MassTest) :
    ∃ T : ℝ, 0 < T ∧ (∀ x, φ.toFun T x = 0) ∧
      ∀ t, T < t → ∀ p : Phase, φ.transportDerivative t p = 0 := by
  obtain ⟨R,hR,hzero⟩ := φ.compact_time
  let L : ℝ × Velocity → ℝ := fun z => φ.toFun z.1 (torusProjection z.2)
  have hs : tsupport L ⊆ {z : ℝ × Velocity | z.1 ≤ R} := by
    apply closure_minimal
    · intro z hz
      by_contra hn
      exact hz (hzero z.1 (torusProjection z.2) ((lt_of_not_ge hn).trans_le (le_abs_self _)))
    · exact isClosed_le continuous_fst continuous_const
  refine ⟨R+1,by linarith,?_,?_⟩
  · intro x
    exact hzero (R+1) x (by rw [abs_of_pos (by linarith : 0 < R+1)]; linarith)
  · intro t ht p
    have hn : (t,torusRepresentative p.1) ∉ tsupport L := by
      intro hp
      have := hs hp
      change t ≤ R at this
      linarith
    have hd : fderiv ℝ L (t,torusRepresentative p.1) = 0 := fderiv_of_notMem_tsupport ℝ hn
    exact congrArg (fun A : (ℝ × Velocity) →L[ℝ] ℝ => A (1,p.2)) hd

end BoltzmannNonuniqueness

end

end

section

/-! # The actual finite collision rates divided by the same spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X]

def massRegularizedPreRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPreRate N f z/(1+fiberMass volume f z.1.1)

def massRegularizedPostRate (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  regularizedPostRate N f z/(1+fiberMass volume f z.1.1)

theorem massRegularizedPreRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (massRegularizedPreRate N f) := by
  exact (regularizedPreRate_measurable N hfm).div
    (measurable_const.add ((fiberMass_measurable hfm).comp measurable_fst.fst))

omit [MeasurableSpace X] in
theorem massRegularizedPostRate_eq (N : ℝ) (f : X × Velocity → ℝ) :
    massRegularizedPostRate N f = massRegularizedPreRate N f ∘ scatterTriple := rfl

theorem massRegularizedPostRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (massRegularizedPostRate N f) :=
  (massRegularizedPreRate_measurable N hfm).comp scatterTriple_measurable

omit [MeasurableSpace X] in
theorem massRegularizedPreRate_bounds {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ massRegularizedPreRate N f z ∧ massRegularizedPreRate N f z ≤ massNormalizedPreRate f z := by
  have hd : 0 ≤ 1+fiberMass volume f z.1.1 := by
    have h : 0 ≤ fiberMass volume f z.1.1 := integral_nonneg (fun v => hf (z.1.1,v))
    linarith
  exact ⟨div_nonneg (regularizedPreRate_bounds hN hf z).1 hd,
    div_le_div_of_nonneg_right (regularizedPreRate_le_physical hN hf z) hd⟩

variable {μ : Measure X} [SFinite μ]

omit [SFinite μ] in
theorem massRegularizedPreRate_integrable {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massRegularizedPreRate N f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply (massNormalizedPreRate_integrable hfm hi).mono'
    (massRegularizedPreRate_measurable N hfm).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (massRegularizedPreRate_bounds hN hf z).1]
  exact (massRegularizedPreRate_bounds hN hf z).2

theorem massRegularizedPostRate_integrable {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massRegularizedPostRate N f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable
    (massRegularizedPreRate_integrable hN hfm hf hi)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy controls the mass-normalized collision rate outside velocity windows -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem massPreRate_velocity_tail {R C : ℝ} (hR : 0 < R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm ((collisionWindow R)ᶜ.indicator (massNormalizedPreRate f)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
      ENNReal.ofReal (16*C/R)*eLpNorm (fun _ : Sphere => (1:ℝ)) 1 sphereArea := by
  let u : X × (Velocity × Velocity) → ℝ :=
    fun z => weightedNormalizedPair f z-pairVelocityCut (R/2) f z
  have hum : Measurable u :=
    (weightedNormalizedPair_measurable hfm).sub (pairVelocityCut_measurable (R/2) hfm)
  have hdom (z : (X × (Velocity × Velocity)) × Sphere) :
      ‖((collisionWindow R)ᶜ.indicator (massNormalizedPreRate f)) z‖ ≤ ‖u z.1‖ := by
    by_cases hz : z ∈ collisionWindow R
    · rw [indicator_of_notMem (notMem_compl_iff.mpr hz),norm_zero]
      exact norm_nonneg _
    · have hbox : ¬(‖z.1.2.1‖ ≤ R/2 ∧ ‖z.1.2.2‖ ≤ R/2) := by
        intro h
        have hv : ‖z.1.2.1‖^2 ≤ (R/2)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h.1
        have hw : ‖z.1.2.2‖^2 ≤ (R/2)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h.2
        apply hz
        change ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ R^2
        nlinarith [sq_nonneg R]
      rw [indicator_of_mem (mem_compl hz),massNormalizedPreRate_eq]
      change ‖normalizedKernel z*weightedNormalizedPair f z.1‖ ≤
        ‖weightedNormalizedPair f z.1-pairVelocityCut (R/2) f z.1‖
      simp only [pairVelocityCut,hbox,ite_false,sub_zero,norm_mul]
      exact (mul_le_mul_of_nonneg_right (normalizedKernel_bound z) (norm_nonneg _)).trans_eq (one_mul _)
  have hm := (massNormalizedPreRate_measurable hfm).indicator (collisionWindow_measurable R).compl
  have hn := eLpNorm_mono (p := 1) (μ := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
    hm.aestronglyMeasurable hdom
  have hp := eLpNorm_mul_prod_one (μ := μ.prod (volume.prod volume))
    (ν := sphereArea) hum (g := fun _ : Sphere => (1:ℝ)) measurable_const
  simp only [mul_one] at hp
  rw [Measure.volume_eq_prod] at hn
  rw [hp] at hn
  apply hn.trans
  have he := pairVelocityCut_L1_error (half_pos hR) hfm hf hi hb
  have hc : 8*C/(R/2) = 16*C/R := by ring
  rw [hc] at he
  exact mul_le_mul' he le_rfl

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong mass coefficients on bounded collision windows -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

def collisionMassClip (K : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  massClip K (fiberMass volume f z.1.1)

theorem collisionMassClip_measurable (K : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) : Measurable (collisionMassClip K f) :=
  (massClip_measurable K (fiberMass_measurable hf)).comp measurable_fst.fst

theorem collisionMassClip_strong_on_box {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0)) (K R : ℝ) :
    Tendsto (fun n => eLpNorm (fun z => collisionMassClip K (f n) z-collisionMassClip K g z)
      1 (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
        (angularPairBox R))) atTop (𝓝 0) := by
  let B : Set (Velocity × Velocity) := Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R
  let ν : Measure (Velocity × Velocity) := volume.restrict B
  have : IsFiniteMeasure ν := by
    constructor
    dsimp only [ν]
    rw [Measure.restrict_apply_univ,Measure.volume_eq_prod,Measure.prod_prod]
    exact ENNReal.mul_lt_top (isCompact_closedBall (0:Velocity) R).measure_lt_top
      (isCompact_closedBall (0:Velocity) R).measure_lt_top
  let a n x := massClip K (fiberMass volume (f n) x)-massClip K (fiberMass volume g x)
  have ham n : Measurable (a n) :=
    (massClip_measurable K (fiberMass_measurable (hfm n))).sub
      (massClip_measurable K (fiberMass_measurable hgm))
  have ha := strong_massClip (fun n => fiberMass_measurable (hfm n))
    (fiberMass_measurable hgm) K hm
  have ht := strongL1_comp_fst (ν := sphereArea)
    (fun n => (ham n).comp measurable_fst) (strongL1_comp_fst (ν := ν) ham ha)
  have he : (μ.prod ν).prod sphereArea =
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
        (angularPairBox R) := by
    dsimp only [ν,angularPairBox,velocityPairBox,B]
    rw [← Measure.restrict_prod_eq_prod_univ,← Measure.prod_restrict,Measure.restrict_univ]
  rw [he] at ht
  exact ht

omit [MeasurableSpace X] in
theorem collisionWindow_subset_angularPairBox {R : ℝ} (hR : 0 ≤ R) :
    collisionWindow (X := X) R ⊆ angularPairBox R := by
  intro z hz
  have h := collisionWindow_bounds hR hz
  exact ⟨⟨mem_univ _,by simpa only [Set.mem_prod,Metric.mem_closedBall,dist_zero_right] using h⟩,mem_univ _⟩

theorem collisionMassClip_strong_on_window {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0)) (K : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z => collisionMassClip K (f n) z-collisionMassClip K g z)
      1 (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
        (collisionWindow R))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (collisionMassClip_strong_on_box hfm hgm hm K R) (fun _ => zero_le)
  exact fun n => eLpNorm_mono_measure _
    (Measure.restrict_mono (collisionWindow_subset_angularPairBox hR) le_rfl)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual finite pre-rates converge to physical pre-rates on each collision window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionWindow_mono {R N : ℝ} (hR : 0 ≤ R) (hRN : R ≤ N) :
    collisionWindow (X := X) R ⊆ collisionWindow N := by
  intro z hz
  exact hz.trans ((sq_le_sq₀ hR (hR.trans hRN)).mpr hRN)

omit [MeasurableSpace X] in
theorem massRegularizedPreRate_on_window {R N : ℝ} (hR : 0 ≤ R) (hRN : R ≤ N)
    (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere)
    (hz : z ∈ collisionWindow R) :
    massRegularizedPreRate N f z = rateMultiplier N f z*massNormalizedPreRate f z := by
  unfold massRegularizedPreRate massNormalizedPreRate
  rw [regularizedPreRate_factor,windowKernel,indicator_of_mem (collisionWindow_mono hR hRN hz)]
  unfold preRate
  ring

omit [MeasurableSpace X] in
theorem massRegularizedPreRate_window_difference {R N : ℝ} (hR : 0 ≤ R) (hRN : R ≤ N)
    (f : X × Velocity → ℝ) :
    (collisionWindow R).indicator (fun z => massRegularizedPreRate N f z-massNormalizedPreRate f z) =
      fun z => -((collisionWindow R).indicator (fun z => 1-rateMultiplier N f z) z *
        massNormalizedPreRate f z) := by
  funext z
  by_cases hz : z ∈ collisionWindow R
  · rw [indicator_of_mem hz,indicator_of_mem hz,massRegularizedPreRate_on_window hR hRN f z hz]
    ring
  · simp only [indicator_of_notMem hz,zero_mul,neg_zero]

variable {μ : Measure X} [IsFiniteMeasure μ]

theorem massRegularizedPreRate_window_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (R : ℝ) (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm ((collisionWindow R).indicator
      (fun z => massRegularizedPreRate (N n) (f n) z-massNormalizedPreRate (f n) z)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  have ht := collisionAttenuation_preRate_L1 R hR hfm hf hi hb hN hNt B hB
  have he : (fun n => eLpNorm ((collisionWindow R).indicator
      (fun z => massRegularizedPreRate (N n) (f n) z-massNormalizedPreRate (f n) z)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) =ᶠ[atTop]
      (fun n => eLpNorm (fun z => (collisionWindow R).indicator
        (fun z => 1-rateMultiplier (N n) (f n) z) z*massNormalizedPreRate (f n) z) 1
        ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) := by
    filter_upwards [hNt.eventually (eventually_ge_atTop R)] with n hn
    rw [massRegularizedPreRate_window_difference hR hn]
    exact eLpNorm_neg _ _ _
  exact (tendsto_congr' he).mpr ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing every collision cutoff from the mass-normalized actual rates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] [IsFiniteMeasure μ] in
private theorem massRegularizedPreRate_difference_bound {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    |massRegularizedPreRate N f z-massNormalizedPreRate f z| ≤ |massNormalizedPreRate f z| := by
  have h := massRegularizedPreRate_bounds hN hf z
  rw [abs_of_nonpos (sub_nonpos.mpr h.2),abs_of_nonneg (h.1.trans h.2)]
  linarith

theorem massRegularizedPreRate_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun z => massRegularizedPreRate (N n) (f n) z-
      massNormalizedPreRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let d n := fun z => massRegularizedPreRate (N n) (f n) z-massNormalizedPreRate (f n) z
  let P := eLpNorm (fun _ : Sphere => (1:ℝ)) 1 sphereArea
  have hP : P ≠ ⊤ := (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ))).eLpNorm_ne_top
  have hdm n : Measurable (d n) := (massRegularizedPreRate_measurable (N n) (hfm n)).sub
    (massNormalizedPreRate_measurable (hfm n))
  have htail (R : ℝ) (hR : 0 < R) (n : ℕ) :
      eLpNorm ((collisionWindow R)ᶜ.indicator (d n)) 1 ν ≤ ENNReal.ofReal (16*C/R)*P := by
    apply le_trans (b := eLpNorm ((collisionWindow R)ᶜ.indicator (massNormalizedPreRate (f n))) 1 ν)
    · apply eLpNorm_mono ((hdm n).indicator (collisionWindow_measurable R).compl).aestronglyMeasurable
      intro z
      by_cases hz : z ∈ collisionWindow R
      · simp only [indicator_of_notMem (notMem_compl_iff.mpr hz),norm_zero,le_refl]
      · simp only [indicator_of_mem (mem_compl hz),Real.norm_eq_abs]
        exact massRegularizedPreRate_difference_bound (hN n) (hf n) z
    · exact massPreRate_velocity_tail hR (hfm n) (hf n) (hi n) (hb n)
  have hsplit (R : ℝ) (n : ℕ) : eLpNorm (d n) 1 ν ≤
      eLpNorm ((collisionWindow R).indicator (d n)) 1 ν+
        eLpNorm ((collisionWindow R)ᶜ.indicator (d n)) 1 ν := by
    have he : d n = (collisionWindow R).indicator (d n)+(collisionWindow R)ᶜ.indicator (d n) := by
      funext z
      by_cases hz : z ∈ collisionWindow R <;> simp [hz]
    conv_lhs => rw [he]
    exact eLpNorm_add_le (by norm_num)
  have hδ : Tendsto (fun j : ℕ => ENNReal.ofReal (16*C/((j:ℝ)+1))*P) atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds) :
      Tendsto (fun j : ℕ => 16*C/((j:ℝ)+1)) atTop (𝓝 0))
    simpa only [ENNReal.ofReal_zero,zero_mul] using ENNReal.Tendsto.mul_const ht (Or.inr hP)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨j,hj⟩ := (ENNReal.tendsto_nhds_zero.mp hδ (ε/2) hε2).exists
  have hR : 0 < (j:ℝ)+1 := by positivity
  have hw := massRegularizedPreRate_window_L1 ((j:ℝ)+1) hR.le hfm hf hi hb hN hNt B hB
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hw (ε/2) hε2] with n hn
  exact (hsplit ((j:ℝ)+1) n).trans ((add_le_add hn ((htail _ hR n).trans hj)).trans_eq ε.add_halves)

theorem massRegularizedPostRate_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun z => massRegularizedPostRate (N n) (f n) z-
      massNormalizedPostRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  have he n : eLpNorm (fun z => massRegularizedPostRate (N n) (f n) z-
      massNormalizedPostRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      eLpNorm (fun z => massRegularizedPreRate (N n) (f n) z-
        massNormalizedPreRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    exact eLpNorm_comp_measurePreserving
      ((massRegularizedPreRate_measurable (N n) (hfm n)).sub
        (massNormalizedPreRate_measurable (hfm n))).aestronglyMeasurable
      (scatterTriple_measurePreserving μ)
  simpa only [he] using massRegularizedPreRate_L1 hfm hf hi hb hN hNt B hB

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing velocity cutoffs from strong mass averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem strong_mass_of_velocity_averages {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hw : Published.WeakL1Converges (μ.prod ν) f g)
    {k : ℕ → Y → ℝ} (hkm : ∀ j, Measurable (k j)) (hkb : ∀ j y, |k j y| ≤ 1)
    {δ : ℕ → ℝ≥0∞} (hδ : Tendsto δ atTop (𝓝 0))
    (he : ∀ j n, eLpNorm (fun p => f n p-k j p.2*f n p) 1 (μ.prod ν) ≤ δ j)
    (hc : ∀ j, Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, k j v*f n (x,v) ∂ν)-(∫ v, k j v*g (x,v) ∂ν)) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (∫ v, f n (x,v) ∂ν)-(∫ v, g (x,v) ∂ν))
      1 μ) atTop (𝓝 0) := by
  let U := fun j n x => ∫ v, k j v*f n (x,v) ∂ν
  have hu j n : Integrable (fun p : X × Y => k j p.2*f n p) (μ.prod ν) :=
    (hfi n).bdd_mul ((hkm j).comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun p => hkb j p.2))
  have herr j n : eLpNorm ((fun x => ∫ v, f n (x,v) ∂ν)-U j n) 1 μ ≤ δ j := by
    have hae : ((fun x => ∫ v, f n (x,v) ∂ν)-U j n) =ᵐ[μ]
        (fun x => ∫ v, f n (x,v)-k j v*f n (x,v) ∂ν) := by
      filter_upwards [(hfi n).prod_right_ae,(hu j n).prod_right_ae] with x hfx hux
      exact (integral_sub hfx hux).symm
    rw [eLpNorm_congr_ae hae]
    exact (eLpNorm_integral_le ((hfm n).sub (((hkm j).comp measurable_snd).mul (hfm n)))).trans (he j n)
  obtain ⟨q,hqi,hq⟩ := l1_limit_of_uniform_approximation
    (fun n => (hfi n).integral_prod_left) hδ herr hc
  have hwm := hw.marginal hfi (measurable_const : Measurable (fun _ : X × Y => (1:ℝ))) 1
    (fun _ => by norm_num)
  simp only [one_mul] at hwm
  have hq' : Tendsto (fun n => eLpNorm (fun x => (∫ v, f n (x,v) ∂ν)-q x) 1 μ) atTop (𝓝 0) := hq
  have hqe := hwm.eq_of_strong (fun n => (hfi n).integral_prod_left) hqi hq'
  have hn n : eLpNorm (fun x => (∫ v, f n (x,v) ∂ν)-q x) 1 μ =
      eLpNorm (fun x => (∫ v, f n (x,v) ∂ν)-(∫ v, g (x,v) ∂ν)) 1 μ := by
    apply eLpNorm_congr_ae
    filter_upwards [hqe] with x hx
    rw [hx]
  simpa only [hn] using hq'

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The actual finite collision rates have the same mass-normalized weak limit -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weak_massRegularizedPreRate
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B)
    (hw : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massNormalizedPreRate (f n)) (massNormalizedPreRate g)) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPreRate (N n) (f n)) (massNormalizedPreRate g) := by
  have hwi n : Integrable (weightedNormalizedPair (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    rw [Measure.volume_eq_prod]
    exact weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  exact hw.of_eLpNorm_sub (fun n => massNormalizedPreRate_integrable (hfm n) (hwi n))
    (fun n => massRegularizedPreRate_integrable (hN n) (hfm n) (hf n) (hwi n))
    (massRegularizedPreRate_L1 hfm hf hi hb hN hNt B hB)

theorem weak_massRegularizedPostRate
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B)
    (hw : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massNormalizedPostRate (f n)) (massNormalizedPostRate g)) :
    Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPostRate (N n) (f n)) (massNormalizedPostRate g) := by
  have hwi n : Integrable (weightedNormalizedPair (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    rw [Measure.volume_eq_prod]
    exact weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  exact hw.of_eLpNorm_sub (fun n => massNormalizedPostRate_integrable (hfm n) (hwi n))
    (fun n => massRegularizedPostRate_integrable (hN n) (hfm n) (hf n) (hwi n))
    (massRegularizedPostRate_L1 hfm hf hi hb hN hNt B hB)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing finite collision attenuation from the mass-normalized gain -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem massRegularized_gain {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ) (p : X × Velocity) :
    collisionMarginal (massRegularizedPostRate N f) p = gain N f p/(1+fiberMass volume f p.1) := by
  change (∫ q : Velocity × Sphere,
    regularizedPostRate N f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  rw [integral_div,← gain_eq_full_integral hN]

theorem massNormalized_gain (f : X × Velocity → ℝ) (p : X × Velocity) :
    collisionMarginal (massNormalizedPostRate f) p = gainDensity f p/(1+fiberMass volume f p.1) := by
  change (∫ q : Velocity × Sphere,
    postRate f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  rw [integral_div]
  rfl

theorem massRegularizedGain_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun p =>
      gain (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
      gainDensity (f n) p/(1+fiberMass volume (f n) p.1)) 1 (μ.prod volume)) atTop (𝓝 0) := by
  have herr := massRegularizedPostRate_L1 hfm hf hi hb hN hNt B hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr (fun _ => zero_le)
  intro n
  have hwi : Integrable (weightedNormalizedPair (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  have hm := massRegularizedPostRate_measurable (N n) (hfm n)
  have km := massNormalizedPostRate_measurable (hfm n)
  have hri := massRegularizedPostRate_integrable (hN n) (hfm n) (hf n) hwi
  have hpi := massNormalizedPostRate_integrable (hfm n) hwi
  have h := collisionMarginal_difference_le hm km hri hpi
  have he : collisionMarginal (massRegularizedPostRate (N n) (f n))-
      collisionMarginal (massNormalizedPostRate (f n)) =
      (fun p => gain (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
        gainDensity (f n) p/(1+fiberMass volume (f n) p.1)) := by
    funext p
    exact congrArg₂ (fun a b : ℝ => a-b) (massRegularized_gain (hN n).le (f n) p)
      (massNormalized_gain (f n) p)
  rw [he] at h
  exact h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing finite collision attenuation from the mass-normalized loss -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem massRegularized_loss {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ) (p : X × Velocity) :
    collisionMarginal (massRegularizedPreRate N f) p = loss N f p/(1+fiberMass volume f p.1) := by
  change (∫ q : Velocity × Sphere,
    regularizedPreRate N f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  rw [integral_div,← loss_eq_full_integral hN]

theorem massNormalized_loss (f : X × Velocity → ℝ) (p : X × Velocity) :
    collisionMarginal (massNormalizedPreRate f) p = lossDensity f p/(1+fiberMass volume f p.1) := by
  change (∫ q : Velocity × Sphere,
    preRate f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  rw [integral_div]
  rfl

theorem massRegularizedLoss_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun p =>
      loss (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
      lossDensity (f n) p/(1+fiberMass volume (f n) p.1)) 1 (μ.prod volume)) atTop (𝓝 0) := by
  have herr := massRegularizedPreRate_L1 hfm hf hi hb hN hNt B hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr (fun _ => zero_le)
  intro n
  have hwi : Integrable (weightedNormalizedPair (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  have hm := massRegularizedPreRate_measurable (N n) (hfm n)
  have km := massNormalizedPreRate_measurable (hfm n)
  have hri := massRegularizedPreRate_integrable (hN n) (hfm n) (hf n) hwi
  have hpi := massNormalizedPreRate_integrable (hfm n) hwi
  have h := collisionMarginal_difference_le hm km hri hpi
  have he : collisionMarginal (massRegularizedPreRate (N n) (f n))-
      collisionMarginal (massNormalizedPreRate (f n)) =
      (fun p => loss (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
        lossDensity (f n) p/(1+fiberMass volume (f n) p.1)) := by
    funext p
    exact congrArg₂ (fun a b : ℝ => a-b) (massRegularized_loss (hN n).le (f n) p)
      (massNormalized_loss (f n) p)
  rw [he] at h
  exact h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
