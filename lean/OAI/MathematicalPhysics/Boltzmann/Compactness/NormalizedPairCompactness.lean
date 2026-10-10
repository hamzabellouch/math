import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedL1Tests
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedPairRate
import OAI.MathematicalPhysics.Boltzmann.Branching.MarginalUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.MixedPhysicalMeasures
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedPairUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.L1VelocityTranslationApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedCollisionRates
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedKernelAction
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairBoundedTruncation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchIdentity
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Factorization of mass-normalized pair moments -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

omit [MeasurableSpace X] in
theorem normalizedPair_moment_identity {f : X × Y → ℝ} {k l : X × Y → ℝ} (x : X) :
    (∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*normalizedPair ν f (x,y) ∂ν.prod ν) =
      (∫ v, k (x,v)*f (x,v) ∂ν)*(∫ w, l (x,w)*f (x,w) ∂ν)/(1+fiberMass ν f x) := by
  have he : (fun y : Y × Y => (k (x,y.1)*l (x,y.2))*normalizedPair ν f (x,y)) =
      (fun y : Y × Y => ((k (x,y.1)*f (x,y.1))*(l (x,y.2)*f (x,y.2)))/(1+fiberMass ν f x)) := by
    funext y
    dsimp only [normalizedPair,normalizedTensor]
    ring
  rw [he,integral_div,integral_prod_mul (fun v => k (x,v)*f (x,v)) (fun w => l (x,w)*f (x,w))]

theorem normalizedPair_moment_limit {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    {W : X × (Y × Y) → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hW : Published.WeakL1Converges (μ.prod (ν.prod ν)) (fun n => normalizedPair ν (f n)) W)
    (hrui : UniformIntegrable (fun n => fiberMass ν (f n)) 1 μ)
    (hr : Tendsto (fun n => eLpNorm (fun x => fiberMass ν (f n) x-fiberMass ν g x) 1 μ) atTop (𝓝 0))
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    {C D : ℝ} (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D)
    (hA : Tendsto (fun n => eLpNorm (fun x => (∫ v, k (x,v)*f n (x,v) ∂ν)-
      (∫ v, k (x,v)*g (x,v) ∂ν)) 1 μ) atTop (𝓝 0))
    (hB : Tendsto (fun n => eLpNorm (fun x => (∫ v, l (x,v)*f n (x,v) ∂ν)-
      (∫ v, l (x,v)*g (x,v) ∂ν)) 1 μ) atTop (𝓝 0)) :
    (fun x => ∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*W (x,y) ∂ν.prod ν) =ᵐ[μ]
      (fun x => (∫ v, k (x,v)*g (x,v) ∂ν)*(∫ w, l (x,w)*g (x,w) ∂ν)/(1+|fiberMass ν g x|)) := by
  have hki n := ((hfi n).bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)).integral_prod_left
  have hli n := ((hfi n).bdd_mul hl.aestronglyMeasurable (ae_of_all _ hD)).integral_prod_left
  have hbound (a : X × Y → ℝ) {E : ℝ}
      (hE : ∀ z, |a z| ≤ E) (n : ℕ) :
      ∀ᵐ x ∂μ, |∫ v, a (x,v)*f n (x,v) ∂ν| ≤ E*fiberMass ν (f n) x := by
    filter_upwards [(hfi n).prod_right_ae] with x hx
    have hbnd v : ‖a (x,v)*f n (x,v)‖ ≤ E*f n (x,v) := by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (hf n _)]
      exact mul_le_mul_of_nonneg_right (hE _) (hf n _)
    have h := norm_integral_le_of_norm_le (hx.const_mul E) (ae_of_all _ hbnd)
    simpa only [Real.norm_eq_abs,integral_const_mul,fiberMass] using h
  have hprod := tendsto_L1_normalized_product
    (fun n => (hki n).aestronglyMeasurable) (fun n => (hli n).aestronglyMeasurable)
    (fun n => fiberMass_measurable (hfm n)) hA hB hr hrui
    (fun n => ae_of_all _ (fun x => integral_nonneg (fun v => hf n (x,v)))) hC0 hD0
    (hbound k hC) (hbound l hD)
  let kl : X × (Y × Y) → ℝ := fun z => k (z.1,z.2.1)*l (z.1,z.2.2)
  have hkl : Measurable kl := by dsimp [kl]; fun_prop
  have hklB z : |kl z| ≤ C*D := by
    change |k (z.1,z.2.1)*l (z.1,z.2.2)| ≤ C*D
    rw [abs_mul]
    exact mul_le_mul (hC _) (hD _) (abs_nonneg _) hC0
  have hw := hW.marginal (fun n => normalizedPair_integrable (hfm n) (hf n) (hfi n)) hkl (C*D) hklB
  have he (n : ℕ) (x : X) : (∫ y, kl (x,y)*normalizedPair ν (f n) (x,y) ∂ν.prod ν) =
      (∫ v, k (x,v)*f n (x,v) ∂ν)*(∫ w, l (x,w)*f n (x,w) ∂ν)/(1+|fiberMass ν (f n) x|) := by
    have hm0 : 0 ≤ fiberMass ν (f n) x :=
      integral_nonneg (μ := ν) (f := fun v => f n (x,v)) (fun v => hf n (x,v))
    rw [abs_of_nonneg hm0]
    exact normalizedPair_moment_identity x
  have hsource n : Integrable (fun x => ∫ y, kl (x,y)*normalizedPair ν (f n) (x,y) ∂ν.prod ν) μ :=
    ((normalizedPair_integrable (hfm n) (hf n) (hfi n)).bdd_mul hkl.aestronglyMeasurable
      (ae_of_all _ hklB)).integral_prod_left
  have hs : Tendsto (fun n => eLpNorm (fun x =>
      (∫ y, kl (x,y)*normalizedPair ν (f n) (x,y) ∂ν.prod ν)-
      (∫ v, k (x,v)*g (x,v) ∂ν)*(∫ w, l (x,w)*g (x,w) ∂ν)/(1+|fiberMass ν g x|)) 1 μ)
      atTop (𝓝 0) := by simpa only [he] using hprod
  have ht := Published.integrable_of_strong_limit (Filter.Eventually.of_forall hsource) hs
  exact (hw.eq_of_strong hsource ht hs).symm

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Countably many moments determine the mass-normalized pair -/
noncomputable section
open MeasureTheory Filter
namespace BoltzmannNonuniqueness.Compactness

theorem normalized_pair_eq_of_moments {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {W : Velocity × Velocity → ℝ} {g : Velocity → ℝ}
    (hWm : Measurable W) (hgm : Measurable g) (hWi : Integrable W) (hgi : Integrable g)
    (hg : ∀ v, 0 ≤ g v)
    (hmom : ∀ i j, (∫ z, (ψ i z.1*ψ j z.2)*W z) =
      (∫ v, ψ i v*g v)*(∫ w, ψ j w*g w)/(1+|∫ v, g v|)) :
    W =ᵐ[volume] (fun z => g z.1*g z.2/(1+∫ v, g v)) := by
  let r : ℝ := ∫ v, g v
  have hr : 0 ≤ r := integral_nonneg hg
  have hd : 1+r ≠ 0 := ne_of_gt (by linarith)
  let U : Velocity × Velocity → ℝ := fun z => (1+r)*W z
  have hU : U =ᵐ[volume] (fun z => g z.1*g z.2) := by
    apply pair_eq_product_of_moments (W := U) (g := g) hψ hc hdet
      (measurable_const.mul hWm) hgm (hWi.const_mul (1+r)) hgi
    intro i j
    have he : (fun z : Velocity × Velocity => (ψ i z.1*ψ j z.2)*U z) =
        (fun z => (1+r)*((ψ i z.1*ψ j z.2)*W z)) := by funext z; dsimp only [U]; ring
    rw [he,integral_const_mul,hmom i j]
    change (1+r)*((∫ v, ψ i v*g v)*(∫ w, ψ j w*g w)/(1+|r|)) = _
    rw [abs_of_nonneg hr]
    exact mul_div_cancel₀ _ hd
  filter_upwards [hU] with z hz
  change W z = g z.1*g z.2/(1+r)
  apply (eq_div_iff hd).mpr
  change (1+r)*W z = g z.1*g z.2 at hz
  nlinarith [hz]

theorem normalizedPair_eq_of_fiber_moments
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    {W : X × (Velocity × Velocity) → ℝ} {g : X × Velocity → ℝ}
    (hWm : Measurable W) (hgm : Measurable g)
    (hWi : Integrable W (μ.prod volume)) (hgi : Integrable g (μ.prod volume))
    (hg : ∀ z, 0 ≤ g z)
    (hmom : ∀ i j, ∀ᵐ x ∂μ, (∫ y : Velocity × Velocity, (ψ i y.1*ψ j y.2)*W (x,y)) =
      (∫ v, ψ i v*g (x,v))*(∫ w, ψ j w*g (x,w))/(1+|fiberMass volume g x|)) :
    W =ᵐ[μ.prod volume] normalizedPair volume g := by
  have hm : ∀ᵐ x ∂μ, ∀ i j, (∫ y : Velocity × Velocity, (ψ i y.1*ψ j y.2)*W (x,y)) =
      (∫ v, ψ i v*g (x,v))*(∫ w, ψ j w*g (x,w))/(1+|fiberMass volume g x|) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hmom i))
  have hfib : ∀ᵐ x ∂μ, (fun y => W (x,y)) =ᵐ[volume]
      (fun y => normalizedPair volume g (x,y)) := by
    filter_upwards [hm,hWi.prod_right_ae,hgi.prod_right_ae] with x hx hWx hgx
    exact normalized_pair_eq_of_moments hψ hc hdet
      (hWm.comp measurable_prodMk_left) (hgm.comp measurable_prodMk_left)
      hWx hgx (fun v => hg (x,v)) hx
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hWm
    (normalizedTensor_measurable (fiberMass_measurable hgm) hgm hgm))).mpr hfib

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Actual entropy-controlled normalized pairs admit bounded compact moment approximations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] in
theorem momentPair_normalizedPair (f : X × Velocity → ℝ) :
    momentPair (normalizedPair volume f) = weightedNormalizedPair f := rfl

omit [MeasurableSpace X] in
theorem momentVelocityCut_normalizedPair (R : ℝ) (f : X × Velocity → ℝ) :
    momentVelocityCut R (normalizedPair volume f) = pairVelocityCut R f := by
  funext z
  by_cases hv : ‖z.2.1‖ ≤ R <;> by_cases hw : ‖z.2.2‖ ≤ R <;>
    simp [momentVelocityCut,incomingBall,Metric.mem_closedBall,dist_zero_right,
      hv,hw,pairVelocityCut,momentPair,weightedNormalizedPair,pairVelocityWeight]

theorem normalizedPair_bounded_moment_approximation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (R : ℝ) (_hR : 0 < R) (B : ℝ≥0) (u : ℕ → X × (Velocity × Velocity) → ℝ),
      (∀ n, Measurable (u n)) ∧ (∀ n z, |u n z| ≤ B) ∧
      (∀ n z, z.2 ∉ incomingBall R → u n z = 0) ∧
      (∀ n, eLpNorm (momentPair (fun z => normalizedPair volume (f n) z-u n z)) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ε) := by
  have hhalf : 0 < ε/2 := ENNReal.half_pos hε.ne'
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (8*C) hhalf
  let R : ℝ := (j:ℝ)+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hui := weightedNormalizedPair_uniformIntegrable hfm hf hi hb
  rw [← Measure.volume_eq_prod] at hui
  obtain ⟨B,hB⟩ := hui.spec (by norm_num) (by norm_num) hhalf
  let u := fun n => boundedPairCut R B (normalizedPair volume (f n))
  have hgm n : Measurable (normalizedPair volume (f n)) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n)) (hfm n) (hfm n)
  refine ⟨R,hR,B,u,fun n => boundedPairCut_measurable R B (hgm n),
    fun n z => boundedPairCut_bound R B _ z,
    fun n z hz => boundedPairCut_support R B _ z hz,fun n => ?_⟩
  have hvel : eLpNorm (fun z => momentPair (normalizedPair volume (f n)) z-
      momentVelocityCut R (normalizedPair volume (f n)) z) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ε/2 := by
    rw [momentPair_normalizedPair,momentVelocityCut_normalizedPair]
    apply (pairVelocityCut_L1_error hR (hfm n) (hf n) (hi n) (hb n)).trans
    exact hj
  have hamp : eLpNorm (({z | B ≤ ‖momentPair (normalizedPair volume (f n)) z‖₊}).indicator
      (momentPair (normalizedPair volume (f n)))) 1
      (μ.prod (volume : Measure (Velocity × Velocity))) ≤ ε/2 := by
    simpa only [momentPair_normalizedPair] using hB n
  exact ((boundedPairCut_moment_error R B (hgm n)).trans
    (add_le_add hvel hamp)).trans_eq ε.add_halves

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Strong convergence of the actual normalized pair against product tests -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

theorem normalizedPair_product_strong {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z) (hg : ∀ z, 0 ≤ g z)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hrui : UniformIntegrable (fun n => fiberMass ν (f n)) 1 μ)
    (hr : Tendsto (fun n => eLpNorm (fun x => fiberMass ν (f n) x-fiberMass ν g x) 1 μ) atTop (𝓝 0))
    {k l : X × Y → ℝ} (hk : Measurable k) (hl : Measurable l)
    {C D : ℝ} (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hC : ∀ z, |k z| ≤ C) (hD : ∀ z, |l z| ≤ D)
    (hA : Tendsto (fun n => eLpNorm (fun x => (∫ v, k (x,v)*f n (x,v) ∂ν)-
      (∫ v, k (x,v)*g (x,v) ∂ν)) 1 μ) atTop (𝓝 0))
    (hB : Tendsto (fun n => eLpNorm (fun x => (∫ v, l (x,v)*f n (x,v) ∂ν)-
      (∫ v, l (x,v)*g (x,v) ∂ν)) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      (∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*normalizedPair ν (f n) (x,y) ∂ν.prod ν)-
      (∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*normalizedPair ν g (x,y) ∂ν.prod ν))
      1 μ) atTop (𝓝 0) := by
  have hki n := ((hfi n).bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)).integral_prod_left
  have hli n := ((hfi n).bdd_mul hl.aestronglyMeasurable (ae_of_all _ hD)).integral_prod_left
  have hbound (a : X × Y → ℝ) {E : ℝ}
      (hE : ∀ z, |a z| ≤ E) (n : ℕ) :
      ∀ᵐ x ∂μ, |∫ v, a (x,v)*f n (x,v) ∂ν| ≤ E*fiberMass ν (f n) x := by
    filter_upwards [(hfi n).prod_right_ae] with x hx
    have hbnd v : ‖a (x,v)*f n (x,v)‖ ≤ E*f n (x,v) := by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (hf n _)]
      exact mul_le_mul_of_nonneg_right (hE _) (hf n _)
    have h := norm_integral_le_of_norm_le (hx.const_mul E) (ae_of_all _ hbnd)
    simpa only [Real.norm_eq_abs,integral_const_mul,fiberMass] using h
  have hprod := tendsto_L1_normalized_product
    (fun n => (hki n).aestronglyMeasurable) (fun n => (hli n).aestronglyMeasurable)
    (fun n => fiberMass_measurable (hfm n)) hA hB hr hrui
    (fun n => ae_of_all _ (fun x => integral_nonneg (fun v => hf n (x,v)))) hC0 hD0
    (hbound k hC) (hbound l hD)
  have he (u : X × Y → ℝ) (hu : ∀ z, 0 ≤ u z) (x : X) :
      (∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*normalizedPair ν u (x,y) ∂ν.prod ν) =
      (∫ v, k (x,v)*u (x,v) ∂ν)*(∫ w, l (x,w)*u (x,w) ∂ν)/(1+|fiberMass ν u x|) := by
    have hm : 0 ≤ fiberMass ν u x :=
      integral_nonneg (μ := ν) (f := fun v => u (x,v)) (fun v => hu (x,v))
    rw [abs_of_nonneg hm]
    exact normalizedPair_moment_identity x
  simpa only [he _ (hf _),he _ hg] using hprod

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Identification of a weak pair limit from strong scalar velocity averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem normalizedPair_weak_limit_eq
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    {W : X × (Velocity × Velocity) → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hfi : ∀ n, Integrable (f n) (μ.prod volume))
    (hgm : Measurable g) (hg : ∀ z, 0 ≤ g z) (hgi : Integrable g (μ.prod volume))
    (hW : Published.WeakL1Converges (μ.prod (volume.prod volume))
      (fun n => normalizedPair volume (f n)) W)
    (hrui : UniformIntegrable (fun n => fiberMass volume (f n)) 1 μ)
    (hr : Tendsto (fun n => eLpNorm (fun x =>
      fiberMass volume (f n) x-fiberMass volume g x) 1 μ) atTop (𝓝 0))
    {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    (hstrong : ∀ i, Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, ψ i v*f n (x,v))-(∫ v, ψ i v*g (x,v))) 1 μ) atTop (𝓝 0)) :
    W =ᵐ[μ.prod (volume.prod volume)] normalizedPair volume g := by
  have hWi : Integrable W (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using hW.2.1
  have h := normalizedPair_eq_of_fiber_moments hψ hc hdet hW.1 hgm hWi hgi hg
  apply h
  intro i j
  obtain ⟨C,hC⟩ := (hψ i).continuous.bounded_above_of_compact_support (hc i)
  obtain ⟨D,hD⟩ := (hψ j).continuous.bounded_above_of_compact_support (hc j)
  have hC0 : 0 ≤ C := (abs_nonneg (ψ i 0)).trans (hC 0)
  have hD0 : 0 ≤ D := (abs_nonneg (ψ j 0)).trans (hD 0)
  have hi := normalizedPair_moment_limit hfm hf hfi hW hrui hr
    ((hψ i).continuous.measurable.comp measurable_snd)
    ((hψ j).continuous.measurable.comp measurable_snd)
    hC0 hD0 (fun z => hC z.2) (fun z => hD z.2) (hstrong i) (hstrong j)
  filter_upwards [hi] with x hx
  simpa only [Measure.volume_eq_prod,Function.comp_apply] using hx

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Identifying a normalized pair on a nonzero averaging patch -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem normalizedPair_eq_on_patch
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    {W : X × (Velocity × Velocity) → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hfi : ∀ n, Integrable (f n) (μ.prod volume))
    (hgm : Measurable g) (hg : ∀ z, 0 ≤ g z) (hgi : Integrable g (μ.prod volume))
    (hW : Published.WeakL1Converges (μ.prod (volume.prod volume))
      (fun n => normalizedPair volume (f n)) W)
    (hrui : UniformIntegrable (fun n => fiberMass volume (f n)) 1 μ)
    {χ : X → ℝ} {s : Set X} (hs : MeasurableSet s) {δ : ℝ} (hδ : 0 < δ)
    (hχ : ∀ x ∈ s, δ ≤ |χ x|)
    (hr : Tendsto (fun n => eLpNorm (fun x =>
      χ x*fiberMass volume (f n) x-χ x*fiberMass volume g x) 1 μ) atTop (𝓝 0))
    {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    (hstrong : ∀ i, Tendsto (fun n => eLpNorm (fun x =>
      χ x*(∫ v, ψ i v*f n (x,v))-χ x*(∫ v, ψ i v*g (x,v))) 1 μ) atTop (𝓝 0)) :
    W =ᵐ[(μ.restrict s).prod (volume.prod volume)] normalizedPair volume g := by
  apply normalizedPair_weak_limit_eq hfm hf
    (fun n => (hfi n).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
    hgm hg (hgi.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
    (hW.restrict_base hs) (uniformIntegrable_restrict hrui s)
  · exact strong_on_patch_of_weighted (fun n => fiberMass_measurable (ν := volume) (hfm n))
      (fiberMass_measurable (ν := volume) hgm) hs hδ hχ hr
  · exact hψ
  · exact hc
  · exact hdet
  · intro i
    apply strong_on_patch_of_weighted
      (fun n => (((hψ i).continuous.measurable.comp measurable_snd).mul (hfm n)).stronglyMeasurable.integral_prod_right'.measurable)
      ((((hψ i).continuous.measurable.comp measurable_snd).mul hgm).stronglyMeasurable.integral_prod_right'.measurable)
      hs hδ hχ (hstrong i)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Local uniform integrability of the mass-normalized physical collision rates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

def velocityPairBox (R : ℝ) : Set (X × (Velocity × Velocity)) :=
  univ ×ˢ (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R)

def angularPairBox (R : ℝ) : Set ((X × (Velocity × Velocity)) × Sphere) :=
  velocityPairBox R ×ˢ univ

theorem velocityPairBox_measurable (R : ℝ) : MeasurableSet (velocityPairBox (X := X) R) :=
  MeasurableSet.univ.prod
    (Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet)

theorem angularPairBox_measurable (R : ℝ) : MeasurableSet (angularPairBox (X := X) R) :=
  (velocityPairBox_measurable R).prod MeasurableSet.univ

variable {μ : Measure X} [IsFiniteMeasure μ]

theorem velocityPairBox_finite (R : ℝ) :
    (μ.prod (volume : Measure (Velocity × Velocity))) (velocityPairBox R) < ⊤ := by
  rw [Measure.volume_eq_prod]
  dsimp only [velocityPairBox]
  rw [Measure.prod_prod,Measure.prod_prod]
  have hb : volume (Metric.closedBall (0:Velocity) R) ≠ ⊤ :=
    (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (measure_ne_top μ univ) (ENNReal.mul_ne_top hb hb))

theorem weightedPair_angular_local_uniformIntegrable (R : ℝ)
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n z => weightedNormalizedPair (f n) z.1) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (angularPairBox R)) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).restrict (velocityPairBox R)
  have : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    rw [Measure.restrict_apply_univ]
    exact velocityPairBox_finite R⟩
  have hui := weightedNormalizedPair_uniformIntegrable hfm hf hi hb
  rw [← Measure.volume_eq_prod] at hui
  have hr : UniformIntegrable (fun n => weightedNormalizedPair (f n)) 1 ν :=
    uniformIntegrable_restrict hui (velocityPairBox R)
  have hp := uniformIntegrable_tensor (μ := ν) (ν := sphereArea) (fun n => weightedNormalizedPair_measurable (hfm n)) hr
    (g := fun _ : Sphere => (1:ℝ)) measurable_const (integrable_const 1)
  dsimp only [ν] at hp
  rw [Measure.restrict_prod_eq_prod_univ] at hp
  simpa only [Measure.restrict_univ,mul_one,angularPairBox] using hp

theorem massNormalizedPreRate_local_uniformIntegrable (R : ℝ)
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => massNormalizedPreRate (f n)) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (angularPairBox R)) := by
  have h := uniformIntegrable_of_bounded_multiplier
    (weightedPair_angular_local_uniformIntegrable R hfm hf hi hb)
    normalizedKernel_measurable 1 normalizedKernel_bound
  simpa only [massNormalizedPreRate_eq_fun] using h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Uniform velocity translations of the actual entropy-controlled normalized gain -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem normalizedGain_translation
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    {a : ℕ → Velocity} (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n => ∫ p,
      |pairGain (normalizedPair volume (f n)) (p.1,p.2+a n)-
        pairGain (normalizedPair volume (f n)) p| ∂μ.prod volume) atTop (𝓝 0) := by
  let g := fun n => normalizedPair volume (f n)
  have hgm n : Measurable (g n) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n)) (hfm n) (hfm n)
  have hmi n : Integrable (momentPair (g n)) (μ.prod (volume : Measure (Velocity × Velocity))) := by
    have hh := weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
    rw [← Measure.volume_eq_prod] at hh
    exact hh
  have hri n := pairPreRate_integrable_of_moment (hgm n) (hmi n)
  apply velocityTranslation_of_uniform_L1_approximation (fun n => pairGain_integrable (hri n))
  intro ε hε
  let D := sphereArea.real univ
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  let δ := ε/(D+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨R,hR,B,u,hum,huB,hus,herr⟩ := normalizedPair_bounded_moment_approximation
    hfm hf hi hb (ENNReal.ofReal_pos.mpr hδ)
  have hui n := bounded_pairPreRate_integrable (μ := μ) R (hum n) (huB n) (hus n)
  refine ⟨fun n => pairGain (u n),fun n => pairGain_integrable (hui n),?_,
    bounded_pairGain_translation_no_rate_assumption R ha hum huB hus⟩
  intro n
  have he : (fun z => pairPreRate (g n) z-pairPreRate (u n) z) =
      pairPreRate (fun z => g n z-u n z) := by
    funext z
    exact (mul_sub _ _ _).symm
  have hn : eLpNorm (fun p => pairGain (g n) p-pairGain (u n) p) 1 (μ.prod volume) ≤
      sphereArea univ*eLpNorm (momentPair (fun z => g n z-u n z)) 1
        (μ.prod (volume : Measure (Velocity × Velocity))) := by
    apply (pairGain_difference_eLpNorm_le (hgm n) (hum n) (hri n) (hui n)).trans
    rw [he]
    exact pairPreRate_moment_norm_le ((hgm n).sub (hum n))
  have hDreal : ENNReal.ofReal D = sphereArea univ :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have heps : D*δ ≤ ε := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < D+1)).mpr
    nlinarith
  have heL : eLpNorm (fun p => pairGain (g n) p-pairGain (u n) p) 1 (μ.prod volume) ≤
      ENNReal.ofReal ε := by
    apply hn.trans
    calc
      _ ≤ sphereArea univ*ENNReal.ofReal δ := mul_le_mul' le_rfl (herr n)
      _ = ENNReal.ofReal (D*δ) := by rw [← hDreal,ENNReal.ofReal_mul hD]
      _ ≤ _ := ENNReal.ofReal_le_ofReal heps
  exact Published.integral_abs_le_of_eLpNorm_le
    ((pairGain_integrable (hri n)).sub (pairGain_integrable (hui n))) hε.le heL

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # Normalized collision pairs determine the weighted squares of velocity averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

omit [MeasurableSpace X] in
private theorem square_identity (ψ : Y → ℝ) (f : X × Y → ℝ) (x : X) :
    (∫ y : Y × Y, (ψ y.1*ψ y.2)*normalizedPair ν f (x,y) ∂ν.prod ν) =
      (∫ v, ψ v*f (x,v) ∂ν)^2/(1+fiberMass ν f x) := by
  simpa only [pow_two] using
    normalizedPair_moment_identity (ν := ν) (f := f)
      (k := fun p => ψ p.2) (l := fun p => ψ p.2) x

theorem normalized_average_square_integrable {f : X × Y → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfi : Integrable f (μ.prod ν))
    {ψ : Y → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) :
    Integrable (fun x => (∫ v, ψ v*f (x,v) ∂ν)^2/(1+fiberMass ν f x)) μ := by
  have hkm : Measurable (fun z : X × (Y × Y) => ψ z.2.1*ψ z.2.2) :=
    (hψ.comp measurable_snd.fst).mul (hψ.comp measurable_snd.snd)
  have hkb (z : X × (Y × Y)) : |ψ z.2.1*ψ z.2.2| ≤ |C| * |C| := by
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self C)) ((hC _).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have hi := ((normalizedPair_integrable hfm hf hfi).bdd_mul
    hkm.aestronglyMeasurable (ae_of_all _ hkb)).integral_prod_left
  simpa only [square_identity ψ] using hi

theorem weak_normalized_average_squares
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hp : Published.WeakL1Converges (μ.prod (ν.prod ν))
      (fun n => normalizedPair ν (f n)) (normalizedPair ν g))
    {ψ : Y → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) :
    Published.WeakL1Converges μ
      (fun n x => (∫ v, ψ v*f n (x,v) ∂ν)^2/(1+fiberMass ν (f n) x))
      (fun x => (∫ v, ψ v*g (x,v) ∂ν)^2/(1+fiberMass ν g x)) := by
  have hkm : Measurable (fun z : X × (Y × Y) => ψ z.2.1*ψ z.2.2) :=
    (hψ.comp measurable_snd.fst).mul (hψ.comp measurable_snd.snd)
  have hkb (z : X × (Y × Y)) : |ψ z.2.1*ψ z.2.2| ≤ |C| * |C| := by
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self C)) ((hC _).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have h := hp.marginal (fun n => normalizedPair_integrable (hfm n) (hf n) (hfi n))
    hkm (|C| * |C|) hkb
  simpa only [square_identity ψ] using h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Normalizing the actual cutoff mixed gain by the velocity weight -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem normalized_mixed_cutoff_le_chart (hcarleman : Published.GPV2009CarlemanInput)
    (b q : ℝ) {c f : X × Velocity → ℝ} (hcm : Measurable c) (hfm : Measurable f)
    (hc : ∀ z, 0 ≤ c z) (hf : ∀ z, 0 ≤ f z) (x : X) :
    ∀ᵐ v : Velocity, ENNReal.ofReal (mixedGainDensity b c (fun z => H q z.2*f z) (x,v)) ≤
      ENNReal.ofReal (H q v)*chartGain (volume.withDensity (fun p => ENNReal.ofReal (c (x,p))))
        (fun p => ENNReal.ofReal (H q p/H q v)*ENNReal.ofReal (f (x,p))) v := by
  have hwm : Measurable (fun z => H q z.2*f z) :=
    ((ChartKernel.measurable_H q).comp measurable_snd).mul hfm
  have hwn (z) : 0 ≤ H q z.2*f z := mul_nonneg (H_nonneg q z.2) (hf z)
  filter_upwards [hcarleman (fun p => ENNReal.ofReal (c (x,p)))
    (fun p => ENNReal.ofReal (H q p*f (x,p)))
    ((hcm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)
    ((hwm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)] with v hv
  have h := mixedGainDensity_le_nonnegative b hcm hwm hc hwn (x,v)
  rw [hv] at h
  have he : (fun p => ENNReal.ofReal (H q p*f (x,p))) =
      (fun p => ENNReal.ofReal (H q v)*(ENNReal.ofReal (H q p/H q v)*ENNReal.ofReal (f (x,p)))) := by
    funext p
    rw [ENNReal.ofReal_mul (H_nonneg q p),← mul_assoc,
      ← ENNReal.ofReal_mul (H_nonneg q v)]
    congr 2
    field_simp [(H_pos q v).ne']
  rw [he,chartGain_const_mul_right _ _ ENNReal.ofReal_ne_top] at h
  exact h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
