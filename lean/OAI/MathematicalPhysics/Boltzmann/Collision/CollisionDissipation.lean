import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffLossFrequency
import OAI.MathematicalPhysics.Boltzmann.Branching.MovingCutoffWeakLimit
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianEstimates
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairRepresentative

namespace OAI

section

/-! # The moving relative-speed cutoff has the full collision limit -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

def truncatedPreRate (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  {z | ‖z.1.2.1-z.1.2.2‖ < b}.indicator (preRate f) z

def truncatedPostRate (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  {z | ‖z.1.2.1-z.1.2.2‖ < b}.indicator (postRate f) z

theorem truncatedPreRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) (b : ℝ) :
    Measurable (truncatedPreRate b f) :=
  (preRate_measurable hfm).indicator (measurableSet_lt (by fun_prop) measurable_const)

theorem truncatedPostRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) (b : ℝ) :
    Measurable (truncatedPostRate b f) :=
  ((preRate_measurable hfm).comp scatterTriple_measurable).indicator
    (measurableSet_lt (by fun_prop) measurable_const)

theorem cutoffGain_eq_marginal (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    KineticCollisionNullSets.gain b f p = ∫ q : Velocity × Sphere,
      truncatedPostRate b f (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea := by
  apply integral_congr_ae
  filter_upwards [] with q
  change CollisionCutoff.kernel b p.2 q.1 q.2 * f (p.1,scatterLeft p.2 q.1 q.2) *
    f (p.1,scatterRight p.2 q.1 q.2) =
    if ‖p.2-q.1‖ < b then postRate f ((p.1,(p.2,q.1)),q.2) else 0
  rw [postRate_formula]
  by_cases hq : ‖p.2-q.1‖ < b <;> simp [CollisionCutoff.kernel,hq]

theorem cutoffLoss_eq_marginal (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    cutoffLossDensity b f p = ∫ q : Velocity × Sphere,
      truncatedPreRate b f (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea := by
  apply integral_congr_ae
  filter_upwards [] with q
  change CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1) =
    if ‖p.2-q.1‖ < b then preRate f ((p.1,(p.2,q.1)),q.2) else 0
  by_cases hq : ‖p.2-q.1‖ < b <;> simp [CollisionCutoff.kernel,preRate,hq]

theorem weak_cutoff_gainLoss {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n z, 0 ≤ f n z) (hgm : Measurable g)
    (h : Published.WeakL1Converges (μ.prod (volume : Measure (Velocity × Velocity)))
      (fun n => pairDensity (f n)) (pairDensity g))
    (hf : ∀ n, Integrable (pairDensity (f n)) (μ.prod (volume : Measure (Velocity × Velocity))))
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop) :
    Published.WeakL1Converges (μ.prod volume)
      (fun n => KineticCollisionNullSets.gain (b n) (f n)) (gainDensity g) ∧
      Published.WeakL1Converges (μ.prod volume)
      (fun n => cutoffLossDensity (b n) (f n)) (lossDensity g) := by
  have hr : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => ‖z.1.2.1-z.1.2.2‖) := by
    fun_prop
  have hpre := (weak_preRate h hf).moving_cutoff
    (fun n => preRate_integrable (hfm n) (hfn n) (hf n))
    (fun n z => preRate_nonneg (hfn n) z) hr hb
  have hpost := (weak_postRate hfm hgm h hf).moving_cutoff
    (fun n => postRate_integrable (hfm n) (hfn n) (hf n))
    (fun n z => preRate_nonneg (hfn n) (scatterTriple z)) hr hb
  have hpre' := weak_grouped_rate (fun n => truncatedPreRate_measurable (hfm n) (b n))
    (preRate_measurable hgm) hpre
  have hpost' := weak_grouped_rate (fun n => truncatedPostRate_measurable (hfm n) (b n))
    ((preRate_measurable hgm).comp scatterTriple_measurable) hpost
  have hs n : MeasurableSet {z : (X × (Velocity × Velocity)) × Sphere |
      ‖z.1.2.1-z.1.2.2‖ < b n} := measurableSet_lt hr measurable_const
  have hpInt n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((postRate_integrable (hfm n) (hfn n) (hf n)).indicator (hs n))
  have hlInt n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    ((preRate_integrable (hfm n) (hfn n) (hf n)).indicator (hs n))
  have hp := hpost'.marginal hpInt (k := fun _ => 1) measurable_const 1 (fun _ => by norm_num)
  have hl := hpre'.marginal hlInt (k := fun _ => 1) measurable_const 1 (fun _ => by norm_num)
  simp only [one_mul,← cutoffGain_eq_marginal,← cutoffLoss_eq_marginal] at hp hl
  exact ⟨hp,hl⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Full collision terms are independent of the density representative -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem preRate_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    preRate f =ᵐ[(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea] preRate g := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := μ.prod (volume : Measure (Velocity × Velocity))) (ν := sphereArea)).ae
      (pairProduct_congr hfm hgm he)
  filter_upwards [hp] with z hz
  change f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) =
    g (z.1.1,z.1.2.1)*g (z.1.1,z.1.2.2) at hz
  simp only [preRate,mul_assoc,hz]

theorem postRate_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    postRate f =ᵐ[(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea] postRate g :=
  (scatterTriple_measurePreserving μ).quasiMeasurePreserving.ae (preRate_congr hfm hgm he)

theorem gainLoss_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    gainDensity f =ᵐ[μ.prod volume] gainDensity g ∧
      lossDensity f =ᵐ[μ.prod volume] lossDensity g := by
  have hp := (collisionGrouping_measurePreserving μ).symm.quasiMeasurePreserving.ae
    (postRate_congr hfm hgm he)
  have hl := (collisionGrouping_measurePreserving μ).symm.quasiMeasurePreserving.ae
    (preRate_congr hfm hgm he)
  constructor
  · filter_upwards [Measure.ae_ae_of_ae_prod hp] with p hp
    exact integral_congr_ae hp
  · filter_upwards [Measure.ae_ae_of_ae_prod hl] with p hp
    exact integral_congr_ae hp

theorem collision_fibers {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2 q.1 q.2*f (p.1,scatterLeft p.2 q.1 q.2)*
          f (p.1,scatterRight p.2 q.1 q.2)) ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2 q.1 q.2*f p*f (p.1,q.1))
        ((volume : Measure Velocity).prod sphereArea) := by
  have hp := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (postRate_integrable hfm hf hpair)
  have hl := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (preRate_integrable hfm hf hpair)
  filter_upwards [hp.prod_right_ae,hl.prod_right_ae] with p hp hl
  constructor
  · have he : (fun q : Velocity × Sphere => postRate f (collisionGrouping.symm (p,q))) =
        (fun q => collisionKernel p.2 q.1 q.2*f (p.1,scatterLeft p.2 q.1 q.2)*
          f (p.1,scatterRight p.2 q.1 q.2)) := by
      funext q
      exact postRate_formula f _
    change Integrable (fun q => postRate f (collisionGrouping.symm (p,q))) _ at hp
    rw [he] at hp
    exact hp
  · exact hl

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Particle interchange and elastic substitution for the cutoff collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def particleSwap : ((X × (Velocity × Velocity)) × Sphere) ≃ᵐ
    ((X × (Velocity × Velocity)) × Sphere) :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl X) MeasurableEquiv.prodComm)
    (MeasurableEquiv.refl Sphere)

theorem particleSwap_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (particleSwap (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := ((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap
      (μ := (volume : Measure Velocity)) (ν := (volume : Measure Velocity)))).prod
      (MeasurePreserving.id sphereArea)
  have he : (⇑(particleSwap (X := X))) = Prod.map (Prod.map id Prod.swap) id := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using h

theorem preRate_particleSwap (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : preRate f (particleSwap z) = preRate f z := by
  have hk : collisionKernel z.1.2.2 z.1.2.1 z.2 = collisionKernel z.1.2.1 z.1.2.2 z.2 := by
    unfold collisionKernel normalComponent
    rw [show z.1.2.2-z.1.2.1 = -(z.1.2.1-z.1.2.2) by abel,inner_neg_left,abs_neg]
  change collisionKernel z.1.2.2 z.1.2.1 z.2*f (z.1.1,z.1.2.2)*f (z.1.1,z.1.2.1) = _
  rw [hk]
  unfold preRate
  ring

theorem truncatedPreRate_particleSwap (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPreRate b f (particleSwap z) = truncatedPreRate b f z := by
  change (if ‖z.1.2.2-z.1.2.1‖ < b then preRate f (particleSwap z) else 0) =
    (if ‖z.1.2.1-z.1.2.2‖ < b then preRate f z else 0)
  rw [norm_sub_rev,preRate_particleSwap]

omit [MeasurableSpace X] in
theorem truncatedPreRate_scatter (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPreRate b f (scatterTriple z) = truncatedPostRate b f z := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  change (if ‖scatterLeft z.1.2.1 z.1.2.2 z.2-scatterRight z.1.2.1 z.1.2.2 z.2‖ < b
    then preRate f (scatterTriple z) else 0) = _
  rw [scatter_relative_speed _ _ _ hw]
  rfl

omit [MeasurableSpace X] in
theorem truncatedPostRate_scatter (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPostRate b f (scatterTriple z) = truncatedPreRate b f z := by
  rw [← truncatedPreRate_scatter,scatterTriple_involutive]

theorem integral_preRate_particleSwap (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
  simp only [truncatedPreRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
  simp only [truncatedPostRate_scatter] at h
  exact h.symm

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The gain rate and particle interchange -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem scatterLeft_swap (v w ω : Velocity) : scatterLeft w v ω = scatterRight v w ω := by
  have hn : normalComponent w v ω = -normalComponent v w ω := by
    unfold normalComponent
    rw [show w-v = -(v-w) by abel,inner_neg_left]
  simp only [scatterLeft,scatterRight,hn,neg_smul,sub_neg_eq_add]

theorem scatterRight_swap (v w ω : Velocity) : scatterRight w v ω = scatterLeft v w ω := by
  exact (scatterLeft_swap w v ω).symm

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem scatterTriple_particleSwap (z : (X × (Velocity × Velocity)) × Sphere) :
    scatterTriple (particleSwap z) = particleSwap (scatterTriple z) := by
  change ((z.1.1,(scatterLeft z.1.2.2 z.1.2.1 z.2,scatterRight z.1.2.2 z.1.2.1 z.2)),z.2) =
    ((z.1.1,(scatterRight z.1.2.1 z.1.2.2 z.2,scatterLeft z.1.2.1 z.1.2.2 z.2)),z.2)
  exact congrArg (fun p : Velocity × Velocity => ((z.1.1,p),z.2))
    (Prod.ext (scatterLeft_swap z.1.2.1 z.1.2.2 z.2)
      (scatterRight_swap z.1.2.1 z.1.2.2 z.2))

theorem postRate_particleSwap (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : postRate f (particleSwap z) = postRate f z := by
  change preRate f (scatterTriple (particleSwap z)) = preRate f (scatterTriple z)
  rw [scatterTriple_particleSwap,preRate_particleSwap]

theorem truncatedPostRate_particleSwap (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPostRate b f (particleSwap z) = truncatedPostRate b f z := by
  change (if ‖z.1.2.2-z.1.2.1‖ < b then postRate f (particleSwap z) else 0) =
    (if ‖z.1.2.1-z.1.2.2‖ < b then postRate f z else 0)
  rw [norm_sub_rev,postRate_particleSwap]

theorem integral_postRate_particleSwap (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
  simp only [truncatedPostRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter_right (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z)
  simp only [truncatedPostRate_scatter] at h
  exact h.symm

end CollisionCompactness
end BoltzmannNonuniqueness

end

end

section

/-! # The symmetric weak collision identity with the invariant speed cutoff -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def collisionJump (ψ : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)+
    ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-ψ (z.1.1,z.1.2.1)-ψ (z.1.1,z.1.2.2)

theorem cutoff_weak_identity {μ : Measure X} [SFinite μ] (b : ℝ) (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    (1/2:ℝ) * ∫ z, collisionJump ψ z*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,truncatedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have he : (fun z => collisionJump ψ z*truncatedPreRate b f z) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)+
      (fun z => ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z) := by
    funext z
    dsimp [collisionJump]
    ring
  rw [he,integral_sub' ((hl'.add hr').sub hpre) hr,
    integral_sub' (hl'.add hr') hpre,integral_add' hl' hr']
  rw [← integral_postRate_scatter,← integral_postRate_scatter_right,
    ← integral_postRate_particleSwap,← integral_preRate_particleSwap]
  ring

theorem cutoff_collision_invariant {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : ∀ z, collisionJump ψ z = 0) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := cutoff_weak_identity b f ψ hpre hpost
  simp only [hψ,zero_mul,integral_zero,mul_zero,sub_eq_zero] at h
  exact h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The weak collision identity for the full hard-sphere operator -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem preRate_scatter_full (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    preRate f (scatterTriple z) = postRate f z := rfl

omit [MeasurableSpace X] in
theorem postRate_scatter_full (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    postRate f (scatterTriple z) = preRate f z := by
  change preRate f (scatterTriple (scatterTriple z)) = _
  rw [scatterTriple_involutive]

theorem integral_preRate_particleSwap_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
  simp only [preRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
  simp only [postRate_scatter_full] at h
  exact h.symm

theorem integral_postRate_particleSwap_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
  simp only [postRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter_right_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.2)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.2)*postRate f z)
  simp only [postRate_scatter_full] at h
  exact h.symm

theorem full_weak_identity {μ : Measure X} [SFinite μ] (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    (1/2:ℝ) * ∫ z, collisionJump ψ z*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*preRate f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,preRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*postRate f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,postRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*preRate f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,postRate_scatter_full] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*preRate f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,postRate_scatter_full] at h
    exact h
  have he : (fun z => collisionJump ψ z*preRate f z) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*preRate f z)+
      (fun z => ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*preRate f z)-
      (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)-
      (fun z => ψ (z.1.1,z.1.2.2)*preRate f z) := by
    funext z
    dsimp [collisionJump]
    ring
  rw [he,integral_sub' ((hl'.add hr').sub hpre) hr,
    integral_sub' (hl'.add hr') hpre,integral_add' hl' hr']
  rw [← integral_postRate_scatter_full,← integral_postRate_scatter_right_full,
    ← integral_postRate_particleSwap_full,← integral_preRate_particleSwap_full]
  ring

theorem full_collision_invariant {μ : Measure X} [SFinite μ]
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : ∀ z, collisionJump ψ z = 0) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.1)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := full_weak_identity f ψ hpre hpost
  simp only [hψ,zero_mul,integral_zero,mul_zero,sub_eq_zero] at h
  exact h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Passing collision tests between rates and the physical gain/loss marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem collision_test_marginal {μ : Measure X} [SFinite μ]
    (r : (X × (Velocity × Velocity)) × Sphere → ℝ) (ψ : X × Velocity → ℝ)
    (hi : Integrable (fun z => ψ (z.1.1,z.1.2.1)*r z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea)) (μ.prod volume) ∧
    (∫ p, ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea) ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*r z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have hg := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hi
  have he : (fun p : X × Velocity => ∫ q : Velocity × Sphere,
      ψ p*r (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea) =
      (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
        ∂(volume : Measure Velocity).prod sphereArea)) := by
    funext p
    exact integral_const_mul _ _
  have hgroup : Integrable (fun y : (X × Velocity) × (Velocity × Sphere) =>
      ψ y.1*r (collisionGrouping.symm y))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := hg
  constructor
  · have h := hgroup.integral_prod_left
    rw [he] at h
    exact h
  · calc
      _ = ∫ p, ∫ q : Velocity × Sphere, ψ p*r (collisionGrouping.symm (p,q))
          ∂(volume : Measure Velocity).prod sphereArea ∂μ.prod volume := by rw [he]
      _ = ∫ y : (X × Velocity) × (Velocity × Sphere), ψ y.1*r (collisionGrouping.symm y)
          ∂(μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea) :=
        (integral_prod _ hgroup).symm
      _ = _ := (collisionGrouping_measurePreserving μ).symm.integral_comp
        collisionGrouping.symm.measurableEmbedding (fun z => ψ (z.1.1,z.1.2.1)*r z)

theorem cutoff_test_integrals {μ : Measure X} [SFinite μ] (b : ℝ) (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ p, ψ p*KineticCollisionNullSets.gain b f p ∂μ.prod volume) -
      (∫ p, ψ p*cutoffLossDensity b f p ∂μ.prod volume) =
    (1/2:ℝ) * ∫ z, collisionJump ψ z*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have hp := (collision_test_marginal (truncatedPostRate b f) ψ hpost).2
  have hl := (collision_test_marginal (truncatedPreRate b f) ψ hpre).2
  simp only [← cutoffGain_eq_marginal] at hp
  simp only [← cutoffLoss_eq_marginal] at hl
  rw [hp,hl]
  exact cutoff_weak_identity b f ψ hpre hpost

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Recovering weighted collision-rate integrability from a nonnegative marginal -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

theorem collision_test_integrable_of_marginal {μ : Measure X} [SFinite μ]
    {r : (X × (Velocity × Velocity)) × Sphere → ℝ} (hrm : Measurable r)
    (hrn : ∀ z, 0 ≤ r z)
    (hri : Integrable r ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    {ψ : X × Velocity → ℝ} (hψm : Measurable ψ)
    (hψi : Integrable (fun p => ψ p*(∫ q : Velocity × Sphere,
      r (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea)) (μ.prod volume)) :
    Integrable (fun z => ψ (z.1.1,z.1.2.1)*r z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let s : (X × Velocity) × (Velocity × Sphere) → ℝ := fun z => r (collisionGrouping.symm z)
  have hsm : Measurable s := hrm.comp collisionGrouping.symm.measurable
  have hsi : Integrable s ((μ.prod (volume : Measure Velocity)).prod
      ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hri
  have hweighted : Integrable (fun z => ψ z.1*s z) ((μ.prod (volume : Measure Velocity)).prod
      ((volume : Measure Velocity).prod sphereArea)) := by
    apply (integrable_prod_iff ((hψm.comp measurable_fst).mul hsm).aestronglyMeasurable).mpr
    refine ⟨?_,?_⟩
    · filter_upwards [hsi.prod_right_ae] with p hp
      exact hp.const_mul (ψ p)
    · apply hψi.norm.congr
      filter_upwards [] with p
      have hn : 0 ≤ ∫ q : Velocity × Sphere, s (p,q) ∂(volume : Measure Velocity).prod sphereArea :=
        integral_nonneg (fun q => hrn _)
      change |ψ p*(∫ q : Velocity × Sphere, s (p,q) ∂(volume : Measure Velocity).prod sphereArea)| =
        ∫ q : Velocity × Sphere, |ψ p*s (p,q)| ∂(volume : Measure Velocity).prod sphereArea
      rw [abs_mul,abs_of_nonneg hn]
      calc
        _ = ∫ q : Velocity × Sphere, |ψ p| * s (p,q)
            ∂(volume : Measure Velocity).prod sphereArea := (integral_const_mul _ _).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with q
          rw [abs_mul,abs_of_nonneg (hrn _)]

  exact (collisionGrouping_measurePreserving μ).integrable_comp_of_integrable hweighted

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The mass, momentum, and energy collision invariants -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_mass (a : X → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p => a p.1) z = 0 := by
  unfold collisionJump
  ring

omit [MeasurableSpace X] in
theorem collisionJump_momentum (i : Fin 3) (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p : X × Velocity => p.2 i) z = 0 := by
  have h := congrArg (fun v : Velocity => v i) (scatter_momentum z.1.2.1 z.1.2.2 z.2)
  change (scatterLeft z.1.2.1 z.1.2.2 z.2) i+
    (scatterRight z.1.2.1 z.1.2.2 z.2) i = z.1.2.1 i+z.1.2.2 i at h
  change (scatterLeft z.1.2.1 z.1.2.2 z.2) i+
    (scatterRight z.1.2.1 z.1.2.2 z.2) i-z.1.2.1 i-z.1.2.2 i = 0
  linarith

omit [MeasurableSpace X] in
theorem collisionJump_energy (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p : X × Velocity => ‖p.2‖^2) z = 0 := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have h := scatter_energy z.1.2.1 z.1.2.2 z.2 hw
  unfold collisionJump
  linarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Maxwellian and density logarithms under collision symmetry -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_log_maxwellian (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p : X × Velocity => Real.log (maxwellian p.2)) z = 0 := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have he := scatter_energy z.1.2.1 z.1.2.2 z.2 hw
  unfold collisionJump
  simp only [log_maxwellian]
  linarith

omit [MeasurableSpace X] in
theorem collisionJump_log_density (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p => Real.log (f p)) z =
      Real.log ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
        f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))/(f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))) := by
  rw [Real.log_div (mul_ne_zero (hf _).ne' (hf _).ne') (mul_ne_zero (hf _).ne' (hf _).ne'),
    Real.log_mul (hf _).ne' (hf _).ne',Real.log_mul (hf _).ne' (hf _).ne']
  unfold collisionJump
  ring

omit [MeasurableSpace X] in
theorem collisionJump_scatter (ψ : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump ψ (scatterTriple z) = -collisionJump ψ z := by
  have hi := scatterTriple_involutive (X := X) z
  have hl := congrArg (fun p => p.1.2.1) hi
  have hr := congrArg (fun p => p.1.2.2) hi
  change scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2 = z.1.2.1 at hl
  change scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2 = z.1.2.2 at hr
  change ψ (z.1.1,scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)+
    ψ (z.1.1,scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)-
    ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)-
    ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) = _
  rw [hl,hr]
  unfold collisionJump
  ring

end CollisionCompactness
end BoltzmannNonuniqueness

end

end

section

/-! # Symmetric collision production and its entropy sign -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem integral_jump_post (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, collisionJump ψ z*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(∫ z, collisionJump ψ z*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => collisionJump ψ z*truncatedPostRate b f z)
  simp only [collisionJump_scatter,truncatedPostRate_scatter,neg_mul,integral_neg] at h
  exact h.symm

theorem collisionJump_integrable {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun z => collisionJump ψ z*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (fun z => collisionJump ψ z*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,truncatedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have hp : Integrable (fun z => collisionJump ψ z*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := ((hl'.add hr').sub hpre).sub hr
    convert h using 1
    funext z
    dsimp [collisionJump]
    ring
  refine ⟨hp,?_⟩
  have ht := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hp
  simp only [Function.comp_def,collisionJump_scatter,truncatedPreRate_scatter,neg_mul] at ht
  convert ht.neg using 1
  funext z
  simp only [Pi.neg_apply,neg_neg]

theorem cutoff_production_identity {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(1/4:ℝ) * ∫ z, collisionJump ψ z*(truncatedPostRate b f z-truncatedPreRate b f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable b f ψ hpre hpost
  simp_rw [mul_sub]
  rw [integral_sub hjpost hjpre,integral_jump_post]
  have h := cutoff_weak_identity b f ψ hpre hpost
  linarith

omit [MeasurableSpace X] in
theorem entropy_production_nonneg (b : ℝ) (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionJump (fun p => Real.log (f p)) z*
      (truncatedPostRate b f z-truncatedPreRate b f z) := by
  let A := f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let B := f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)
  have hA : 0 < A := mul_pos (hf _) (hf _)
  have hB : 0 < B := mul_pos (hf _) (hf _)
  have hsign : 0 ≤ (Real.log A-Real.log B)*(A-B) := by
    by_cases hBA : B ≤ A
    · exact mul_nonneg (sub_nonneg.mpr (Real.log_le_log hB hBA)) (sub_nonneg.mpr hBA)
    · have hAB : A ≤ B := le_of_lt (lt_of_not_ge hBA)
      exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.log_le_log hA hAB)) (sub_nonpos.mpr hAB)
  rw [collisionJump_log_density f hf,Real.log_div hA.ne' hB.ne']
  change 0 ≤ (Real.log A-Real.log B)*
    ((if ‖z.1.2.1-z.1.2.2‖ < b then postRate f z else 0)-
      (if ‖z.1.2.1-z.1.2.2‖ < b then preRate f z else 0))
  by_cases hc : ‖z.1.2.1-z.1.2.2‖ < b
  · simp only [hc,↓reduceIte,postRate_formula,preRate]
    have he : collisionKernel z.1.2.1 z.1.2.2 z.2*
        f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-
        collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) =
        collisionKernel z.1.2.1 z.1.2.2 z.2*(A-B) := by dsimp [A,B]; ring
    rw [he]
    have h := mul_nonneg (collisionKernel_nonneg z.1.2.1 z.1.2.2 z.2) hsign
    nlinarith only [h]
  · simp only [hc,↓reduceIte,sub_self,mul_zero,le_refl]

theorem cutoff_entropy_nonpositive {μ : Measure X} [SFinite μ] (b : ℝ)
    (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (hpre : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1))*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1))*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ z, Real.log (f (z.1.1,z.1.2.1))*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, Real.log (f (z.1.1,z.1.2.1))*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤ 0 := by
  rw [cutoff_production_identity b f (fun p => Real.log (f p)) hpre hpost]
  have h : 0 ≤ ∫ z, collisionJump (fun p => Real.log (f p)) z*
      (truncatedPostRate b f z-truncatedPreRate b f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
    integral_nonneg (fun z => entropy_production_nonneg b f hf z)
  linarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
