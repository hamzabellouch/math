import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffLossFrequency
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.IncomingLossRate
import OAI.MathematicalPhysics.Boltzmann.Branching.MixedRealGain
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairBoundedTruncation

namespace OAI

section

/-! # Polarized cutoff rates and their exact collision-map symmetries -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def mixedPreRate (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2*c (z.1.1,z.1.2.1)*h (z.1.1,z.1.2.2)

def mixedPostRate (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  mixedPreRate b c h (scatterTriple z)

def mixedGainDensity (b : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  (1/2 : ℝ)*((∫ q : Velocity × Sphere, mixedPostRate b c h (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea)+
    (∫ q : Velocity × Sphere, mixedPostRate b h c (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea))

theorem mixedPreRate_measurable {c h : X × Velocity → ℝ}
    (hc : Measurable c) (hh : Measurable h) (b : ℝ) : Measurable (mixedPreRate b c h) := by
  have hk : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2) := by
    unfold CollisionCutoff.kernel
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · unfold collisionKernel normalComponent
      fun_prop
    · exact measurable_const
  exact (hk.mul (hc.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst))).mul
    (hh.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd))

theorem mixedPreRate_particleSwap (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPreRate b c h (particleSwap z) = mixedPreRate b h c z := by
  have hk : collisionKernel z.1.2.2 z.1.2.1 z.2 = collisionKernel z.1.2.1 z.1.2.2 z.2 := by
    unfold collisionKernel normalComponent
    rw [show z.1.2.2-z.1.2.1 = -(z.1.2.1-z.1.2.2) by abel,inner_neg_left,abs_neg]
  change CollisionCutoff.kernel b z.1.2.2 z.1.2.1 z.2*c (z.1.1,z.1.2.2)*h (z.1.1,z.1.2.1) = _
  unfold mixedPreRate CollisionCutoff.kernel
  rw [norm_sub_rev,hk]
  ring

theorem mixedPostRate_particleSwap (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b c h (particleSwap z) = mixedPostRate b h c z := by
  unfold mixedPostRate
  rw [scatterTriple_particleSwap,mixedPreRate_particleSwap]

omit [MeasurableSpace X] in
theorem mixedPostRate_scatter (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b c h (scatterTriple z) = mixedPreRate b c h z := by
  unfold mixedPostRate
  rw [scatterTriple_involutive]

omit [MeasurableSpace X] in
theorem mixedPostRate_formula (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b c h z = CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2*
      c (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*h (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  change CollisionCutoff.kernel b (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2* _ * _ = _
  rw [CollisionCutoff.kernel_scatter]
  rfl

theorem integral_mixedPostRate_scatter (μ : Measure X) [SFinite μ] (b : ℝ)
    (c h ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*mixedPostRate b c h z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have he := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*mixedPostRate b c h z)
  calc
    _ = ∫ z, ψ ((scatterTriple z).1.1,(scatterTriple z).1.2.1)*
        mixedPostRate b c h (scatterTriple z)
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := he.symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by dsimp only; rw [mixedPostRate_scatter]; rfl)

theorem integral_mixedPostRate_swap (μ : Measure X) [SFinite μ] (b : ℝ)
    (c h ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*mixedPostRate b h c z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have he := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*mixedPreRate b h c z)
  rw [integral_mixedPostRate_scatter]
  have he' : (∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*mixedPreRate b h c z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
    calc
      _ = ∫ z, ψ ((particleSwap z).1.1,
          scatterLeft (particleSwap z).1.2.1 (particleSwap z).1.2.2 (particleSwap z).2)*
          mixedPreRate b h c (particleSwap z)
          ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by
          dsimp only
          rw [mixedPreRate_particleSwap]
          change ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z =
            ψ (z.1.1,scatterLeft z.1.2.2 z.1.2.1 z.2)*mixedPreRate b c h z
          rw [scatterLeft_swap])
      _ = _ := he
  exact he'.symm

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrability of polarized collision rates from one incoming pair moment -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixedPreRate_integrable {μ : Measure X} {c h : X × Velocity → ℝ}
    (hc : Measurable c) (hh : Measurable h) (hcn : ∀ p, 0 ≤ c p) (hhn : ∀ p, 0 ≤ h p)
    (hi : Integrable (fun p : X × (Velocity × Velocity) =>
      (1+‖p.2.1‖+‖p.2.2‖)*c (p.1,p.2.1)*h (p.1,p.2.2)) (μ.prod volume)) (b : ℝ) :
    Integrable (mixedPreRate b c h) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply (hi.comp_fst sphereArea).mono' (mixedPreRate_measurable hc hh b).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    have hk : CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2 ≤ 1+‖z.1.2.1‖+‖z.1.2.2‖ :=
      (CollisionCutoff.kernel_le b _ _ _).trans ((collisionKernel_le_norm _ _ _).trans
        ((norm_sub_le _ _).trans (by linarith)))
    change ‖CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2*c (z.1.1,z.1.2.1)*h (z.1.1,z.1.2.2)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (hcn _)) (hhn _))]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (hcn _)) (hhn _))

theorem mixedPostRate_integrable {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (mixedPostRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi

theorem mixedPostRate_test_integrable {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h ψ : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ p, |ψ p| ≤ B) :
    Integrable (fun z => ψ (z.1.1,z.1.2.1)*mixedPostRate b c h z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply (mixedPostRate_integrable hi).bdd_mul
    (hψ.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    change ‖ψ (z.1.1,z.1.2.1)‖ ≤ B
    simpa only [Real.norm_eq_abs] using hB (z.1.1,z.1.2.1))

theorem mixedPreRate_swapped_integrable {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (mixedPreRate b h c)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have ht := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hi
  apply ht.congr
  exact ae_of_all _ (fun z => by dsimp only [Function.comp_def]; rw [mixedPreRate_particleSwap])

theorem mixedPreRate_sum_test_integrable {μ : Measure X} {b : ℝ}
    {c h ψ : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ p, |ψ p| ≤ B) :
    Integrable (fun z => (ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)+
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))*mixedPreRate b c h z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hm₁ : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hm₂ : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)) := by
    unfold scatterRight normalComponent
    fun_prop
  apply hi.bdd_mul ((hψ.comp hm₁).add (hψ.comp hm₂)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact (abs_add_le _ _).trans (add_le_add (hB _) (hB _)))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Exact polarization of the finite-cutoff gain -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem mixedPreRate_self (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPreRate b f f z = truncatedPreRate b f z := by
  unfold mixedPreRate CollisionCutoff.kernel truncatedPreRate preRate
  by_cases hz : ‖z.1.2.1-z.1.2.2‖ < b <;> simp [hz]

omit [MeasurableSpace X] in
theorem mixedPostRate_self (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b f f z = truncatedPostRate b f z := by
  rw [mixedPostRate,mixedPreRate_self,truncatedPreRate_scatter]

omit [MeasurableSpace X] in
theorem mixedPostRate_add_self (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b (c+h) (c+h) z =
      mixedPostRate b c c z+mixedPostRate b c h z+
        mixedPostRate b h c z+mixedPostRate b h h z := by
  unfold mixedPostRate mixedPreRate
  simp only [Pi.add_apply]
  ring

theorem mixedGainDensity_self (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    mixedGainDensity b f f p = KineticCollisionNullSets.gain b f p := by
  rw [mixedGainDensity,cutoffGain_eq_marginal]
  simp_rw [mixedPostRate_self]
  ring

theorem cutoffGain_add (b : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity)
    (hcc : Integrable (fun q : Velocity × Sphere => mixedPostRate b c c (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea))
    (hch : Integrable (fun q : Velocity × Sphere => mixedPostRate b c h (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea))
    (hhc : Integrable (fun q : Velocity × Sphere => mixedPostRate b h c (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea))
    (hhh : Integrable (fun q : Velocity × Sphere => mixedPostRate b h h (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea)) :
    KineticCollisionNullSets.gain b (c+h) p = KineticCollisionNullSets.gain b c p+
      2*mixedGainDensity b c h p+KineticCollisionNullSets.gain b h p := by
  have he (f : X × Velocity → ℝ) :
      (∫ q : Velocity × Sphere, mixedPostRate b f f (collisionGrouping.symm (p,q))
        ∂(volume : Measure Velocity).prod sphereArea) = KineticCollisionNullSets.gain b f p := by
    simp_rw [mixedPostRate_self]
    exact (cutoffGain_eq_marginal b f p).symm
  rw [← he (c+h)]
  simp_rw [mixedPostRate_add_self]
  have h₁ := integral_add ((hcc.add hch).add hhc) hhh
  have h₂ := integral_add (hcc.add hch) hhc
  have h₃ := integral_add hcc hch
  simp only [Pi.add_apply] at h₁ h₂ h₃
  rw [h₁,h₂,h₃,he c,he h]
  dsimp only [mixedGainDensity]
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Identification of the polarized loss marginal with hot density times cold frequency -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

def mixedLossDensity (b : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, CollisionCutoff.kernel b p.2 q.1 q.2*h p*c (p.1,q.1)
    ∂(volume : Measure Velocity).prod sphereArea

omit [MeasurableSpace X] in
theorem mixedLossDensity_eq_frequency (b : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity)
    (hi : Integrable (fun q : Velocity × Sphere =>
      CollisionCutoff.kernel b p.2 q.1 q.2*h p*c (p.1,q.1))
      ((volume : Measure Velocity).prod sphereArea)) :
    mixedLossDensity b c h p = h p*KineticCollisionNullSets.frequency b c p := by
  unfold mixedLossDensity
  rw [integral_prod _ hi]
  simp_rw [integral_mul_const,integral_cutoffKernel]
  calc
    _ = ∫ w : Velocity, (h p*(2*Real.pi))*(CollisionCutoff.rate b p.2 w*c (p.1,w)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun w => by ring)
    _ = _ := by
      rw [integral_const_mul]
      unfold KineticCollisionNullSets.frequency CollisionCutoff.frequency
      ring

theorem mixed_loss_ae_eq_frequency {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    mixedLossDensity b c h =ᵐ[μ.prod (volume : Measure Velocity)]
      fun p => h p*KineticCollisionNullSets.frequency b c p := by
  have ht := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (mixedPreRate_swapped_integrable hi)
  filter_upwards [ht.prod_right_ae] with p hp
  exact mixedLossDensity_eq_frequency b c h p hp

theorem mixed_loss_test_integrable {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h ψ : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ p, |ψ p| ≤ B) :
    Integrable (fun p => ψ p*(h p*KineticCollisionNullSets.frequency b c p)) (μ.prod volume) := by
  have hs := mixedPreRate_swapped_integrable hi
  have ht : Integrable (fun z => ψ (z.1.1,z.1.2.1)*mixedPreRate b h c z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    apply hs.bdd_mul (hψ.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      change ‖ψ (z.1.1,z.1.2.1)‖ ≤ B
      simpa only [Real.norm_eq_abs] using hB _)
  have hm := (collision_test_marginal (mixedPreRate b h c) ψ ht).1
  apply hm.congr
  filter_upwards [mixed_loss_ae_eq_frequency hi] with p hp
  change ψ p*mixedLossDensity b c h p = _
  rw [hp]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The symmetric mixed gain tested against outgoing velocities -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixedGain_test_identity {μ : Measure X} [SFinite μ] (b : ℝ)
    (c h ψ : X × Velocity → ℝ)
    (hi : Integrable (fun z => ψ (z.1.1,z.1.2.1)*mixedPostRate b c h z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hi' : Integrable (fun z => ψ (z.1.1,z.1.2.1)*mixedPostRate b h c z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ p, ψ p*mixedGainDensity b c h p ∂μ.prod volume) =
      (1/2 : ℝ)*(∫ z,
        (ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)+
         ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))*mixedPreRate b c h z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  have hL : Integrable (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z) ν := by
    have ht := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hi
    apply ht.congr
    exact ae_of_all _ (fun z => by dsimp only [Function.comp_def]; rw [mixedPostRate_scatter]; rfl)
  have hswap : Integrable (fun z => ψ (z.1.1,z.1.2.2)*mixedPostRate b c h z) ν := by
    have ht := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hi'
    apply ht.congr
    exact ae_of_all _ (fun z => by dsimp only [Function.comp_def]; rw [mixedPostRate_particleSwap]; rfl)
  have hR : Integrable (fun z => ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z) ν := by
    have ht := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hswap
    apply ht.congr
    exact ae_of_all _ (fun z => by dsimp only [Function.comp_def]; rw [mixedPostRate_scatter]; rfl)
  have h₁ := collision_test_marginal (mixedPostRate b c h) ψ hi
  have h₂ := collision_test_marginal (mixedPostRate b h c) ψ hi'
  calc
    _ = (1/2 : ℝ)*((∫ p, ψ p*(∫ q : Velocity × Sphere,
        mixedPostRate b c h (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea) ∂μ.prod volume)+
        (∫ p, ψ p*(∫ q : Velocity × Sphere,
        mixedPostRate b h c (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea) ∂μ.prod volume)) := by
      rw [← integral_add h₁.1 h₂.1,← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by dsimp only [mixedGainDensity]; ring)
    _ = (1/2 : ℝ)*((∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z ∂ν)+
        (∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*mixedPreRate b c h z ∂ν)) := by
      rw [h₁.2,h₂.2,integral_mixedPostRate_scatter,integral_mixedPostRate_swap]
    _ = _ := by
      rw [← integral_add hL hR]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by ring)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The physical mixed loss tested in the two incoming velocities -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem relativeCutoff_incomingLoss (b : ℝ) (φ : Velocity → ℝ) (p : Velocity × Velocity) :
    relativeCutoff b (incomingLossTest φ) p =
      2*Real.pi*CollisionCutoff.rate b p.1 p.2*φ p.2 := by
  unfold relativeCutoff incomingLossTest CollisionCutoff.rate
  split_ifs <;> ring

theorem mixed_loss_velocity_integral (b : ℝ) (c h φ : Velocity → ℝ)
    (hi : Integrable (fun p : Velocity × Velocity =>
      c p.1*h p.2*relativeCutoff b (incomingLossTest φ) p)) :
    (∫ v, (φ v*h v)*CollisionCutoff.frequency b c v) =
      ∫ p : Velocity × Velocity, c p.1*h p.2*relativeCutoff b (incomingLossTest φ) p := by
  rw [Measure.volume_eq_prod Velocity Velocity] at hi ⊢
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    have he : (fun w => c w*h v*relativeCutoff b (incomingLossTest φ) (w,v)) =
        (fun w => ((φ v*h v)*(2*Real.pi))*(CollisionCutoff.rate b v w*c w)) := by
      funext w
      rw [relativeCutoff_incomingLoss]
      have hs : CollisionCutoff.rate b w v = CollisionCutoff.rate b v w := by
        simp only [CollisionCutoff.rate,norm_sub_rev]
      rw [hs]
      ring
    dsimp only
    rw [he,integral_const_mul]
    unfold CollisionCutoff.frequency
    ring)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Physical mixed gain equals the incoming continuous collision test -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem mixed_pre_angular_integral (b : ℝ) (c h : X × Velocity → ℝ)
    (φ : Velocity → ℝ) (x : X) (p : Velocity × Velocity) :
    (∫ ω : Sphere, (φ (scatterLeft p.1 p.2 ω)+φ (scatterRight p.1 p.2 ω))*
      mixedPreRate b c h ((x,p),ω) ∂sphereArea) =
      2*(c (x,p.1)*h (x,p.2)*relativeCutoff b (incomingGainTest φ) p) := by
  by_cases hb : ‖p.1-p.2‖ < b
  · have he : (fun ω : Sphere => (φ (scatterLeft p.1 p.2 ω)+φ (scatterRight p.1 p.2 ω))*
        mixedPreRate b c h ((x,p),ω)) =
        (fun ω : Sphere => (c (x,p.1)*h (x,p.2))*(collisionKernel p.1 p.2 ω*
          (φ (scatterLeft p.1 p.2 ω)+φ (scatterRight p.1 p.2 ω)))) := by
      funext ω
      simp only [mixedPreRate,CollisionCutoff.kernel,ite_eq_left hb]
      ring
    rw [he,integral_const_mul]
    simp only [relativeCutoff,ite_eq_left hb,incomingGainTest]
    ring
  · simp only [mixedPreRate,CollisionCutoff.kernel,ite_eq_right hb,mul_zero,zero_mul,
      integral_zero,relativeCutoff]

theorem mixedGain_test_incoming {μ : Measure X} [SFinite μ] (b : ℝ)
    (c h : X × Velocity → ℝ) (θ : X → ℝ) (φ : Velocity → ℝ)
    (hi : Integrable (fun z => (θ z.1.1*φ z.1.2.1)*mixedPostRate b c h z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hi' : Integrable (fun z => (θ z.1.1*φ z.1.2.1)*mixedPostRate b h c z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpre : Integrable (fun z =>
      ((θ z.1.1*φ (scatterLeft z.1.2.1 z.1.2.2 z.2))+
       (θ z.1.1*φ (scatterRight z.1.2.1 z.1.2.2 z.2)))*mixedPreRate b c h z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ p, (θ p.1*φ p.2)*mixedGainDensity b c h p ∂μ.prod volume) =
      ∫ p, θ p.1*(c (p.1,p.2.1)*h (p.1,p.2.2)*
        relativeCutoff b (incomingGainTest φ) p.2) ∂μ.prod volume := by
  rw [mixedGain_test_identity b c h (fun p => θ p.1*φ p.2) hi hi',integral_prod _ hpre]
  have he (p : X × (Velocity × Velocity)) :
      (∫ ω : Sphere, ((θ p.1*φ (scatterLeft p.2.1 p.2.2 ω))+
       (θ p.1*φ (scatterRight p.2.1 p.2.2 ω)))*mixedPreRate b c h (p,ω) ∂sphereArea) =
      2*(θ p.1*(c (p.1,p.2.1)*h (p.1,p.2.2)*relativeCutoff b (incomingGainTest φ) p.2)) := by
    have he' : (fun ω : Sphere => ((θ p.1*φ (scatterLeft p.2.1 p.2.2 ω))+
        (θ p.1*φ (scatterRight p.2.1 p.2.2 ω)))*mixedPreRate b c h (p,ω)) =
        (fun ω : Sphere => θ p.1*((φ (scatterLeft p.2.1 p.2.2 ω)+φ (scatterRight p.2.1 p.2.2 ω))*
          mixedPreRate b c h (p,ω))) := by funext ω; ring
    rw [he',integral_const_mul,mixed_pre_angular_integral]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Incoming-test representation of the physical mixed loss -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem mixed_pre_loss_angular_integral (b : ℝ) (c h : X × Velocity → ℝ)
    (θ : X → ℝ) (φ : Velocity → ℝ) (p : X × (Velocity × Velocity)) :
    (∫ ω : Sphere, (θ p.1*φ p.2.2)*mixedPreRate b c h (p,ω) ∂sphereArea) =
      θ p.1*(c (p.1,p.2.1)*h (p.1,p.2.2)*relativeCutoff b (incomingLossTest φ) p.2) := by
  have he : (fun ω : Sphere => (θ p.1*φ p.2.2)*mixedPreRate b c h (p,ω)) =
      (fun ω : Sphere => ((θ p.1*φ p.2.2)*c (p.1,p.2.1)*h (p.1,p.2.2))*
        CollisionCutoff.kernel b p.2.1 p.2.2 ω) := by
    funext ω
    dsimp only [mixedPreRate]
    ring
  rw [he,integral_const_mul,integral_cutoffKernel,relativeCutoff_incomingLoss]
  ring

theorem mixedLoss_test_incoming {μ : Measure X} [SFinite μ] (b : ℝ)
    (c h : X × Velocity → ℝ) (θ : X → ℝ) (φ : Velocity → ℝ)
    (hi : Integrable (fun z => (θ z.1.1*φ z.1.2.1)*mixedPreRate b h c z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ p, (θ p.1*φ p.2)*mixedLossDensity b c h p ∂μ.prod volume) =
      ∫ p, θ p.1*(c (p.1,p.2.1)*h (p.1,p.2.2)*relativeCutoff b (incomingLossTest φ) p.2)
        ∂μ.prod volume := by
  have hs : Integrable (fun z => (θ z.1.1*φ z.1.2.2)*mixedPreRate b c h z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have ht := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hi
    apply ht.congr
    exact ae_of_all _ (fun z => by dsimp only [Function.comp_def]; rw [mixedPreRate_particleSwap]; rfl)
  have he := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => (θ z.1.1*φ z.1.2.1)*mixedPreRate b h c z)
  have hswap : (∫ z, (θ z.1.1*φ z.1.2.1)*mixedPreRate b h c z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      ∫ z, (θ z.1.1*φ z.1.2.2)*mixedPreRate b c h z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
    calc
      _ = ∫ z, (θ (particleSwap z).1.1*φ (particleSwap z).1.2.1)*
          mixedPreRate b h c (particleSwap z)
          ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := he.symm
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun z => by dsimp only; rw [mixedPreRate_particleSwap]; rfl)
  have hm := (collision_test_marginal (mixedPreRate b h c) (fun p => θ p.1*φ p.2) hi).2
  change (∫ p, (θ p.1*φ p.2)*mixedLossDensity b c h p ∂μ.prod volume) = _ at hm
  rw [hm,hswap,integral_prod _ hs]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => mixed_pre_loss_angular_integral b c h θ φ p)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The mixed cutoff gain respects almost-everywhere density representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixedGain_congr_ae (μ : Measure X) [SFinite μ] (b : ℝ)
    {c d h k : X × Velocity → ℝ}
    (hcd : c =ᵐ[μ.prod volume] d) (hhk : h =ᵐ[μ.prod volume] k) :
    mixedGainDensity b c h =ᵐ[μ.prod volume] mixedGainDensity b d k := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hcl := ae_ae_of_ae_prod ((KineticCollisionNullSets.left_quasiMeasurePreserving μ).ae hcd)
  have hcr := ae_ae_of_ae_prod ((KineticCollisionNullSets.right_quasiMeasurePreserving μ).ae hcd)
  have hhl := ae_ae_of_ae_prod ((KineticCollisionNullSets.left_quasiMeasurePreserving μ).ae hhk)
  have hhr := ae_ae_of_ae_prod ((KineticCollisionNullSets.right_quasiMeasurePreserving μ).ae hhk)
  filter_upwards [hcl,hcr,hhl,hhr] with z hcl hcr hhl hhr
  have h₁ : (∫ p : Velocity × Sphere, mixedPostRate b c h (collisionGrouping.symm (z,p))
      ∂(volume : Measure Velocity).prod sphereArea) =
      ∫ p : Velocity × Sphere, mixedPostRate b d k (collisionGrouping.symm (z,p))
        ∂(volume : Measure Velocity).prod sphereArea := by
    apply integral_congr_ae
    filter_upwards [hcl,hhr] with p hp hq
    rw [mixedPostRate_formula,mixedPostRate_formula]
    change CollisionCutoff.kernel b z.2 p.1 p.2*c (z.1,scatterLeft z.2 p.1 p.2)*
      h (z.1,scatterRight z.2 p.1 p.2) = _
    change c (z.1,scatterLeft z.2 p.1 p.2) = d (z.1,scatterLeft z.2 p.1 p.2) at hp
    change h (z.1,scatterRight z.2 p.1 p.2) = k (z.1,scatterRight z.2 p.1 p.2) at hq
    rw [hp,hq]
    rfl
  have h₂ : (∫ p : Velocity × Sphere, mixedPostRate b h c (collisionGrouping.symm (z,p))
      ∂(volume : Measure Velocity).prod sphereArea) =
      ∫ p : Velocity × Sphere, mixedPostRate b k d (collisionGrouping.symm (z,p))
        ∂(volume : Measure Velocity).prod sphereArea := by
    apply integral_congr_ae
    filter_upwards [hhl,hcr] with p hp hq
    rw [mixedPostRate_formula,mixedPostRate_formula]
    change CollisionCutoff.kernel b z.2 p.1 p.2*h (z.1,scatterLeft z.2 p.1 p.2)*
      c (z.1,scatterRight z.2 p.1 p.2) = _
    change h (z.1,scatterLeft z.2 p.1 p.2) = k (z.1,scatterLeft z.2 p.1 p.2) at hp
    change c (z.1,scatterRight z.2 p.1 p.2) = d (z.1,scatterRight z.2 p.1 p.2) at hq
    rw [hp,hq]
    rfl
  simp only [mixedGainDensity,h₁,h₂]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Pointwise domination supplies every mixed gain fibre integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem mixedPostRate_nonneg (b : ℝ) {c h : X × Velocity → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ mixedPostRate b c h z :=
  mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (hc _)) (hh _)

omit [MeasurableSpace X] in
theorem mixedPostRate_le_self (b : ℝ) {c h f : X × Velocity → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (hcf : ∀ p, c p ≤ f p) (hhf : ∀ p, h p ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b c h z ≤ mixedPostRate b f f z := by
  unfold mixedPostRate mixedPreRate
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hcf _) (CollisionCutoff.kernel_nonneg _ _ _ _))
    (hhf _) (hh _) (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) ((hc _).trans (hcf _)))

theorem mixedPostRate_fiber_integrable {b : ℝ} {c h f : X × Velocity → ℝ}
    (hcm : Measurable c) (hhm : Measurable h)
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (hcf : ∀ p, c p ≤ f p) (hhf : ∀ p, h p ≤ f p)
    (p : X × Velocity)
    (hi : Integrable (fun q : Velocity × Sphere =>
      mixedPostRate b f f (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (fun q : Velocity × Sphere =>
      mixedPostRate b c h (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea) := by
  apply hi.mono'
  · exact (((mixedPreRate_measurable hcm hhm b).comp scatterTripleEquiv.measurable).comp
      (collisionGrouping.symm.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · filter_upwards [] with w
    rw [Real.norm_of_nonneg (mixedPostRate_nonneg b hc hh _)]
    exact mixedPostRate_le_self b hc hh hcf hhf _

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The actual cutoff mixed gain is dominated by the nonnegative full gain -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixedGainDensity_le_nonnegative (b : ℝ) {c h : X × Velocity → ℝ}
    (hcm : Measurable c) (hhm : Measurable h)
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p) (z : X × Velocity) :
    ENNReal.ofReal (mixedGainDensity b c h z) ≤
      nonnegativeGain (fun v => ENNReal.ofReal (c (z.1,v)))
        (fun v => ENNReal.ofReal (h (z.1,v))) z.2 := by
  let A : Velocity × Sphere → ℝ := fun q => mixedPostRate b c h (collisionGrouping.symm (z,q))
  let B : Velocity × Sphere → ℝ := fun q => mixedPostRate b h c (collisionGrouping.symm (z,q))
  have hA : ∀ p, 0 ≤ A p := fun p => mixedPostRate_nonneg b hc hh _
  have hB : ∀ p, 0 ≤ B p := fun p => mixedPostRate_nonneg b hh hc _
  have hAm : Measurable A := ((mixedPreRate_measurable hcm hhm b).comp
    scatterTripleEquiv.measurable).comp
      (collisionGrouping.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hAi : ENNReal.ofReal (∫ p, A p ∂gainPairMeasure) ≤ ∫⁻ p, ENNReal.ofReal (A p) ∂gainPairMeasure := by
    simpa only [Real.enorm_eq_ofReal (integral_nonneg hA),Real.enorm_eq_ofReal (hA _)] using
      (enorm_integral_le_lintegral_enorm A (μ := gainPairMeasure))
  have hBi : ENNReal.ofReal (∫ p, B p ∂gainPairMeasure) ≤ ∫⁻ p, ENNReal.ofReal (B p) ∂gainPairMeasure := by
    simpa only [Real.enorm_eq_ofReal (integral_nonneg hB),Real.enorm_eq_ofReal (hB _)] using
      (enorm_integral_le_lintegral_enorm B (μ := gainPairMeasure))
  change ENNReal.ofReal ((1/2:ℝ)*((∫ p, A p ∂gainPairMeasure)+(∫ p, B p ∂gainPairMeasure))) ≤ _
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.ofReal_add (integral_nonneg hA) (integral_nonneg hB)]
  apply (mul_le_mul' le_rfl (add_le_add hAi hBi)).trans
  rw [← lintegral_add_left hAm.ennreal_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    MixedRealGain.nonnegative_eq_lintegral (fun p => hc (z.1,p)) (fun p => hh (z.1,p))]
  apply lintegral_mono
  intro p
  dsimp only
  rw [← ENNReal.ofReal_add (hA p) (hB p),← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  apply ENNReal.ofReal_le_ofReal
  have heA : A p = CollisionCutoff.kernel b z.2 p.1 p.2*
      c (z.1,scatterLeft z.2 p.1 p.2)*h (z.1,scatterRight z.2 p.1 p.2) :=
    mixedPostRate_formula b c h _
  have heB : B p = CollisionCutoff.kernel b z.2 p.1 p.2*
      h (z.1,scatterLeft z.2 p.1 p.2)*c (z.1,scatterRight z.2 p.1 p.2) :=
    mixedPostRate_formula b h c _
  rw [heA,heB]
  have hprod : 0 ≤ c (z.1,scatterLeft z.2 p.1 p.2)*h (z.1,scatterRight z.2 p.1 p.2)+
      h (z.1,scatterLeft z.2 p.1 p.2)*c (z.1,scatterRight z.2 p.1 p.2) :=
    add_nonneg (mul_nonneg (hc _) (hh _)) (mul_nonneg (hh _) (hc _))
  have hk := mul_le_mul_of_nonneg_right (CollisionCutoff.kernel_le b z.2 p.1 p.2) hprod
  unfold MixedRealGain.integrand
  nlinarith only [hk]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The Gaussian product moment implies physical mixed-rate integrability -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixed_pair_rate_integrable_of_gaussian {μ : Measure X}
    {c h : X × Velocity → ℝ} (hc : Measurable c) (hh : Measurable h)
    (hcn : ∀ p, 0 ≤ c p) (hhn : ∀ p, 0 ≤ h p)
    (hm : (∫⁻ p, ENNReal.ofReal (weight p.2.1*weight p.2.2)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).withDensity
        (fun p => ENNReal.ofReal (c (p.1,p.2.1)*h (p.1,p.2.2)))) < ⊤) :
    Integrable (fun p : X × (Velocity × Velocity) =>
      (1+‖p.2.1‖+‖p.2.2‖)*c (p.1,p.2.1)*h (p.1,p.2.2)) (μ.prod volume) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).withDensity
    (fun p => ENNReal.ofReal (c (p.1,p.2.1)*h (p.1,p.2.2)))
  have hw : Integrable (fun p : X × (Velocity × Velocity) => weight p.2.1*weight p.2.2) ν := by
    refine ⟨by unfold weight; fun_prop,?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ =>
      mul_nonneg (weight_pos _).le (weight_pos _).le))).mpr hm
  have hr : Integrable (fun p : X × (Velocity × Velocity) => 1+‖p.2.1‖+‖p.2.2‖) ν := by
    apply (hw.const_mul 3).mono' (by fun_prop)
    exact ae_of_all _ (fun p => by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1+‖p.2.1‖+‖p.2.2‖)]
      simpa only [mul_assoc] using pair_weight_le p.2.1 p.2.2)
  have hd : Measurable (fun p : X × (Velocity × Velocity) =>
      ENNReal.ofReal (c (p.1,p.2.1)*h (p.1,p.2.2))) :=
    ((hc.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hh.comp (measurable_fst.prodMk measurable_snd.snd))).ennreal_ofReal
  have ht := (integrable_withDensity_iff_integrable_smul' hd
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hr
  apply ht.congr
  exact ae_of_all _ (fun p => by
    dsimp only
    rw [ENNReal.toReal_ofReal (mul_nonneg (hcn _) (hhn _)),smul_eq_mul]
    ring)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Bounded tests of both physical mixed collision terms are integrable -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixed_gain_test_integrable {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h ψ : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ p, |ψ p| ≤ B) :
    Integrable (fun p => ψ p*mixedGainDensity b c h p) (μ.prod volume) := by
  have h₁ := (collision_test_marginal (mixedPostRate b c h) ψ
    (mixedPostRate_test_integrable hi hψ hB)).1
  have h₂ := (collision_test_marginal (mixedPostRate b h c) ψ
    (mixedPostRate_test_integrable (mixedPreRate_swapped_integrable hi) hψ hB)).1
  apply ((h₁.add h₂).const_mul (1/2 : ℝ)).congr
  exact ae_of_all _ (fun p => by dsimp only [Pi.add_apply,mixedGainDensity]; ring)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Finite positive measures of the actual cutoff mixed gain and loss -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixedGainDensity_nonneg (b : ℝ) {c h : X × Velocity → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p) (p : X × Velocity) :
    0 ≤ mixedGainDensity b c h p := by
  unfold mixedGainDensity
  exact mul_nonneg (by norm_num) (add_nonneg
    (integral_nonneg (fun q => mixedPostRate_nonneg b hc hh _))
    (integral_nonneg (fun q => mixedPostRate_nonneg b hh hc _)))

omit [MeasurableSpace X] in
theorem mixedLossDensity_nonneg (b : ℝ) {c h : X × Velocity → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p) (p : X × Velocity) :
    0 ≤ mixedLossDensity b c h p := by
  exact integral_nonneg (fun q => mul_nonneg
    (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (hh _)) (hc _))

def mixedGainMeasure (μ : Measure X) (b : ℝ) (c h : X × Velocity → ℝ) :
    Measure (X × Velocity) := positiveDensityMeasure (μ.prod volume) (mixedGainDensity b c h)

def mixedLossMeasure (μ : Measure X) (b : ℝ) (c h : X × Velocity → ℝ) :
    Measure (X × Velocity) := positiveDensityMeasure (μ.prod volume) (mixedLossDensity b c h)

theorem mixedGainDensity_integrable {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (mixedGainDensity b c h) (μ.prod volume) := by
  simpa only [one_mul] using mixed_gain_test_integrable hi
    (ψ := fun _ => 1) measurable_const (B := 1) (fun _ => by norm_num)

theorem mixedLossDensity_integrable {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ}
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (mixedLossDensity b c h) (μ.prod volume) := by
  have hl : Integrable (fun p => h p*KineticCollisionNullSets.frequency b c p) (μ.prod volume) := by
    simpa only [one_mul] using mixed_loss_test_integrable hi
      (ψ := fun _ => 1) measurable_const (B := 1) (fun _ => by norm_num)
  exact hl.congr (mixed_loss_ae_eq_frequency hi).symm

theorem mixedGainMeasure_finite {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ} (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    IsFiniteMeasure (mixedGainMeasure μ b c h) :=
  positiveDensityMeasure_finite (mixedGainDensity_integrable hi)
    (ae_of_all _ (mixedGainDensity_nonneg b hc hh))

theorem mixedLossMeasure_finite {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ} (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    IsFiniteMeasure (mixedLossMeasure μ b c h) :=
  positiveDensityMeasure_finite (mixedLossDensity_integrable hi)
    (ae_of_all _ (mixedLossDensity_nonneg b hc hh))

theorem mixedGainMeasure_integral {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ} (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) (ψ : X × Velocity → ℝ) :
    (∫ p, ψ p ∂mixedGainMeasure μ b c h) = ∫ p, ψ p*mixedGainDensity b c h p ∂μ.prod volume :=
  positiveDensityMeasure_integral (mixedGainDensity_integrable hi).aestronglyMeasurable.aemeasurable
    (ae_of_all _ (mixedGainDensity_nonneg b hc hh)) ψ

theorem mixedLossMeasure_integral {μ : Measure X} [SFinite μ] {b : ℝ}
    {c h : X × Velocity → ℝ} (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (hi : Integrable (mixedPreRate b c h)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) (ψ : X × Velocity → ℝ) :
    (∫ p, ψ p ∂mixedLossMeasure μ b c h) = ∫ p, ψ p*mixedLossDensity b c h p ∂μ.prod volume :=
  positiveDensityMeasure_integral (mixedLossDensity_integrable hi).aestronglyMeasurable.aemeasurable
    (ae_of_all _ (mixedLossDensity_nonneg b hc hh)) ψ

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
