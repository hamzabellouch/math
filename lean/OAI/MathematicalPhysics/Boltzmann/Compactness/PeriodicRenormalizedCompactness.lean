import OAI.MathematicalPhysics.Boltzmann.Branching.RationalUniformApproximation
import OAI.MathematicalPhysics.Boltzmann.Branching.SpacetimeRelativeEntropy
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicFiniteMild
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicInitialEntropyLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMomentEntropy
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableGainTail
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakLinearMomentLimit

namespace OAI

section

/-! # Weak L1 extraction for the actual global approximation sequence -/
noncomputable section
open MeasureTheory Filter
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.kinetic_entropy_integrable
    (S : BoundedCutoffSolution N T f₀) (hN : 0 ≤ N)
    {μ : Measure ℝ} [IsFiniteMeasure μ] {C : ℝ}
    (hb : ∀ t, (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ C) :
    Integrable (entropyGauge S.kineticProfile) ((μ.prod (volume : Measure Position)).prod volume) := by
  have hi := spacetimeEntropy_integrable (μ := μ) S.measurable S.nonnegative
    (fun t => (S.finiteEntropy hN t).2.2) hb
  have hr := (kineticGrouping_measurePreserving μ).integrable_comp_of_integrable hi
  exact hr

theorem BoundedCutoffSolution.kinetic_entropy_integral_le
    (S : BoundedCutoffSolution N T f₀) (hN : 0 ≤ N)
    {μ : Measure ℝ} [IsFiniteMeasure μ] {C : ℝ}
    (hb : ∀ t, (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ C) :
    (∫ p, entropyGauge S.kineticProfile p ∂(μ.prod (volume : Measure Position)).prod volume) ≤ μ.real Set.univ*C := by
  have h := spacetimeEntropy_integral_le (μ := μ) S.measurable S.nonnegative
    (fun t => (S.finiteEntropy hN t).2.2) hb
  have he := (kineticGrouping_measurePreserving μ).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding (spacetimeEntropy S.density)
  rw [← he] at h
  exact h

theorem approximatingSolution_compactness_hypotheses (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    UniformIntegrable (fun n => (approximatingSolution f hfm n).kineticProfile) 1
      ((μ.prod (volume : Measure Position)).prod volume) ∧
    UnifTight (fun n => (approximatingSolution f hfm n).kineticProfile) 1
      ((μ.prod (volume : Measure Position)).prod volume) := by
  have hm := fun n => (approximatingSolution f hfm n).kineticProfile_measurable
  have hn : ∀ (n : ℕ) (p : (ℝ × Position) × Velocity),
      0 ≤ (approximatingSolution f hfm n).kineticProfile p :=
    fun n p => (approximatingSolution f hfm n).nonnegative (p.1.1,(p.1.2,p.2))
  have hg := fun n => (approximatingSolution f hfm n).kinetic_entropy_integrable
    (μ := μ) (by positivity) (approximatingSolution_entropy f hfm hf hi n)
  have hb := fun n => (approximatingSolution f hfm n).kinetic_entropy_integral_le
    (μ := μ) (by positivity) (approximatingSolution_entropy f hfm hf hi n)
  exact ⟨uniformIntegrable_of_entropyGauge hm hn hg hb,unifTight_of_entropyGauge hm hn hg hb⟩

theorem exists_weak_approximation_limit (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (T : ℝ) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges
        (((volume.restrict (Set.Icc 0 T)).prod (volume : Measure Position)).prod volume)
        (fun n => (approximatingSolution f hfm (φ n)).kineticProfile) g := by
  have h := approximatingSolution_compactness_hypotheses f hfm hf hi (volume.restrict (Set.Icc 0 T))
  exact Published.l1WeakCompactnessInput _ _
    (fun n => (approximatingSolution f hfm n).kineticProfile_measurable) h.1 h.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual symmetric cutoff loss has a uniform normalized L1 bound -/
noncomputable section
open MeasureTheory Set Filter
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem windowKernel_le_physical (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    windowKernel N z ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 := by
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem hz]
  · rw [windowKernel,indicator_of_notMem hz]
    exact collisionKernel_nonneg _ _ _

omit [MeasurableSpace X] in
theorem regularizedPreRate_le_physical {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) : regularizedPreRate N f z ≤ preRate f z := by
  have hm := rateMultiplier_bounds hN hf z
  have hw := windowKernel_bounds hN.le z
  have hk : windowKernel N z*rateMultiplier N f z ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 :=
    (mul_le_mul_of_nonneg_left hm.2 hw.1).trans (by simpa using windowKernel_le_physical N z)
  rw [regularizedPreRate_factor]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (hf _)) (hf _)

theorem loss_le_physical {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity)
    (h0 : Integrable (fun v => f (p.1,v))) (h1 : Integrable (fun v => ‖v‖*f (p.1,v))) :
    loss N f p ≤ lossDensity f p := by
  have hp : Integrable (fun q : Velocity × Sphere => preRate f (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea) :=
    integrable_loss_of_moments (fun z : Phase => f (p.1,z.2)) 0 p.2 h0 h1
  have hle : fiberMeasure N ≤ (volume : Measure Velocity).prod sphereArea := by
    rw [fiberMeasure_eq_restrict]
    exact Measure.restrict_le_self
  calc
    loss N f p ≤ ∫ q, preRate f (collisionGrouping.symm (p,q)) ∂fiberMeasure N :=
      integral_mono (pre_fiber_integrable hN hfm hf p) (hp.mono_measure hle)
        (fun q => regularizedPreRate_le_physical hN hf _)
    _ ≤ lossDensity f p := integral_mono_measure hle (ae_of_all _ (fun q => preRate_nonneg hf _)) hp

theorem normalizedLoss_uniformIntegrable {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hN : ∀ n, 0 < N n) (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n p => loss (N n) (f n) p/(1+f n p/maxwellian p.2)) 1 (μ.prod volume) := by
  have hui := renormalized_loss_uniformIntegrable hfm hf hi hb
  have hM : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  apply uniformIntegrable_mono_nonneg hui
    (fun n => ((loss_measurable (N n) (hfm n)).div
      (measurable_const.add ((hfm n).div hM))).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun p => div_nonneg (loss_bounds (hN n) (hfm n) (hf n) p).1
      (le_of_lt (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hf n p) (maxwellian_pos p.2).le)))))
  intro n
  have hfi := integrable_of_entropyGauge (hfm n) (hf n) (hi n)
  have hli := linearMoment_integrable (hfm n) (hf n) (hi n)
  have hvi : Integrable (fun p => ‖p.2‖*f n p) (μ.prod volume) := by
    convert hli.sub hfi using 1
    funext p
    dsimp only [linearMoment,Pi.sub_apply]
    ring
  have h0 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hfi.prod_right_ae
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure Velocity))).ae hvi.prod_right_ae
  filter_upwards [h0,h1] with p hp0 hp1
  exact div_le_div_of_nonneg_right (loss_le_physical (hN n) (hfm n) (hf n) p hp0 hp1)
    (le_of_lt (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hf n p) (maxwellian_pos p.2).le)))

theorem approximatingSolution_normalizedLoss_uniformIntegrable (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    UniformIntegrable (fun (n : ℕ) p => loss ((n:ℝ)+1) (approximatingSolution f hfm n).kineticProfile p /
      (1+(approximatingSolution f hfm n).kineticProfile p/maxwellian p.2)) 1
        ((μ.prod (volume : Measure Position)).prod volume) := by
  exact normalizedLoss_uniformIntegrable (N := fun n : ℕ => (n:ℝ)+1) (fun n => by positivity)
    (fun n => (approximatingSolution f hfm n).kineticProfile_measurable)
    (fun n p => (approximatingSolution f hfm n).nonnegative (p.1.1,(p.1.2,p.2)))
    (fun n => (approximatingSolution f hfm n).kinetic_entropy_integrable (by positivity)
      (approximatingSolution_entropy f hfm hf hi n))
    (fun n => (approximatingSolution f hfm n).kinetic_entropy_integral_le (by positivity)
      (approximatingSolution_entropy f hfm hf hi n))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform normalized gain from entropy, moments, and actual dissipation -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem normalizedGain_uniformIntegrable {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ}
    {C : ℝ} {B : ℝ≥0∞} (hN : ∀ n, 0 < N n) (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n p, 0 ≤ f n p) (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hB : B < ⊤) (hD : ∀ n, extendedDissipation μ (N n) (f n) ≤ B) :
    UniformIntegrable (fun n p => gain (N n) (f n) p/normalizer (f n) p) 1 (μ.prod volume) := by
  apply Compactness.uniformIntegrable_of_logarithmic_tail
    (L := fun n p => loss (N n) (f n) p/normalizer (f n) p) (B := 4*B)
  · exact fun n => (gain_measurable (N n) (hfm n)).div (normalizer_measurable (hfm n))
  · exact fun n => (loss_measurable (N n) (hfm n)).div (normalizer_measurable (hfm n))
  · exact fun n p => div_nonneg (gain_bounds (hN n) (hfm n) (hf n) p).1 (normalizer_pos (hf n) p).le
  · exact fun n p => div_nonneg (loss_bounds (hN n) (hfm n) (hf n) p).1 (normalizer_pos (hf n) p).le
  · exact normalizedLoss_uniformIntegrable hN hfm hf hi hb
  · exact ENNReal.mul_lt_top (by norm_num) hB
  · intro R hR n
    exact (normalizedGainExcess_integral_bound (hN n) hR (hfm n) (hf n)).trans
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl (hD n)))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform relative entropy of the concrete global approximation sequence -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem BoundedCutoffSolution.relativeEntropy_all_times {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) (hT : 0 ≤ T) (t : ℝ) :
    relativeEntropy (fun p => S.density (t,p)) ≤ relativeEntropy f₀ := by
  have he : (fun p => S.density (t,p)) = (fun p => S.density (PositiveIntegral.time T t,p)) :=
    funext (S.density_clipped hT t)
  rw [he]
  exact S.relativeEntropy_le hN hT (PositiveIntegral.time_bounds hT t)

theorem approximatingSolution_relativeEntropy (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ) (t : ℝ) :
    relativeEntropy (fun p => (approximatingSolution f hfm n).density (t,p)) ≤
      initialEntropyBudget f := by
  exact ((approximatingSolution f hfm n).relativeEntropy_all_times (by positivity) (by positivity) t).trans
    (initialApproximation_relativeEntropy_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hfm hf hi)

theorem approximatingSolution_spacetimeEntropy_integrable (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (spacetimeEntropy (approximatingSolution f hfm n).density) (μ.prod volume) :=
  spacetimeEntropy_integrable (approximatingSolution f hfm n).measurable
    (approximatingSolution f hfm n).nonnegative
    (fun t => ((approximatingSolution f hfm n).finiteEntropy (by positivity) t).2.2)
    (approximatingSolution_entropy f hfm hf hi n)

theorem approximatingSolution_spacetimeRelativeEntropy (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (spacetimeRelativeEntropy (approximatingSolution f hfm n).density) (μ.prod volume) ∧
      (∫ z, spacetimeRelativeEntropy (approximatingSolution f hfm n).density z ∂μ.prod volume) ≤
        μ.real univ*initialEntropyBudget f := by
  have hE := relativeEntropy_integrable_of_spacetimeEntropy
    (approximatingSolution f hfm n).measurable (approximatingSolution f hfm n).nonnegative
    (approximatingSolution_spacetimeEntropy_integrable f hfm hf hi n μ)
  exact ⟨hE,spacetimeRelativeEntropy_integral_le hE (approximatingSolution_relativeEntropy f hfm hf hi n)⟩

theorem initialEntropyBudget_nonneg (f : Density) (hf : ∀ p, 0 ≤ f p) :
    0 ≤ initialEntropyBudget f := by
  apply add_nonneg
  · exact mul_nonneg initialEntropyCoefficient_nonneg
      (integral_nonneg (fun p => mul_nonneg (hf p) (by positivity)))
  · exact integral_nonneg (fun p => (maxwellian_pos p.2).le)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform integrability of both normalized sources of actual periodic solutions -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_dissipation_bound (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hTN : T ≤ (n:ℝ)+1) :
    extendedDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) ((n:ℝ)+1)
      (approximatingSolution f hfm n).kineticProfile ≤ ENNReal.ofReal (initialEntropyBudget f) := by
  have hd := (approximatingSolution f hfm n).extended_dissipation_le (by positivity) (by positivity) ⟨hT,hTN⟩
  apply hd.trans (ENNReal.ofReal_le_ofReal ?_)
  have hN : 1 ≤ (n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hIni := initialApproximation_relativeEntropy_le hN hfm hf hi
  change relativeEntropy (initialApproximation ((n:ℝ)+1) f) ≤ initialEntropyBudget f at hIni
  have hEnd := relativeEntropy_nonneg ((approximatingSolution f hfm n).finiteEntropy (by positivity) T)
  have he0 : (∫ p, scalarRelativeEntropy (maxwellian p.2) (initialApproximation ((n:ℝ)+1) f p)) =
      relativeEntropy (initialApproximation ((n:ℝ)+1) f) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  have he1 : (∫ p, scalarRelativeEntropy (maxwellian p.2) ((approximatingSolution f hfm n).density (T,p))) =
      relativeEntropy (fun p => (approximatingSolution f hfm n).density (T,p)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  rw [he0,he1]
  linarith

theorem approximatingSolution_normalizedSources_uniformIntegrable (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T) :
    let F := fun n => (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile
    let N := fun n : ℕ => ((n+Nat.ceil T:ℕ):ℝ)+1
    let μ := (volume.restrict (Icc 0 T)).prod (volume : Measure Position)
    UniformIntegrable (fun n p => gain (N n) (F n) p/normalizer (F n) p) 1 (μ.prod volume) ∧
      UniformIntegrable (fun n p => loss (N n) (F n) p/normalizer (F n) p) 1 (μ.prod volume) := by
  dsimp only
  have hN (n : ℕ) : 0 < ((n+Nat.ceil T:ℕ):ℝ)+1 := by positivity
  have hm (n : ℕ) := (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile_measurable
  have hn (n : ℕ) (p : (ℝ × Position) × Velocity) :
      0 ≤ (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile p :=
    (approximatingSolution f hfm (n+Nat.ceil T)).nonnegative _
  have hE (n : ℕ) := (approximatingSolution f hfm (n+Nat.ceil T)).kinetic_entropy_integrable
    (μ := volume.restrict (Icc 0 T)) (hN n).le (approximatingSolution_entropy f hfm hf hi (n+Nat.ceil T))
  have hC (n : ℕ) := (approximatingSolution f hfm (n+Nat.ceil T)).kinetic_entropy_integral_le
    (μ := volume.restrict (Icc 0 T)) (hN n).le (approximatingSolution_entropy f hfm hf hi (n+Nat.ceil T))
  refine ⟨normalizedGain_uniformIntegrable (B := ENNReal.ofReal (initialEntropyBudget f)) hN hm hn hE hC ENNReal.ofReal_lt_top ?_,
    normalizedLoss_uniformIntegrable hN hm hn hE hC⟩
  intro n
  apply approximatingSolution_dissipation_bound f hfm hf hi hT
  have hc := Nat.le_ceil T
  have hn0 := Nat.cast_nonneg (α := ℝ) n
  push_cast
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual finite approximations retain entropy and all earlier dissipation -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem extendedDissipation_mono_measure {μ ν : Measure X} (h : μ ≤ ν)
    (N : ℝ) (f : X × Velocity → ℝ) : extendedDissipation μ N f ≤ extendedDissipation ν N f := by
  unfold extendedDissipation
  apply mul_le_mul' le_rfl
  exact lintegral_mono' (Measure.prod_mono (Measure.prod_mono h le_rfl) le_rfl) le_rfl

theorem BoundedCutoffSolution.earlier_joint_budget {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) (hT : 0 ≤ T)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    ENNReal.ofReal (relativeEntropy (fun p => S.density (t,p)))+
      extendedDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position)) N S.kineticProfile ≤
        ENNReal.ofReal (relativeEntropy f₀) := by
  have htt : t ∈ Icc 0 T := ⟨hr.trans hrt,ht⟩
  have hH := S.relativeEntropy_le hN hT htt
  have hHn := relativeEntropy_nonneg (S.finiteEntropy hN.le t)
  have hd := S.extended_dissipation_le hN hT htt
  have he (u : Density) : (∫ p, scalarRelativeEntropy (maxwellian p.2) (u p)) = relativeEntropy u := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  rw [he,he] at hd
  have hm := extendedDissipation_mono_measure
    (μ := (volume.restrict (Icc 0 r)).prod (volume : Measure Position))
    (ν := (volume.restrict (Icc 0 t)).prod (volume : Measure Position))
    (Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hrt) le_rfl) le_rfl)
    N S.kineticProfile
  apply (add_le_add le_rfl (hm.trans hd)).trans_eq
  rw [← ENNReal.ofReal_add hHn (sub_nonneg.mpr hH)]
  congr 1
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Renormalized compactness bounds for the actual periodic sequence -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_renormalizedSources_uniformIntegrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) :
    let F := fun n => (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile
    let N := fun n : ℕ => ((n+Nat.ceil T:ℕ):ℝ)+1
    let μ := ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume
    UniformIntegrable (fun n p => derivWithin β.toFun (Ici 0) (F n p/maxwellian p.2)*
      gain (N n) (F n) p) 1 μ ∧
    UniformIntegrable (fun n p => derivWithin β.toFun (Ici 0) (F n p/maxwellian p.2)*
      loss (N n) (F n) p) 1 μ ∧
    UniformIntegrable (fun n p => derivWithin β.toFun (Ici 0) (F n p/maxwellian p.2)*
      collisionOperator (N n) (F n) p) 1 μ := by
  dsimp only
  obtain ⟨hg,hl⟩ := approximatingSolution_normalizedSources_uniformIntegrable f hfm hf hi hT
  have hm n := (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile_measurable
  have hn n p : 0 ≤ (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile p :=
    (approximatingSolution f hfm (n+Nat.ceil T)).nonnegative _
  have hM : Measurable (fun p : (ℝ × Position) × Velocity => maxwellian p.2) := by
    unfold maxwellian
    fun_prop
  have hG := β.derivative_uniformIntegrable hm hM hn (fun p => maxwellian_pos p.2) hg
  have hL := β.derivative_uniformIntegrable hm hM hn (fun p => maxwellian_pos p.2) hl
  refine ⟨hG,hL,?_⟩
  have hs := Compactness.uniformIntegrable_sub hG hL
  simpa only [collisionOperator,mul_sub] using hs

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform rational approximation of the actual periodic solutions -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_rational_uniform_L1 (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Tendsto (fun k : ℕ => ⨆ n : ℕ, eLpNorm (fun p =>
      (approximatingSolution f hfm n).kineticProfile p-
      rationalApproximation ((k:ℝ)+1) (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
        (approximatingSolution f hfm n).kineticProfile p)
      1 ((μ.prod (volume : Measure Position)).prod volume)) atTop (𝓝 0) := by
  apply rationalApproximation_uniform_L1
    (fun n => (approximatingSolution f hfm n).kineticProfile_measurable)
    (fun n p => (approximatingSolution f hfm n).nonnegative _)
    (fun n => (approximatingSolution f hfm n).kinetic_entropy_integrable (by positivity)
      (approximatingSolution_entropy f hfm hf hi n))
  exact fun n => (approximatingSolution f hfm n).kinetic_entropy_integral_le (by positivity)
    (approximatingSolution_entropy f hfm hf hi n)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform integrability of the actual renormalized densities -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_renormalizedDensity_uniformIntegrable
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {T : ℝ} (β : Renormalization) :
    UniformIntegrable (fun n p => maxwellian p.2*β.toFun
      ((approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile p/maxwellian p.2)) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) := by
  obtain ⟨hu,C,hC⟩ := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1
  have htail : UniformIntegrable (fun n => (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) :=
    ⟨hu.comp (fun n => n+Nat.ceil T),C,fun n => hC (n+Nat.ceil T)⟩
  exact β.weighted_uniformIntegrable
    (fun n => (approximatingSolution f hfm (n+Nat.ceil T)).kineticProfile_measurable)
    (by unfold maxwellian; fun_prop)
    (fun n p => (approximatingSolution f hfm (n+Nat.ceil T)).nonnegative _)
    (fun p => maxwellian_pos p.2) htail

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
