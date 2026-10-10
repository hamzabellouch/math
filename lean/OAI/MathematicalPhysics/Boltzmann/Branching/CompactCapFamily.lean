import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedTightness
import OAI.MathematicalPhysics.Boltzmann.Branching.AverageMajorant
import OAI.MathematicalPhysics.Boltzmann.Branching.AveragedPairIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources

namespace OAI

section

/-! # Strong local product convergence from pair uniform integrability -/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

open Published

theorem uniformIntegrable_compact_average_product {μ : Measure SpaceTime} [SFinite μ]
    {f : ℕ → KineticPhase → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable (fun (n : ℕ) (z : SpaceTime × (Velocity × Velocity)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod volume))
    {k l : KineticPhase → ℝ} (hk : Continuous k) (hl : Continuous l)
    (hkc : HasCompactSupport k) (hlc : HasCompactSupport l) :
    UniformIntegrable (fun n x => (∫ v, k (x,v)*f n (x,v))*
      (∫ w, l (x,w)*f n (x,w))) 1 μ := by
  obtain ⟨R,_hR,hball⟩ := ((hkc.union hlc).image continuous_snd).isBounded.subset_ball_lt
    0 (0 : Velocity)
  have hs (z : KineticPhase) (hz : z.2 ∉ Metric.closedBall (0 : Velocity) R) :
      k z = 0 ∧ l z = 0 := by
    have hn : z ∉ tsupport k ∪ tsupport l := by
      intro h
      have hb := hball (mem_image_of_mem Prod.snd h)
      exact hz (Metric.ball_subset_closedBall hb)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inr h))⟩
  obtain ⟨C,hC⟩ := hk.bounded_above_of_compact_support hkc
  obtain ⟨D,hD⟩ := hl.bounded_above_of_compact_support hlc
  let : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  apply uniformIntegrable_average_product_of_support (s := Metric.closedBall (0 : Velocity) R)
    hf (by simpa only [Measure.volume_eq_prod] using hui) hk.measurable hl.measurable
    (⟨max C 0,le_max_right _ _⟩ : ℝ≥0) (⟨max D 0,le_max_right _ _⟩ : ℝ≥0)
    (fun z => (hC z).trans (le_max_left _ _))
    (fun z => (hD z).trans (le_max_left _ _))
  · exact fun x v hv => (hs (x,v) hv).1
  · exact fun x v hv => (hs (x,v) hv).2

theorem local_average_product_convergence {T : ℝ} {μ : Measure SpaceTime}
    [SFinite μ] (hμ : μ ≤ timeSpaceVolume T)
    {f : ℕ → KineticPhase → ℝ} (hf : ∀ n, Measurable (f n))
    (hui : UniformIntegrable (fun (n : ℕ) (z : SpaceTime × (Velocity × Velocity)) =>
      f n (z.1,z.2.1)*f n (z.1,z.2.2)) 1 (μ.prod volume))
    {k l : KineticPhase → ℝ} (hk : Continuous k) (hl : Continuous l)
    (hkc : HasCompactSupport k) (hlc : HasCompactSupport l)
    {A B : SpaceTime → ℝ}
    (hA : TimeLocalL1Converges T (fun n x => ∫ v, k (x,v)*f n (x,v)) A)
    (hB : TimeLocalL1Converges T (fun n x => ∫ v, l (x,v)*f n (x,v)) B)
    (K : Set SpaceTime) (hK : IsCompact K) [IsFiniteMeasure (μ.restrict K)] :
    Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, k (x,v)*f n (x,v))*(∫ w, l (x,w)*f n (x,w))-A x*B x) 1 (μ.restrict K))
      atTop (𝓝 0) := by
  have hprod := uniformIntegrable_restrict
    (uniformIntegrable_compact_average_product hf hui hk hl hkc hlc) K
  have hmono := Measure.restrict_mono_measure hμ K
  apply tendsto_L1_product
    (fun n => ((hk.measurable.mul (hf n)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
    (fun n => ((hl.measurable.mul (hf n)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
    ?_ ?_ hprod
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hA.2 K hK)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hmono)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hB.2 K hK)
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ hmono)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The constructed cap sequence and its compactness bounds

The actual positive cutoff solutions satisfy bounds sufficient for the
compactness and limit constructions.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

structure CompactCapFamily (s₀ η K α γ d₀ q : ℝ) where
  time : ℝ
  time_pos : 0 < time
  time_le : time ≤ 1/32
  approximation : ∀ N, CapApproximation s₀ η K α γ d₀ q time N
  density_ui : UniformIntegrable (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_ui : UniformIntegrable (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_ui : UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_ui : UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  initial_l1 : Tendsto (fun N => ∫ p,
    ‖periodicInitial s₀ η K α γ d₀ q N (approximation N).coefficient p-
      JetPeriodicDatum.datum s₀ η K α γ d₀ p‖) atTop (𝓝 0)

theorem CompactCapFamily.source_ui {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.collisionSource (N+1)
      (torusPhysical q (F.approximation N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume F.time).prod (volume : Measure Velocity)) :=
  CollisionCompactness.collisionSource_uniformIntegrable
    (fun N => torusPhysical_measurable (F.approximation N).solution.measurable_value q)
    (fun N => torusPhysical_nonneg (fun z => ((F.approximation N).solution.value_bounds z).1) q)
    F.pairs_ui (fun N => N+1) F.gain_ui F.loss_ui

theorem exists_compact_cap_family (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    Nonempty (CompactCapFamily s₀ η K α γ d₀ q) := by
  obtain ⟨T,hT,hTmax,F,hpair,hinit⟩ := exists_integrable_cap_family hcarleman
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  have hα₁ : α ≤ 1 := hαmax.trans (by norm_num)
  have hcut := cap_family_cutoff_uniformIntegrable hs₀ hsmax hη hηmax hK hα hα₁ hγ hd₀ hd₀max
    hsmall hq₂ hT.le hTmax F
  exact ⟨⟨T,hT,hTmax,F,
    cap_family_density_uniformIntegrable hs₀ hsmax hη hηmax hK hα hα₁ hγ hd₀ hd₀max
      hsmall hq₂ hT.le hTmax F,
    hpair,hcut.1,hcut.2,hinit⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
