import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildRenormalizedBalance
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalFrequencyWindow
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakCapOuterBound

namespace OAI

section

/-! # The actual cold datum has a nonnegative strong local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

/-- The local solution properties established before the entropy and continuation steps. -/
structure LocalMildSolution (T : ℝ) (f₀ : Density) (F : Evolution) : Prop where
  strong : StrongEarly T F
  measurable : Measurable (fun z : ℝ × Phase => F z.1 z.2)
  nonnegative : ∀ t p, 0 ≤ F t p
  initial : F 0 = f₀
  integrable_each_time : ∀ t, Integrable (F t)
  pair_integrable : Integrable (CollisionCompactness.pairDensity (kineticDensity F))
    ((AnnularEnvelope.timePositionVolume T).prod volume)
  characteristic : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => f₀ z.2 + Published.timePrimitive (volume.restrict (Icc 0 T))
      (fun w => collision (F w.1) (TorusFlight.flight w.1 w.2).1
        (TorusFlight.flight w.1 w.2).2) z)

theorem MildCollisionSolution.localMildSolution
    {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p) :
    LocalMildSolution T f₀ (MildCollisionSolution.positiveEvolution T f₀ g) where
  strong := S.positiveEvolution_strongEarly hT hf₀m hf₀i
  measurable := S.positiveEvolution_measurable hf₀m
  nonnegative := MildCollisionSolution.positiveEvolution_nonnegative
  initial := funext (MildCollisionSolution.positiveEvolution_initial hT.le hf₀n)
  integrable_each_time := S.positiveEvolution_integrable hf₀m hf₀i
  pair_integrable := S.positiveDensity_pair_integrable hf₀m
  characteristic := S.positiveEvolution_characteristic hf₀m

namespace JetCopyDatum

theorem exists_local_mild_solution
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    FiniteEntropyDatum (JetPeriodicDatum.datum s₀ η K α γ d₀) ∧
      BoundedVelocitySupport (JetPeriodicDatum.datum s₀ η K α γ d₀) ∧
      ∃ (T : ℝ) (F : Evolution), T ≤ 1/32 ∧
        LocalMildSolution T (JetPeriodicDatum.datum s₀ η K α γ d₀) F := by
  obtain ⟨A⟩ := exists_tight_cap_family hcarleman hs₀ hsmax hη hηmax hK.le hα hαmax hγ
    hd₀ hd₀max hwidth hsmall hq₁ hq₂
  obtain ⟨φ,g,_hφ,_hg,S⟩ := A.exists_mild_limit hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK.le hγ hd₀ hq₁ hq₂
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hi := JetPeriodicDatum.integrable_pullback
    (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ α)
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  exact ⟨JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax,
    JetPeriodicDatum.boundedVelocitySupport hs₀ hsmax hη.le hd₀ hwidth hα.le hαmax K γ,
    A.time,MildCollisionSolution.positiveEvolution A.time _ g,A.time_le,
    S.localMildSolution A.time_pos hm hi hn⟩

end JetCopyDatum
end BoltzmannNonuniqueness

end

end

section

/-! # Moment and annular bounds for the constructed strong local solution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveEvolution_moment (S : MildCollisionSolution T f₀ g) {M : ℝ × Position → ℝ}
    (hb : ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T,
      VelocityMoment.moment (fun v => g (u,v)) ≤ ENNReal.ofReal (M u)) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T,
      VelocityMoment.moment (fun v => positiveEvolution T f₀ g u.1 (u.2,v)) ≤ ENNReal.ofReal (M u) := by
  filter_upwards [Measure.ae_ae_of_ae_prod S.positiveDensity_eq_ae,hb] with u hu hb
  have he : VelocityMoment.moment (fun v => g (u,v)) =
      VelocityMoment.moment (fun v => positiveEvolution T f₀ g u.1 (u.2,v)) := by
    apply lintegral_congr_ae
    filter_upwards [hu] with v hv
    exact congrArg (fun a => ENNReal.ofReal (VelocityMoment.weight v*a)) hv
  rwa [← he]

theorem positiveEvolution_outer_bound (S : MildCollisionSolution T f₀ g)
    {s : Set (ℝ × Position)} {A q : ℝ}
    (hb : ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T, ∀ᵐ v : Velocity,
      u ∉ s → g (u,v) ≤ A*H q v) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T, ∀ᵐ v : Velocity,
      u ∉ s → positiveEvolution T f₀ g u.1 (u.2,v) ≤ A*H q v := by
  filter_upwards [Measure.ae_ae_of_ae_prod S.positiveDensity_eq_ae,hb] with u hu hb
  filter_upwards [hu,hb] with v hv hb
  change g (u,v) = positiveEvolution T f₀ g u.1 (u.2,v) at hv
  rwa [← hv]

end MildCollisionSolution

namespace JetCopyDatum

theorem TightCapFamily.exists_bounded_local_mild_solution
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ F : Evolution, LocalMildSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) F ∧
      (∀ t ∈ Icc 0 A.time, (∫ p, F t p) = ∫ p, JetPeriodicDatum.datum s₀ η K α γ d₀ p) ∧
      (∀ᵐ u ∂AnnularEnvelope.timePositionVolume A.time,
        VelocityMoment.moment (fun v => F u.1 (u.2,v)) ≤
          ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
            (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
            (AnnularEnvelope.torusChart u))) ∧
      (∀ J : ℕ, ∀ᵐ u ∂AnnularEnvelope.timePositionVolume A.time, ∀ᵐ v : Velocity,
        u ∉ AnnularEnvelope.torusTail s₀ η J → F u.1 (u.2,v) ≤
          (2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J)*H q v) := by
  obtain ⟨φ,g,_hφ,hg,S⟩ := A.exists_mild_limit hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hi := JetPeriodicDatum.integrable_pullback
    (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK hd₀.le η α γ _
  refine ⟨MildCollisionSolution.positiveEvolution A.time _ g,
    S.localMildSolution A.time_pos hm hi hn,fun t ht => S.mass_conservation A.time_pos hm hi ht,?_,?_⟩
  · exact S.positiveEvolution_moment (A.toCompactCapFamily.weak_limit_moment
      hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₂ hg S.nonnegative)
  · intro J
    exact S.positiveEvolution_outer_bound (A.toCompactCapFamily.weak_limit_outer_bound
      hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₂ hg J)

end JetCopyDatum
end BoltzmannNonuniqueness

end

end

section

/-! # Finite first moments give locally integrable physical frequencies -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem kineticFrequency_integrable_local {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (linearMoment f) (μ.prod volume))
    {R : ℝ} (hR : 0 ≤ R) :
    Integrable (kineticFrequency f)
      (μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))) := by
  let τ : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure τ := isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  have hm := (hi.integral_prod_left.comp_fst τ).const_mul (2*Real.pi*(R+1))
  apply hm.mono' (kineticFrequency_measurable hfm).aestronglyMeasurable
  have hx := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := τ)).ae hi.prod_right_ae
  have hv := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := τ)).ae
    (ae_restrict_mem Metric.isClosed_closedBall.measurableSet)
  filter_upwards [hx,hv] with p hpx hpv
  have hpR : ‖p.2‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hpv
  have hb w : ‖‖p.2-w‖*f (p.1,w)‖ ≤ (R+1)*linearMoment f (p.1,w) := by
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hf _))]
    apply le_trans (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (hf _))
    dsimp only [linearMoment]
    have hc : ‖p.2‖+‖w‖ ≤ (R+1)*(1+‖w‖) := by nlinarith [norm_nonneg w]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (hf (p.1,w))
  have hh := norm_integral_le_of_norm_le (hpx.const_mul (R+1)) (ae_of_all _ hb)
  rw [integral_const_mul] at hh
  rw [Real.norm_of_nonneg (kineticFrequency_nonneg hf p)]
  dsimp only [kineticFrequency]
  calc
    2*Real.pi*(∫ w, ‖p.2-w‖*f (p.1,w)) ≤
        2*Real.pi*‖∫ w, ‖p.2-w‖*f (p.1,w)‖ :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ 2*Real.pi*((R+1)*(∫ w, linearMoment f (p.1,w))) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Local admissibility and terminal traces for global continuation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

/-- Local admissibility retains endpoint terms for arbitrary tests. This permits pasting at
`T` without assuming that a test vanishes at the joining time. -/
structure AdmissibleLocal (T : ℝ) (f₀ : Density) (F : Evolution) : Prop
    extends LocalMildSolution T f₀ F where
  datum : FiniteEntropyDatum f₀
  finite_each_time : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (F t)
  uniform_moment : ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ z, entropyMoment (F t) z) ≤ C
  collision_fibers : ∀ᵐ p ∂volume.restrict (boundedTimes T),
    Integrable (fun q : Velocity × Sphere => collisionKernel p.2.2 q.1 q.2 *
      F p.1 (p.2.1,scatterLeft p.2.2 q.1 q.2)*F p.1 (p.2.1,scatterRight p.2.2 q.1 q.2))
      ((volume : Measure Velocity).prod sphereArea) ∧
    Integrable (fun q : Velocity × Sphere => collisionKernel p.2.2 q.1 q.2 *
      F p.1 p.2*F p.1 (p.2.1,q.1)) ((volume : Measure Velocity).prod sphereArea)
  renormalized_integrable : ∀ β φ, IntegrableOn (renormalizedIntegrand F β φ) (boundedTimes T)
  renormalized_balance : ∀ (β : Renormalization) (φ : KineticTest),
    (∫ z in boundedTimes T, renormalizedIntegrand F β φ z)+
      (∫ p, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) =
      ∫ p, maxwellian p.2*β.toFun (F T p/maxwellian p.2)*φ.toFun T p.1 p.2
  local_mass_integrable : ∀ φ : MassTest, IntegrableOn
    (fun z : ℝ × Phase => F z.1 z.2*φ.transportDerivative z.1 z.2) (boundedTimes T)
  local_mass_balance : ∀ φ : MassTest,
    (∫ z in boundedTimes T, F z.1 z.2*φ.transportDerivative z.1 z.2)+
      (∫ p, f₀ p*φ.toFun 0 p.1) = ∫ p, F T p*φ.toFun T p.1
  momentum_conservation : ∀ t ∈ Icc 0 T, momentum (F t) = momentum f₀
  energy_conservation : ∀ t ∈ Icc 0 T, energy (F t) = energy f₀
  entropy_inequality : ∀ t ∈ Icc 0 T,
    ENNReal.ofReal (relativeEntropy (F t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (F s)) ≤ ENNReal.ofReal (relativeEntropy f₀)

end BoltzmannNonuniqueness

end

end

section

/-! # Weak continuity against every bounded measurable phase-space test -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BoltzmannNonuniqueness.LocalMildSolution

theorem weak_continuity {T : ℝ} {f₀ : Density} {F : Evolution}
    (S : LocalMildSolution T f₀ F) {ψ : Phase → ℝ} (hψ : Measurable ψ)
    (hb : ∃ C : ℝ, ∀ p, |ψ p| ≤ C) :
    ContinuousOn (fun t => ∫ p, F t p*ψ p) (Icc 0 T) := by
  obtain ⟨C,hC⟩ := hb
  let c : ℝ≥0 := ⟨|C|,abs_nonneg C⟩
  have hm t : Measurable (F t) := S.measurable.comp (measurable_const.prodMk measurable_id)
  have hi t : Integrable (fun p => F t p*ψ p) :=
    (S.integrable_each_time t).mul_bdd hψ.aestronglyMeasurable (ae_of_all _ hC)
  intro t ht
  apply tendsto_integral_of_L1' (fun p => F t p*ψ p) (Eventually.of_forall hi)
  have hu := ENNReal.Tendsto.const_mul (a := (c : ℝ≥0∞))
    (S.strong.strong_continuity t ht) (Or.inr ENNReal.coe_ne_top)
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le)
  intro s
  have hbnd : ∀ᵐ p ∂(volume : Measure Phase),
      ‖F s p*ψ p-F t p*ψ p‖₊ ≤ c*‖F s p-F t p‖₊ := by
    filter_upwards [] with p
    have hh : ‖F s p*ψ p-F t p*ψ p‖ ≤ |C| * ‖F s p-F t p‖ := by
      rw [← sub_mul,norm_mul,Real.norm_eq_abs (ψ p)]
      exact (mul_le_mul_of_nonneg_left ((hC p).trans (le_abs_self C)) (norm_nonneg _)).trans_eq
        (mul_comm _ _)
    exact_mod_cast hh
  exact eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (((hm s).mul hψ).sub ((hm t).mul hψ)).aestronglyMeasurable hbnd 1

end BoltzmannNonuniqueness.LocalMildSolution

end

end

end OAI
