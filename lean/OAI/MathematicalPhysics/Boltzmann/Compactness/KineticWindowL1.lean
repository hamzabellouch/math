import OAI.MathematicalPhysics.Boltzmann.Approximation.CapNonlinearHotLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanBackwardMap
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.SpacetimeFourierCoordinates
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityAverageDifference
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport

namespace OAI

section

/-! # Measure-preserving coordinates for the partial Fourier argument -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published

def kineticFourierEquiv : KineticPhase ≃ᵐ Velocity × FourierSpace :=
  MeasurableEquiv.prodComm.trans ((MeasurableEquiv.refl Velocity).prodCongr spacetimeHilbertEquiv)

theorem kineticFourierEquiv_apply (z : KineticPhase) :
    kineticFourierEquiv z = (z.2,spacetimeHilbertEquiv z.1) := rfl

theorem kineticFourier_measurePreserving :
    MeasurePreserving kineticFourierEquiv (volume : Measure KineticPhase) volume := by
  have hp := (MeasurePreserving.id (volume : Measure Velocity)).prod spacetimeHilbert_measurePreserving
  have h := hp.comp (Measure.measurePreserving_swap (μ := (volume : Measure SpaceTime))
    (ν := (volume : Measure Velocity)))
  have he : (kineticFourierEquiv : KineticPhase → Velocity × FourierSpace) =
      Prod.map id spacetimeHilbertEquiv ∘ Prod.swap := rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using h

theorem kineticFourier_symm_measurePreserving :
    MeasurePreserving kineticFourierEquiv.symm (volume : Measure (Velocity × FourierSpace)) volume :=
  kineticFourier_measurePreserving.symm kineticFourierEquiv

theorem kineticFourier_characteristic (p : Velocity × FourierSpace) (s : ℝ) :
    kineticFourierEquiv ((p.2.ofLp.1-s,p.2.ofLp.2-s • p.1),p.1) =
      (p.1,p.2-s • characteristicDirection p.1) := by
  rw [kineticFourierEquiv_apply,spacetimeHilbert_translation]
  rfl

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The Fourier-coordinate average is the original physical resolvent average -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def fourierSource (r : KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (p : Velocity × FourierSpace) : ℂ := (ψ p.1*r (p.2.ofLp,p.1) : ℝ)

theorem fourierSource_measurable {r : KineticPhase → ℝ} {ψ : Velocity → ℝ}
    (hr : Measurable r) (hψ : Measurable ψ) : Measurable (fourierSource r ψ) := by
  unfold fourierSource
  fun_prop

theorem fourierSource_resolvent (r : KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (v : Velocity) (z : SpaceTime) :
    velocityLineResolvent (fourierSource r ψ) (v,spacetimeHilbertEquiv z) =
      (ψ v*transportResolvent r (z,v) : ℝ) := by
  change (∫ s in Ioi (0 : ℝ), Real.exp (-s) •
    fourierSource r ψ (v,spacetimeHilbertEquiv z-s • characteristicDirection v)) = _
  calc
    _ = ∫ s in Ioi (0 : ℝ),
        ((Real.exp (-s)*(ψ v*r ((z.1-s,z.2-s • v),v)) : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by
        dsimp only
        rw [← spacetimeHilbert_translation z s v]
        simp only [fourierSource,spacetimeHilbertEquiv,MeasurableEquiv.coe_toLp,
          WithLp.ofLp_toLp,Complex.real_smul,Complex.ofReal_mul])
    _ = ((∫ s in Ioi (0 : ℝ), Real.exp (-s)*(ψ v*r ((z.1-s,z.2-s • v),v)) : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := by
      congr 1
      unfold transportResolvent
      rw [← restrict_Ioi_eq_restrict_Ici,← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by ring)

theorem fourierSource_average (r : KineticPhase → ℝ) (ψ : Velocity → ℝ) (z : SpaceTime) :
    velocityLineAverage (fourierSource r ψ) (spacetimeHilbertEquiv z) =
      (resolventAverage r ψ z : ℂ) := by
  change (∫ v, velocityLineResolvent (fourierSource r ψ) (v,spacetimeHilbertEquiv z)) = _
  simp_rw [fourierSource_resolvent]
  exact integral_complex_ofReal

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Compact time support of the complete kinetic test integrand -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness

theorem KineticTest.exists_time_cutoff (φ : KineticTest) :
    ∃ T : ℝ, 0 < T ∧ (∀ x v, φ.toFun T x v = 0) ∧
      ∀ t, T < t → ∀ p : Phase, φ.transportDerivative t p = 0 ∧ φ.toFun t p.1 p.2 = 0 := by
  obtain ⟨R,hR,hzero⟩ := φ.compact_time_velocity
  let L : LiftedSpaceTimePhase → ℝ := fun z => φ.toFun z.1 (torusProjection z.2.1) z.2.2
  have hs : tsupport L ⊆ {z : LiftedSpaceTimePhase | z.1 ≤ R} := by
    apply closure_minimal
    · intro z hz
      by_contra hn
      exact hz (hzero z.1 (torusProjection z.2.1) z.2.2
        (Or.inl ((lt_of_not_ge hn).trans_le (le_abs_self _))))
    · exact isClosed_le continuous_fst continuous_const
  refine ⟨R+1,by linarith,?_,?_⟩
  · intro x v
    exact hzero (R+1) x v (Or.inl (by rw [abs_of_pos (by linarith : 0 < R+1)]; linarith))
  · intro t ht p
    have hn : (t,torusRepresentative p.1,p.2) ∉ tsupport L := by
      intro hp
      have := hs hp
      change t ≤ R at this
      linarith
    have hd : fderiv ℝ L (t,torusRepresentative p.1,p.2) = 0 := fderiv_of_notMem_tsupport ℝ hn
    refine ⟨congrArg (fun A : LiftedSpaceTimePhase →L[ℝ] ℝ => A (1,p.2,0)) hd,?_⟩
    exact hzero t p.1 p.2 (Or.inl (by linarith [le_abs_self t]))

end BoltzmannNonuniqueness

end

end

section

/-! # Regrouping time and phase space in the weak limit -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

def regroup (f : (ℝ × Position) × Velocity → ℝ) (z : ℝ × Phase) : ℝ :=
  f ((z.1,z.2.1),z.2.2)

theorem weak_regroup {μ : Measure ℝ} [SFinite μ]
    {f : ℕ → (ℝ × Position) × Velocity → ℝ} {g : (ℝ × Position) × Velocity → ℝ}
    (hf : ∀ n, Measurable (f n))
    (h : Published.WeakL1Converges ((μ.prod volume).prod volume) f g) :
    Published.WeakL1Converges (μ.prod (volume : Measure Phase))
      (fun n => regroup (f n)) (regroup g) := by
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((ℝ × Position) × Velocity) ≃ᵐ ℝ × Phase)
      ((μ.prod volume).prod volume) (μ.prod volume) := by
    simpa only [Measure.volume_eq_prod] using measurePreserving_prodAssoc μ
      (volume : Measure Position) (volume : Measure Velocity)
  exact Published.WeakL1Converges.of_comp_measurePreserving hmp
    (fun n => (hf n).comp MeasurableEquiv.prodAssoc.symm.measurable)
    (h.1.comp MeasurableEquiv.prodAssoc.symm.measurable) h

theorem weak_constant_time {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℕ → Phase → ℝ} {g : Phase → ℝ} (hf : ∀ n, Measurable (f n))
    (hfi : ∀ n, Integrable (f n)) (h : Published.WeakL1Converges volume f g) :
    Published.WeakL1Converges (μ.prod volume) (fun n z => f n z.2) (fun z => g z.2) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving
    (Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ))
    (fun n => (hf n).comp measurable_snd) (h.1.comp measurable_snd)
  exact h.prod_constant hfi

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Passing from measurable time traces to kinetic almost-everywhere statements -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.KineticTraceAE

theorem of_traces {P : KineticPhase → Prop} (hP : MeasurableSet {z | P z})
    (h : ∀ᵐ t : ℝ, ∀ᵐ p : Velocity × Velocity, P ((t,p.1),p.2)) :
    ∀ᵐ z : KineticPhase, P z := by
  have hm : Measurable (fun u : ℝ × (Velocity × Velocity) => ((u.1,u.2.1),u.2.2)) := by fun_prop
  have hp : ∀ᵐ u ∂(volume : Measure ℝ).prod (volume : Measure (Velocity × Velocity)),
      P ((u.1,u.2.1),u.2.2) := (Measure.ae_prod_iff_ae_ae (hP.preimage hm)).mpr h
  have he := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure Velocity)
    (volume : Measure Velocity)).quasiMeasurePreserving.ae hp
  have he' : ∀ᵐ z ∂((volume : Measure ℝ).prod (volume : Measure Velocity)).prod volume, P z := by
    filter_upwards [he] with z hz
    exact hz
  simpa only [Measure.volume_eq_prod] using he'

end BoltzmannNonuniqueness.KineticTraceAE

end

end

section

/-! # Time restriction converts local hot-window convergence to compact L1 convergence -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem time_cutoff_compact_L1 {f : ℕ → KineticPhase → ℝ} {A : ℝ}
    (hf : ∀ n, Measurable (f n)) (hn : ∀ n z, 0 ≤ f n z)
    (hL : ∀ R V : ℝ, 0 ≤ V → Tendsto (fun n => eLpNorm (f n) 1
      (((hotBaseVolume A R).prod volume).restrict {z | ‖z.2‖ ≤ V})) atTop (𝓝 0))
    (C : Set KineticPhase) (hC : IsCompact C) :
    Tendsto (fun n => ∫⁻ z in C,
      {z : KineticPhase | z.1.1 ∈ Icc 0 A}.indicator
        (fun z => ENNReal.ofReal (f n z)) z) atTop (𝓝 0) := by
  have hx : Continuous (fun z : KineticPhase => spaceEquiv z.1.2) :=
    spaceEquiv_continuous.comp continuous_fst.snd
  obtain ⟨R,hR⟩ := hC.exists_bound_of_continuousOn hx.continuousOn
  obtain ⟨V,hV⟩ := hC.exists_bound_of_continuousOn continuous_snd.continuousOn
  let V' := max V 0
  let D := {z : KineticPhase | z.1.1 ∈ Icc 0 A}
  have hD : MeasurableSet D := measurableSet_Icc.preimage measurable_fst.fst
  let W := (hotBaseSet A R ×ˢ (univ : Set Velocity)) ∩ {z : KineticPhase | ‖z.2‖ ≤ V'}
  have hCW : C ∩ D ⊆ W := by
    intro z hz
    exact ⟨⟨⟨hz.2,by simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hR z hz.1⟩,
      mem_univ _⟩,(hV z hz.1).trans (le_max_left V 0)⟩
  have hmeasure : ((hotBaseVolume A R).prod volume).restrict {z : KineticPhase | ‖z.2‖ ≤ V'} =
      volume.restrict W := by
    rw [hotBaseVolume_eq,← Measure.restrict_univ (μ := (volume : Measure Velocity)),
      Measure.prod_restrict,← Measure.volume_eq_prod,Measure.restrict_restrict]
    · exact congrArg (fun E => (volume : Measure KineticPhase).restrict E) (inter_comm _ _)
    · exact measurableSet_le measurable_snd.norm measurable_const
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hL R V' (le_max_right V 0)) (fun _ => bot_le)
  intro n
  dsimp only
  rw [eLpNorm_one_eq_lintegral_enorm (hf n).aestronglyMeasurable,hmeasure]
  simp_rw [Real.enorm_eq_ofReal (hn n _)]
  rw [lintegral_indicator hD,Measure.restrict_restrict hD,inter_comm D C]
  exact lintegral_mono' (Measure.restrict_mono_set volume hCW) le_rfl

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
