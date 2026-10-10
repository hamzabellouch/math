import OAI.MathematicalPhysics.Boltzmann.Branching.CompactCapFamily
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.RawPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMildApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport

namespace OAI

section

/-! # Transfer of the actual cap sequence to the Euclidean fundamental cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.TorusKineticChart

def cellVolume (T : ℝ) : Measure Published.KineticPhase :=
  ((volume.restrict (Icc 0 T)).prod (volume.restrict TorusChart.cube)).prod volume

def chart (z : (ℝ × Position) × Velocity) : Published.KineticPhase :=
  ((z.1.1,TorusChart.representative z.1.2),z.2)

theorem measurePreserving (T : ℝ) : MeasurePreserving chart
    ((AnnularEnvelope.timePositionVolume T).prod volume) (cellVolume T) :=
  ((MeasurePreserving.id (volume.restrict (Icc 0 T))).prod
    TorusChart.representative_measurePreserving).prod (MeasurePreserving.id volume)

theorem density_comp (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    EuclideanFlight.density q F ∘ chart = JetCopyDatum.torusPhysical q F := by
  funext z
  simp only [Function.comp_apply,EuclideanFlight.density,chart,
    EuclideanFlight.phaseEquiv_apply,PhysicalLocalization.density,
    JetPeriodicDatum.phaseMap,JetCopyDatum.torusPhysical]

theorem source_comp (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    EuclideanFlight.source b q F ∘ chart =
      CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F) := by
  rw [EuclideanFlight.source_eq_collision]
  funext z
  have hd (v : Velocity) : EuclideanFlight.density q F (chart (z.1,v)) =
      JetCopyDatum.torusPhysical q F (z.1,v) := congrFun (density_comp q F) (z.1,v)
  simp only [Function.comp_apply,CollisionCompactness.collisionSource,
    KineticCollisionNullSets.gain,KineticCollisionNullSets.frequency]
  simp only [chart] at hd ⊢
  simp_rw [hd]

end BoltzmannNonuniqueness.TorusKineticChart

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.density_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n => EuclideanFlight.density q (F.approximation n).solution.value) 1
      (TorusKineticChart.cellVolume F.time) := by
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.measurePreserving F.time)
    (fun n => EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q)
  simpa only [TorusKineticChart.density_comp] using F.density_ui

theorem CompactCapFamily.source_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n : ℕ => EuclideanFlight.source (n+1) q (F.approximation n).solution.value) 1
      (TorusKineticChart.cellVolume F.time) := by
  have hm (n : ℕ) : Measurable (EuclideanFlight.source (n+1) q (F.approximation n).solution.value) := by
    rw [EuclideanFlight.source_eq_collision]
    exact CollisionCompactness.collisionSource_measurable
      (EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q) (n+1)
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.measurePreserving F.time) hm
  simpa only [TorusKineticChart.source_comp] using F.source_ui

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The periodic Euclidean density descends to the actual spatial torus -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusPeriodicity

private theorem exists_lattice_difference {x y : Velocity}
    (h : torusProjection x = torusProjection y) :
    ∃ n : JetLattice.Lattice, ∀ i, x i-y i = (n i : ℝ) := by
  have hc i : ((x i-y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr (congrFun h i)
  have hn i : ∃ n : ℤ, x i-y i = (n : ℝ) := by
    obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hc i)
    refine ⟨n,?_⟩
    have hn' : (n : ℝ) = x i-y i := by simpa only [zsmul_eq_mul,mul_one] using hn
    exact hn'.symm
  choose n hn using hn
  exact ⟨n,hn⟩

private theorem spatial_difference {x y : Velocity} {n : JetLattice.Lattice}
    (hn : ∀ i, x i-y i = (n i : ℝ)) :
    JetPeriodicDatum.spatialMap x-JetCopyDatum.displacement n = JetPeriodicDatum.spatialMap y := by
  apply Prod.ext
  · ext i
    change x i.castSucc-(n i.castSucc : ℝ) = y i.castSucc
    linarith [hn i.castSucc]
  · change x (Fin.last 2)-(n (Fin.last 2) : ℝ) = y (Fin.last 2)
    linarith [hn (Fin.last 2)]

theorem density_eq_of_projection_eq {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, WeightedTranslation.pull (JetCopyDatum.displacement n) F = F)
    {x y : Velocity} (h : torusProjection x = torusProjection y) (q t : ℝ) (v : Velocity) :
    EuclideanFlight.density q F ((t,x),v) = EuclideanFlight.density q F ((t,y),v) := by
  obtain ⟨n,hn⟩ := exists_lattice_difference h
  have he := congrFun (hF n) (t,(JetPeriodicDatum.spatialMap x,v))
  change F (t,(JetPeriodicDatum.spatialMap x-JetCopyDatum.displacement n,v)) =
    F (t,(JetPeriodicDatum.spatialMap x,v)) at he
  rw [spatial_difference hn] at he
  simp only [EuclideanFlight.density,PhysicalLocalization.density,EuclideanFlight.phaseEquiv_apply,
    JetPeriodicDatum.phaseMap]
  rw [he]

theorem density_descends {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, WeightedTranslation.pull (JetCopyDatum.displacement n) F = F)
    (q t : ℝ) (x v : Velocity) :
    JetCopyDatum.torusPhysical q F ((t,torusProjection x),v) =
      EuclideanFlight.density q F ((t,x),v) := by
  have he := density_eq_of_projection_eq hF (TorusChart.projection_representative (torusProjection x)) q t v
  simpa only [JetCopyDatum.torusPhysical,EuclideanFlight.density,PhysicalLocalization.density,
    EuclideanFlight.phaseEquiv_apply,JetPeriodicDatum.phaseMap] using he

theorem source_descends {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, WeightedTranslation.pull (JetCopyDatum.displacement n) F = F)
    (b q t : ℝ) (x v : Velocity) :
    CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F) ((t,torusProjection x),v) =
      EuclideanFlight.source b q F ((t,x),v) := by
  rw [EuclideanFlight.source_eq_collision]
  simp only [CollisionCompactness.collisionSource,KineticCollisionNullSets.gain,
    KineticCollisionNullSets.frequency]
  simp_rw [density_descends hF]

end BoltzmannNonuniqueness.TorusPeriodicity

end

end

section

/-! # Actual pair-product compactness in the Euclidean fundamental cell -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusKineticChart

def pairCellVolume (T : ℝ) : Measure (Published.SpaceTime × (Velocity × Velocity)) :=
  ((volume.restrict (Set.Icc 0 T)).prod (volume.restrict TorusChart.cube)).prod volume

def pairChart (z : (ℝ × Position) × (Velocity × Velocity)) :
    Published.SpaceTime × (Velocity × Velocity) :=
  ((z.1.1,TorusChart.representative z.1.2),z.2)

theorem pair_measurePreserving (T : ℝ) : MeasurePreserving pairChart
    ((AnnularEnvelope.timePositionVolume T).prod volume) (pairCellVolume T) :=
  ((MeasurePreserving.id (volume.restrict (Set.Icc 0 T))).prod
    TorusChart.representative_measurePreserving).prod (MeasurePreserving.id volume)

theorem pair_comp (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    CollisionCompactness.pairProduct (EuclideanFlight.density q F) ∘ pairChart =
      CollisionCompactness.pairProduct (JetCopyDatum.torusPhysical q F) := by
  funext z
  have h (v : Velocity) := congrFun (density_comp q F) (z.1,v)
  dsimp only [Function.comp_apply] at h
  change EuclideanFlight.density q F (chart (z.1,z.2.1))*
    EuclideanFlight.density q F (chart (z.1,z.2.2)) = _
  rw [h,h]
  rfl

end BoltzmannNonuniqueness.TorusKineticChart

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CompactCapFamily.raw_pairs_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n => CollisionCompactness.pairProduct
      (EuclideanFlight.density q (F.approximation n).solution.value)) 1
      (TorusKineticChart.pairCellVolume F.time) := by
  have hm (n) := torusPhysical_measurable (F.approximation n).solution.measurable_value q
  have hn (n) (z) := torusPhysical_nonneg
    (fun u => ((F.approximation n).solution.value_bounds u).1) q z
  have hp := CollisionCompactness.pairProduct_uniformIntegrable hm hn F.pairs_ui
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.pair_measurePreserving F.time)
    (fun n => CollisionCompactness.pairProduct_measurable
      (EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q))
  simpa only [TorusKineticChart.pair_comp] using hp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Euclidean representatives of the actual torus weak limits -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusKineticChart

def liftDensity (g : (ℝ × Position) × Velocity → ℝ) (z : Published.KineticPhase) : ℝ :=
  g ((z.1.1,torusProjection z.1.2),z.2)

def liftPair (W : (ℝ × Position) × (Velocity × Velocity) → ℝ)
    (z : Published.SpaceTime × (Velocity × Velocity)) : ℝ :=
  W ((z.1.1,torusProjection z.1.2),z.2)

theorem projection_measurable : Measurable torusProjection := by
  unfold torusProjection
  fun_prop

theorem liftDensity_measurable {g : (ℝ × Position) × Velocity → ℝ} (hg : Measurable g) :
    Measurable (liftDensity g) := by
  apply hg.comp
  exact (measurable_fst.fst.prodMk (projection_measurable.comp measurable_fst.snd)).prodMk measurable_snd

theorem liftPair_measurable {W : (ℝ × Position) × (Velocity × Velocity) → ℝ} (hW : Measurable W) :
    Measurable (liftPair W) := by
  apply hW.comp
  exact (measurable_fst.fst.prodMk (projection_measurable.comp measurable_fst.snd)).prodMk measurable_snd

theorem liftDensity_comp (g : (ℝ × Position) × Velocity → ℝ) : liftDensity g ∘ chart = g := by
  funext z
  simp only [Function.comp_apply,liftDensity,chart,TorusChart.projection_representative]

theorem liftPair_comp (W : (ℝ × Position) × (Velocity × Velocity) → ℝ) :
    liftPair W ∘ pairChart = W := by
  funext z
  simp only [Function.comp_apply,liftPair,pairChart,TorusChart.projection_representative]

theorem weak_density_transfer {T q : ℝ} {F : ℕ → ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, Measurable (F n)) {g : (ℝ × Position) × Velocity → ℝ}
    (h : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod volume)
      (fun n => JetCopyDatum.torusPhysical q (F n)) g) :
    Published.WeakL1Converges (cellVolume T) (fun n => EuclideanFlight.density q (F n))
      (liftDensity g) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (measurePreserving T)
    (fun n => EuclideanFlight.density_measurable (hF n) q) (liftDensity_measurable h.1)
  simpa only [density_comp,liftDensity_comp] using h

theorem weak_pair_transfer {T q : ℝ} {F : ℕ → ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ n, Measurable (F n)) {W : (ℝ × Position) × (Velocity × Velocity) → ℝ}
    (h : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod volume)
      (fun n => CollisionCompactness.pairProduct (JetCopyDatum.torusPhysical q (F n))) W) :
    Published.WeakL1Converges (pairCellVolume T)
      (fun n => CollisionCompactness.pairProduct (EuclideanFlight.density q (F n))) (liftPair W) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (pair_measurePreserving T)
    (fun n => CollisionCompactness.pairProduct_measurable
      (EuclideanFlight.density_measurable (hF n) q)) (liftPair_measurable h.1)
  simpa only [pair_comp,liftPair_comp] using h

end BoltzmannNonuniqueness.TorusKineticChart

end

end

section

/-! # The constructed approximations satisfy the characteristic equation on the torus -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.TorusFlight

def initialDensity (q : ℝ) (f₀ : JetPrototype.Phase → ℝ) (p : Phase) : ℝ :=
  H q p.2*f₀ (JetPeriodicDatum.phaseMap (TorusChart.phaseRepresentative p))

theorem projection_flight (t : ℝ) (p : Phase) :
    (flight t p).1 = torusProjection (TorusChart.representative p.1+t • p.2) := by
  funext i
  have hp := congrFun (TorusChart.projection_representative p.1) i
  change p.1 i+(t*p.2 i : ℝ) = ((TorusChart.representative p.1 i+t*p.2 i : ℝ) : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  exact congrArg (fun x : AddCircle (1 : ℝ) => x+(t*p.2 i : ℝ)) hp.symm

theorem characteristic (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    ∀ᵐ p : Phase ∂volume,
      JetCopyDatum.torusPhysical q F.value ((T,(flight T p).1),(flight T p).2) =
        initialDensity q f₀ p + ∫ t in 0..T,
          CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)
            ((t,(flight t p).1),(flight t p).2) := by
  have hE := EuclideanFlight.characteristic hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
  have h := TorusChart.phase_measurePreserving.quasiMeasurePreserving.ae (ae_restrict_of_ae hE)
  filter_upwards [h] with p hp
  have hd t : JetCopyDatum.torusPhysical q F.value ((t,(flight t p).1),(flight t p).2) =
      EuclideanFlight.density q F.value ((t,TorusChart.representative p.1+t • p.2),p.2) := by
    rw [projection_flight]
    exact TorusPeriodicity.density_descends F.periodic q t _ p.2
  have hs t : CollisionCompactness.collisionSource b (JetCopyDatum.torusPhysical q F.value)
      ((t,(flight t p).1),(flight t p).2) =
      EuclideanFlight.source b q F.value ((t,TorusChart.representative p.1+t • p.2),p.2) := by
    rw [projection_flight]
    exact TorusPeriodicity.source_descends F.periodic b q t _ p.2
  rw [hd]
  simp_rw [hs]
  simpa only [initialDensity,EuclideanFlight.phaseEquiv_apply,TorusChart.phaseRepresentative] using hp

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
