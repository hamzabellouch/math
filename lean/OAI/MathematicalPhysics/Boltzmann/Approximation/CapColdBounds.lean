import OAI.MathematicalPhysics.Boltzmann.Approximation.CapFiniteBackgroundLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotSourceIntegrability
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLabelFreeLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.MomentAverageBound
import OAI.MathematicalPhysics.Boltzmann.Branching.VanishingMajorant
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricDampedRetention
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricMesh
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFiniteCap
import OAI.MathematicalPhysics.Boltzmann.Jets.JetFamilyBounds

namespace OAI

section

/-! # Half-Gaussian moments of the actual cold part -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedTranslation BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.cold_envelope {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (i : JetLattice.Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    H q p.2*F.cold i (t,p) ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (shift (displacement i.lattice) p) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  exact rebuilt_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq (by positivity)
    (bounds (by positivity) F.amplitude_pos).1 hT (by linarith [F.amplitude_pos])
    (hTmax.trans (by norm_num)) le_rfl N hh₀ F.solution.measurable_value
    F.solution.value_bounds F.initial_bound i ht p

theorem CapApproximation.coldTotal_moment_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x : JetPrototype.Space) :
    moment (fun v => H q v*F.coldTotal (t,(x,v))) ≤ ENNReal.ofReal
      (escapedConstant s₀ η K α d₀*hotConstant q+JetEnvelopeGain.momentConstant K α γ/t) := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT
  have hs := F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT
  have hcell (y : Velocity) (hy : y ∈ TorusChart.cube) :
      moment (fun v => H q v*F.coldTotal (t,(JetPeriodicDatum.spatialMap y,v))) ≤
        ENNReal.ofReal (escapedConstant s₀ η K α d₀*hotConstant q+
          JetEnvelopeGain.momentConstant K α γ/t) := by
    have hm := cell_moment_bound (Z := 0) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hq le_rfl ht.1 (ht.2.trans hTmax) hsmall N y hy
      (fun v => F.coldTotal (t,(JetPeriodicDatum.spatialMap y,v)))
      (fun i v => F.cold i (t,(JetPeriodicDatum.spatialMap y,v)))
      (fun i => (hc.1 i).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      (fun i v => hc.2.1 i _) (fun v => (hs.2 _).1)
      (fun i hi v => congrFun (rebuilt_zero s₀ η K α γ d₀ q (N+1)
        (damping q (N+1) F.amplitude) T N (fun u => (F.solution.value_bounds u).1) i hi) _)
      (fun i v => F.cold_envelope hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall hq hT hTmax
        i ht (JetPeriodicDatum.spatialMap y,v)) (ae_of_all _ (fun _ => by simp [coldTotal]))
    apply hm.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa only [zero_add,div_eq_mul_inv,one_mul] using
      add_le_add (le_refl (escapedConstant s₀ η K α d₀*hotConstant q))
        (mul_le_mul_of_nonneg_left
          (AnnularEnvelope.finiteEnvelope_le_inv_time hs₀.le hη.le ht.1 (Finset.range N)
            (transverse y)) (JetEnvelopeGain.momentConstant_nonneg hK α γ))
  obtain ⟨n,y,hy,hxy⟩ := exists_shift_in_centered_cell x
  have he (v : Velocity) : F.coldTotal (t,(JetPeriodicDatum.spatialMap y,v)) =
      F.coldTotal (t,(x,v)) := by
    have h := family_sum_pull (c := F.cold) (displacement n) (relabel n)
      (fun i => rebuilt_shift n (F.solution.periodic n) i) (t,(x,v))
    change F.coldTotal (t,(x-displacement n,v)) = F.coldTotal (t,(x,v)) at h
    rwa [hxy] at h
  simpa only [he] using hcell y hy

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform cold moments on positive-time blow-up slabs -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.VelocityMoment

theorem moment_const_mul {r : ℝ} (hr : 0 ≤ r) (f : Velocity → ℝ) :
    moment (fun v => r*f v) = ENNReal.ofReal r*moment f := by
  unfold moment
  simp_rw [show ∀ v, weight v*(r*f v) = r*(weight v*f v) by intro v; ring,
    ENNReal.ofReal_mul hr]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

open VelocityMoment

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem rescaledColdDensity_moment (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (hT : S.radius n*t ≤ shrinkingHorizon F.horizonScale n) (x : JetPrototype.Space) :
    moment (fun v => S.rescaledColdDensity n ((t,x),v)) ≤ ENNReal.ofReal
      (S.radius n*(escapedConstant s₀ η K α d₀*hotConstant q)+
        JetEnvelopeGain.momentConstant K α γ/t) := by
  have hr := S.radius_pos hs₀ n
  have hb := (F.approximation n).coldTotal_moment_bound hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq (shrinkingHorizon_pos F.horizonScale_pos n).le
    ((shrinkingHorizon_le F.horizonScale_pos n).trans F.horizonScale_le)
    ⟨mul_pos hr ht,hT⟩ (S.radius n • x)
  have he : (fun v => S.rescaledColdDensity n ((t,x),v)) =
      (fun v => S.radius n*(H q v*(F.approximation n).coldTotal
        (S.radius n*t,(S.radius n • x,v)))) := by
    funext v
    exact mul_assoc _ _ _
  rw [he,moment_const_mul hr.le]
  apply (mul_le_mul' le_rfl hb).trans
  rw [← ENNReal.ofReal_mul hr.le]
  apply le_of_eq
  congr 1
  field_simp

theorem eventually_rescaledColdDensity_moment (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc a A, ∀ x : JetPrototype.Space,
      moment (fun v => S.rescaledColdDensity (κ n) ((t,x),v)) ≤ ENNReal.ofReal
        (escapedConstant s₀ η K α d₀*hotConstant q+JetEnvelopeGain.momentConstant K α γ/a) := by
  have hC : 0 ≤ escapedConstant s₀ η K α d₀*hotConstant q :=
    mul_nonneg (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _) (hotConstant_nonneg q)
  have hr := ((S.radius_tendsto_zero hs₀).comp hκ.tendsto_atTop).eventually
    (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hr,S.eventually_scaled_slab hs₀ hU hA] with n hn hslab
  intro t ht x
  have htpos := ha.trans_le ht.1
  apply (S.rescaledColdDensity_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq
    (κ n) htpos (hslab t ⟨htpos.le,ht.2⟩).2 x).trans
  apply ENNReal.ofReal_le_ofReal
  apply add_le_add
  · simpa only [Function.comp_apply,one_mul] using mul_le_mul_of_nonneg_right hn.le hC
  · exact div_le_div_of_nonneg_left (JetEnvelopeGain.momentConstant_nonneg hK α γ) ha ht.1

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual escaped cold density in Euclidean coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetLattice

theorem measurableSet_spatialEnlargement (s₀ η : ℝ) (i : Label) :
    MeasurableSet {z : ℝ × Velocity | z.2 ∈ spatialEnlargement s₀ η z.1 i} := by
  change MeasurableSet
    ({z : ℝ × Velocity | transverse z.2-transverseShift i.lattice ∈
      JetGeometry.enlargement η (JetGeometry.jetScale s₀ η i.annulus) i.positive} ∩
     {z : ℝ × Velocity | |axial z.2-axialShift i.lattice| ≤ 1/8+2*z.1+1/16})
  apply MeasurableSet.inter
  · exact (Metric.isClosed_cthickening.measurableSet).preimage (by
      unfold transverse transverseShift
      fun_prop)
  · exact measurableSet_le (by unfold axial; fun_prop) (by fun_prop)

end BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.escapedTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ :=
  ∑' i, escaped s₀ η z.1.1 N z.1.2
    (fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) i

theorem CapApproximation.escapedTotal_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.escapedTotal := by
  classical
  have hc := (F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).1
  apply Measurable.tsum
  intro i
  have hi : MeasurableSet {z : Published.KineticPhase |
      z.1.2 ∉ JetLattice.spatialEnlargement s₀ η z.1.1 i} :=
    ((JetLattice.measurableSet_spatialEnlargement s₀ η i).preimage measurable_fst).compl
  have hm : Measurable (fun z : Published.KineticPhase =>
      F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) := by
    apply (hc i).comp
    unfold JetPeriodicDatum.spatialMap transverse axial
    fun_prop
  by_cases hN : i.annulus < N
  · change Measurable (fun z : Published.KineticPhase => if i.annulus < N ∧
        JetLatticeTail.outside η (JetGeometry.jetScale s₀ η i.annulus) z.1.1 i.positive z.1.2 i.lattice
        then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0)
    simp only [hN,true_and,outside_iff_not_mem]
    exact hm.ite hi measurable_const
  · change Measurable (fun z : Published.KineticPhase => if i.annulus < N ∧
        JetLatticeTail.outside η (JetGeometry.jetScale s₀ η i.annulus) z.1.1 i.positive z.1.2 i.lattice
        then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0)
    simp only [hN,false_and,ite_false]
    exact measurable_const

theorem CapApproximation.escapedTotal_nonneg {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (z : Published.KineticPhase) : 0 ≤ F.escapedTotal z := by
  have hc := (F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).2.1
  apply tsum_nonneg
  intro i
  unfold escaped
  split_ifs
  · exact hc i _
  · exact le_rfl

theorem CapApproximation.escapedTotal_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (A : ℝ) {z : Published.KineticPhase} (ht : z.1.1 ∈ Ioc 0 T)
    (hx : ∀ k, |z.1.2 k| ≤ 1) :
    F.escapedTotal z ≤ JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent A)*z.1.1^A := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT
  let f : JetLattice.Label → ℝ := fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))
  have hfs : Summable f :=
    ((F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT).2 _).1
  have henv (i : JetLattice.Label) : H q z.2*f i ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
        (JetSpatialBox.shifted z.1.2 i.lattice,z.2) := by
    have he : (JetSpatialBox.shifted z.1.2 i.lattice,z.2) =
        WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2) := rfl
    rw [he]
    exact F.cold_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hT hTmax i ht
      (JetPeriodicDatum.spatialMap z.1.2,z.2)
  have hb := normalized_escaped_bound (γ := γ) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht.1
    (ht.2.trans hTmax) hsmall A q N f z.1.2 z.2 hx
    (fun i => hc.2.1 i _) hfs (fun i _ => henv i)
  exact hb

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact removal of the escaped colors from an actual cap approximation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def CapApproximation.centralTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ := by
  classical
  exact ∑' i, if i.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i
    then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0

theorem CapApproximation.centralTotal_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.centralTotal := by
  classical
  have hc := (F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).1
  apply Measurable.tsum
  intro i
  have hm : Measurable (fun z : Published.KineticPhase =>
      F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) := by
    apply (hc i).comp
    unfold JetPeriodicDatum.spatialMap transverse axial
    fun_prop
  have hi : MeasurableSet {z : Published.KineticPhase |
      z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i} :=
    (JetLattice.measurableSet_spatialEnlargement s₀ η i).preimage measurable_fst
  by_cases hN : i.annulus < N
  · simpa only [hN,true_and] using hm.ite hi measurable_const
  · simp only [hN,false_and,ite_false]
    exact measurable_const

theorem CapApproximation.coldTotal_eq_central_add_escaped {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (z : Published.KineticPhase) :
    F.coldTotal (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) =
      F.centralTotal z+F.escapedTotal z := by
  classical
  let f : JetLattice.Label → ℝ := fun i => F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))
  let g : JetLattice.Label → ℝ := fun i =>
    if i.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i then f i else 0
  let h : JetLattice.Label → ℝ := escaped s₀ η z.1.1 N z.1.2 f
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hfs : Summable f := (F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).2 _ |>.1
  have hfn (i) : 0 ≤ f i := hc.2.1 i _
  have hgn (i) : 0 ≤ g i := by
    dsimp [g]
    split_ifs
    · exact hfn i
    · exact le_rfl
  have hgl (i) : g i ≤ f i := by dsimp [g]; split_ifs <;> simp only [le_refl,hfn]
  have hhn (i) : 0 ≤ h i := by
    dsimp [h,escaped]
    split_ifs
    · exact hfn i
    · exact le_rfl
  have hhl (i) : h i ≤ f i := by dsimp [h,escaped]; split_ifs <;> simp only [le_refl,hfn]
  have hgs := Summable.of_nonneg_of_le hgn hgl hfs
  have hhs := Summable.of_nonneg_of_le hhn hhl hfs
  change (∑' i, f i) = (∑' i, g i)+(∑' i, h i)
  rw [← hgs.tsum_add hhs]
  apply tsum_congr
  intro i
  by_cases hN : i.annulus < N
  · by_cases hi : z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i
    <;> simp [g,h,escaped,hN,hi,outside_iff_not_mem]
  · have hz : f i = 0 := congrFun
      (rebuilt_zero s₀ η K α γ d₀ q (N+1) (WeightedLocalControl.damping q (N+1) F.amplitude)
        T N (fun u => (F.solution.value_bounds u).1) i hN) _
    simp [g,h,escaped,hN,hz]

theorem CapApproximation.centralTotal_single {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (z : Published.KineticPhase) (ht : z.1.1 ≤ 1/32)
    (i : JetLattice.Label) (hN : i.annulus < N)
    (hi : z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i) :
    F.centralTotal z = F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) := by
  classical
  unfold centralTotal
  rw [tsum_eq_single i]
  · simp only [hN,hi,and_self,ite_true]
  · intro j hji
    have hj : ¬(j.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 j) := by
      rintro ⟨_,hj⟩
      exact hji (JetLattice.common_point_label hs₀ hsmax hη hηmax ht hj hi)
    simp only [hj,ite_false]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cold density is bounded by the main free core and its remainder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.cold_free_majorant_at_main {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (z : KineticPhase) (ht : z.1.1 ∈ Ioc 0 T) (i : Label) (hi : i.annulus < N)
    (hx : z.1.2 ∈ spatialEnlargement s₀ η z.1.1 i) :
    H q z.2*F.coldTotal (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) ≤
      JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
        (WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2))+
      JetSupersolution.epsilon K (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10)*
        JetBarrier.barrier η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
          (WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2))+
      H q z.2*F.escapedTotal z := by
  rw [F.coldTotal_eq_central_add_escaped hs₀ hsmax hη hηmax hK hd₀.le hq hT z,
    F.centralTotal_single hs₀ hsmax hη hηmax z (ht.2.trans hTmax) i hi hx,mul_add]
  exact add_le_add (F.cold_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hT hTmax
    i ht (JetPeriodicDatum.spatialMap z.1.2,z.2)) le_rfl

theorem CapApproximation.coldTotal_eq_escaped_of_no_main {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) (z : KineticPhase)
    (hx : ∀ i : Label, i.annulus < N → z.1.2 ∉ spatialEnlargement s₀ η z.1.1 i) :
    F.coldTotal (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) = F.escapedTotal z := by
  classical
  rw [F.coldTotal_eq_central_add_escaped hs₀ hsmax hη hηmax hK hd₀ hq hT z]
  have hz : F.centralTotal z = 0 := by
    have hi : ∀ i : Label, ¬(i.annulus < N ∧ z.1.2 ∈ spatialEnlargement s₀ η z.1.1 i) :=
      fun i hi => hx i hi.1 hi.2
    simp only [CapApproximation.centralTotal,hi,ite_false,tsum_zero]
  rw [hz,zero_add]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Only finitely many central colors remain in the centered cell -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

def centralLabels (N : ℕ) : Finset JetLattice.Label :=
  ((Finset.range N).product (Finset.univ : Finset Bool)).image
    (fun p => ⟨p.1,p.2,0⟩)

theorem mem_centralLabels {N : ℕ} {i : JetLattice.Label} :
    i ∈ centralLabels N ↔ i.annulus < N ∧ i.lattice = 0 := by
  classical
  constructor
  · intro hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    exact ⟨Finset.mem_range.mp (Finset.mem_product.mp hp).1,rfl⟩
  · rintro ⟨hN,hl⟩
    apply Finset.mem_image.mpr
    refine ⟨(i.annulus,i.positive),Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hN,Finset.mem_univ _⟩,?_⟩
    cases i
    simp_all

theorem CapApproximation.centralTotal_finite {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (z : Published.KineticPhase) (ht : z.1.1 ≤ 1/32) (hx : z.1.2 ∈ TorusChart.cube) :
    F.centralTotal z = ∑ i ∈ centralLabels N,
      (JetLattice.spatialEnlargement s₀ η z.1.1 i).indicator
        (fun _ => F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) z.1.2 := by
  classical
  unfold centralTotal
  rw [tsum_eq_sum (s := centralLabels N)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [(mem_centralLabels.mp hi).1,true_and,Set.indicator_apply]
  · intro i hi
    by_cases hm : i.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i
    · exact False.elim (hi (mem_centralLabels.mpr
        ⟨hm.1,enlargement_central_lattice hs₀ hsmax hη ht hx hm.2⟩))
    · simp only [hm,ite_false]

theorem CapApproximation.centralTotal_finite_pairs {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (z : Published.KineticPhase) (ht : z.1.1 ≤ 1/32) (hx : z.1.2 ∈ TorusChart.cube) :
    F.centralTotal z = ∑ j ∈ Finset.range N, ∑ a : Bool,
      (JetLattice.spatialEnlargement s₀ η z.1.1 ⟨j,a,0⟩).indicator
        (fun _ => F.cold ⟨j,a,0⟩ (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) z.1.2 := by
  rw [F.centralTotal_finite hs₀ hsmax hη z ht hx,centralLabels,Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro p _ q _ hpq
    have h₁ := congrArg JetLattice.Label.annulus hpq
    have h₂ := congrArg JetLattice.Label.positive hpq
    exact Prod.ext h₁ h₂

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The central cold sum on a fixed radial window has fixed mesh indices -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.centralTotal_mesh_window (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    {δ R : ℝ} (hδ : 0 < δ) (n : ℕ) (t : ℝ) (x v : Velocity)
    (ht : S.radius (E.indices n)*t ≤ 1/32)
    (hx : S.radius (E.indices n) • x ∈ TorusChart.cube)
    (hlo : δ ≤ ‖transverse x‖) (hhi : ‖transverse x‖ ≤ R)
    (hU : GeometricMesh.index R η < GeometricMesh.index (s₀/S.radius (E.indices n)) η) :
    (F.approximation (E.indices n)).centralTotal
      ((S.radius (E.indices n)*t,S.radius (E.indices n) • x),v) =
    ∑ a : Bool, ∑ k ∈ Finset.Icc (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η),
      if (E.coldLabel k a n).annulus < F.indices (E.indices n) then
        (JetLattice.spatialEnlargement s₀ η (S.radius (E.indices n)*t) (E.coldLabel k a n)).indicator
          (fun _ => (F.approximation (E.indices n)).cold (E.coldLabel k a n)
            (S.radius (E.indices n)*t,(JetPeriodicDatum.spatialMap (S.radius (E.indices n) • x),v)))
          (S.radius (E.indices n) • x)
      else 0 := by
  classical
  let r := S.radius (E.indices n)
  let N := F.indices (E.indices n)
  rw [(F.approximation (E.indices n)).centralTotal_finite_pairs hs₀ hsmax hη _ ht hx,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  let f : ℕ → ℝ := fun j =>
    (JetLattice.spatialEnlargement s₀ η (r*t) ⟨j,a,0⟩).indicator
      (fun _ => (F.approximation (E.indices n)).cold ⟨j,a,0⟩
        (r*t,(JetPeriodicDatum.spatialMap (r • x),v))) (r • x)
  have hsupp (j : ℕ) (_hj : j < N) (hf : f j ≠ 0) :
      GeometricMesh.jetMeshIndex s₀ η r j ∈
        Finset.Icc (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) := by
    have hy : r • x ∈ JetLattice.spatialEnlargement s₀ η (r*t) ⟨j,a,0⟩ := by
      by_contra h
      exact hf (indicator_of_notMem h _)
    have hz : JetLattice.transverseShift (0 : JetLattice.Lattice) = 0 := by
      ext i
      simp [JetLattice.transverseShift]
    have hy₁ : transverse (r • x)-JetLattice.transverseShift 0 ∈
        JetGeometry.enlargement η (JetGeometry.jetScale s₀ η j) a := hy.1
    rw [hz,sub_zero] at hy₁
    have hs : r • transverse x ∈ JetGeometry.enlargement η (JetGeometry.jetScale s₀ η j) a := hy₁
    exact Finset.mem_Icc.mpr (JetGeometry.enlargement_mesh_window hs₀ hη (S.radius_pos hs₀ _)
      hδ j a hs hlo hhi)
  exact GeometricMesh.finite_sum_on_window s₀ η (fun m => S.radius (E.indices m)) n N
    (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) hU f hsupp

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Escaped cold mass vanishes on bounded positive-time dilation windows -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledEscapedDensity (S : AttainedCapSequence F) (n : ℕ)
    (z : Published.KineticPhase) : ℝ :=
  S.radius n*H q z.2*(F.approximation n).escapedTotal
    ((S.radius n*z.1.1,S.radius n • z.1.2),z.2)

theorem rescaledEscapedDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.rescaledEscapedDensity n) := by
  have hm := (F.approximation n).escapedTotal_measurable hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  exact (((ChartKernel.measurable_H q).comp measurable_snd).const_mul _).mul
    (hm.comp (by fun_prop))

theorem rescaledEscapedDensity_nonneg (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : Published.KineticPhase) :
    0 ≤ S.rescaledEscapedDensity n z :=
  mul_nonneg (mul_nonneg (S.radius_pos hs₀ n).le (H_nonneg q z.2))
    ((F.approximation n).escapedTotal_nonneg hs₀ hsmax hη hηmax hK hd₀ hq
      (shrinkingHorizon_pos F.horizonScale_pos n).le _)

theorem eventually_rescaledEscapedDensity_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < U) (R : ℝ) :
    ∀ᶠ n in atTop, ∀ z : Published.KineticPhase, z.1.1 ∈ Icc a A → ‖z.1.2‖ ≤ R →
      |S.rescaledEscapedDensity (κ n) z| ≤
        (JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)*
          S.radius (κ n))*H q z.2 := by
  have hrlim : Tendsto (fun n => S.radius (κ n)*R) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_mul] using
      ((S.radius_tendsto_zero hs₀).comp hκ.tendsto_atTop).mul_const R
  have hr := hrlim.eventually
    (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hr,S.eventually_scaled_slab hs₀ hU hA] with n hn hslab
  intro z ht hx
  have hrpos := S.radius_pos hs₀ (κ n)
  have hbound := (F.approximation (κ n)).escapedTotal_bound hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq (shrinkingHorizon_pos F.horizonScale_pos _).le
    ((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le) 0
    (z := ((S.radius (κ n)*z.1.1,S.radius (κ n) • z.1.2),z.2))
    ⟨mul_pos hrpos (ha.trans_le ht.1),(hslab z.1.1 ⟨(ha.trans_le ht.1).le,ht.2⟩).2⟩
    (fun k => ?_)
  · simp only [Real.rpow_zero,mul_one] at hbound
    rw [abs_of_nonneg (S.rescaledEscapedDensity_nonneg hs₀ hsmax hη hηmax hK hd₀.le hq _ _)]
    exact (mul_le_mul_of_nonneg_left hbound (mul_nonneg hrpos.le (H_nonneg q z.2))).trans_eq
      (by ring)
  · calc
      |(S.radius (κ n) • z.1.2) k| = S.radius (κ n)*|z.1.2 k| := by
        change |S.radius (κ n)*z.1.2 k| = _
        rw [abs_mul,abs_of_pos hrpos]
      _ ≤ S.radius (κ n)*‖z.1.2‖ := mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.1.2 k) hrpos.le
      _ ≤ S.radius (κ n)*R := mul_le_mul_of_nonneg_left hx hrpos.le
      _ ≤ 1 := hn.le

def coldSlabSet (a A R : ℝ) : Set Published.KineticPhase :=
  (Icc a A ×ˢ Metric.closedBall (0 : Velocity) R) ×ˢ univ

def coldSlabVolume (a A R : ℝ) : Measure Published.KineticPhase :=
  ((volume.restrict (Icc a A)).prod (volume.restrict (Metric.closedBall (0 : Velocity) R))).prod volume

theorem coldSlabVolume_eq (a A R : ℝ) :
    coldSlabVolume a A R = volume.restrict (coldSlabSet a A R) := by
  rw [coldSlabVolume,Measure.prod_restrict,← Measure.volume_eq_prod,
    Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]
  rfl

theorem rescaledEscapedDensity_tendsto_zero (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < U) (R : ℝ) :
    Tendsto (fun n => eLpNorm (S.rescaledEscapedDensity (κ n)) 1 (coldSlabVolume a A R))
      atTop (𝓝 0) := by
  let C := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)
  let _ : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  have hi : Integrable (fun z : Published.KineticPhase => H q z.2) (coldSlabVolume a A R) :=
    (integrable_H hq).comp_snd _
  apply Compactness.tendsto_L1_of_vanishing_majorant
    (fun n => (S.rescaledEscapedDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq _).aestronglyMeasurable)
    ((ChartKernel.measurable_H q).comp measurable_snd) hi (ae_of_all _ (fun z => H_nonneg q z.2))
    (c := fun n => C*S.radius (κ n))
  · simpa only [Function.comp_def,mul_zero] using
      ((S.radius_tendsto_zero hs₀).comp hκ.tendsto_atTop).const_mul C
  · filter_upwards [S.eventually_rescaledEscapedDensity_bound hs₀ hsmax hη hηmax hK hα hαmax hγ
      hd₀ hd₀max hsmall hq hκ hU ha hA R] with n hn
    rw [coldSlabVolume_eq]
    filter_upwards [ae_restrict_mem ((measurableSet_Icc.prod measurableSet_closedBall).prod
      MeasurableSet.univ)] with z hz
    exact hn z hz.1.1 (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual cold dilation has the same local limit as its central colors -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def rescaledCentralDensity (S : AttainedCapSequence F) (n : ℕ)
    (z : Published.KineticPhase) : ℝ :=
  S.radius n*H q z.2*(F.approximation n).centralTotal
    ((S.radius n*z.1.1,S.radius n • z.1.2),z.2)

theorem rescaledCentralDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.rescaledCentralDensity n) := by
  have hm := (F.approximation n).centralTotal_measurable hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  exact (((ChartKernel.measurable_H q).comp measurable_snd).const_mul _).mul
    (hm.comp (by fun_prop))

theorem rescaledCold_sub_central (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : Published.KineticPhase) :
    S.rescaledColdDensity n ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)-
      S.rescaledCentralDensity n z = S.rescaledEscapedDensity n z := by
  have h := (F.approximation n).coldTotal_eq_central_add_escaped hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le ((S.radius n*z.1.1,S.radius n • z.1.2),z.2)
  have hmap : JetPeriodicDatum.spatialMap (S.radius n • z.1.2) =
      S.radius n • JetPeriodicDatum.spatialMap z.1.2 := rfl
  change S.radius n*H q z.2*(F.approximation n).coldTotal
    (S.radius n*z.1.1,(S.radius n • JetPeriodicDatum.spatialMap z.1.2,z.2))-
    S.radius n*H q z.2*(F.approximation n).centralTotal
      ((S.radius n*z.1.1,S.radius n • z.1.2),z.2) =
    S.radius n*H q z.2*(F.approximation n).escapedTotal
      ((S.radius n*z.1.1,S.radius n • z.1.2),z.2)
  rw [← hmap,h]
  ring

theorem cold_central_difference_tendsto_zero (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < U) (R : ℝ) :
    Tendsto (fun n => eLpNorm (fun z : Published.KineticPhase =>
      S.rescaledColdDensity (κ n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2)-
        S.rescaledCentralDensity (κ n) z) 1 (coldSlabVolume a A R)) atTop (𝓝 0) := by
  simp_rw [S.rescaledCold_sub_central hs₀ hsmax hη hηmax hK hd₀.le hq]
  exact S.rescaledEscapedDensity_tendsto_zero hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hκ hU ha hA R

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual escaped cold density is uniformly bounded in every cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem escaped_bound_global {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (A q : ℝ) (N : ℕ)
    (f : Label → ℝ) (x v : Velocity)
    (hf : ∀ i, 0 ≤ f i) (hfs : Summable f)
    (hfU : ∀ i, i.annulus < N → f i ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    (∑' i, escaped s₀ η t N x f i) ≤
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A*VelocityWeight.H q v := by
  classical
  have hnon (i) : 0 ≤ escaped s₀ η t N x f i := by
    unfold escaped
    split_ifs
    · exact hf i
    · exact le_rfl
  have hle (i) : escaped s₀ η t N x f i ≤ f i := by
    unfold escaped
    split_ifs
    · exact le_rfl
    · exact hf i
  have hsum : Summable (escaped s₀ η t N x f) := Summable.of_nonneg_of_le hnon hle hfs
  have h := JetEscapedEnvelope.real_power_global hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    ht htmax hsmall A q (fun j _ _ => j < N) (fun j a n => f ⟨j,a,n⟩) x v
    (fun j a n hj => hfU ⟨j,a,n⟩ hj)
  have he : (∑' i, ENNReal.ofReal (escaped s₀ η t N x f i)) =
      JetEscapedEnvelope.escapedSum s₀ η t x (fun j _ _ => j < N) (fun j a n => f ⟨j,a,n⟩) := by
    rw [tsum_labels]
    unfold escaped JetEscapedEnvelope.escapedSum
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero]
  rw [← he, ← ENNReal.ofReal_tsum_of_nonneg hnon hsum] at h
  have hB : 0 ≤ JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*
      t^A*VelocityWeight.H q v := by
    have hc := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent A)
    exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg ht.le A)) (VelocityWeight.H_nonneg q v)
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg hnon),ENNReal.toReal_ofReal hB] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

theorem normalized_escaped_bound_global {s₀ η K α γ d₀ t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (A q : ℝ) (N : ℕ)
    (f : Label → ℝ) (x v : Velocity)
    (hf : ∀ i, 0 ≤ f i) (hfs : Summable f)
    (hfU : ∀ i, i.annulus < N → VelocityWeight.H q v*f i ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    (∑' i, escaped s₀ η t N x f i) ≤
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A := by
  have h := escaped_bound_global hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall A q N
    (fun i => VelocityWeight.H q v*f i) x v
    (fun i => mul_nonneg (VelocityWeight.H_nonneg q v) (hf i))
    (hfs.mul_left (VelocityWeight.H q v)) hfU
  have he (i) : escaped s₀ η t N x (fun j => VelocityWeight.H q v*f j) i =
      VelocityWeight.H q v*escaped s₀ η t N x f i := by
    unfold escaped
    split_ifs <;> simp only [mul_zero]
  simp_rw [he] at h
  rw [tsum_mul_left] at h
  have hh : VelocityWeight.H q v*(∑' i, escaped s₀ η t N x f i) ≤
      VelocityWeight.H q v*(JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A) :=
    h.trans_eq (mul_comm _ _)
  exact (mul_le_mul_iff_of_pos_left (VelocityWeight.H_pos q v)).mp hh

theorem CapApproximation.escapedTotal_bound_global {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (A : ℝ) {z : Published.KineticPhase} (ht : z.1.1 ∈ Ioc 0 T) :
    F.escapedTotal z ≤ JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent A)*z.1.1^A := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT
  let f : JetLattice.Label → ℝ := fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))
  have hfs : Summable f :=
    ((F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT).2 _).1
  have henv (i : JetLattice.Label) : H q z.2*f i ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
        (JetSpatialBox.shifted z.1.2 i.lattice,z.2) := by
    have he : (JetSpatialBox.shifted z.1.2 i.lattice,z.2) =
        WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2) := rfl
    rw [he]
    exact F.cold_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hT hTmax i ht
      (JetPeriodicDatum.spatialMap z.1.2,z.2)
  have hb := normalized_escaped_bound_global (γ := γ) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht.1
    (ht.2.trans hTmax) hsmall A q N f z.1.2 z.2
    (fun i => hc.2.1 i _) hfs (fun i _ => henv i)
  exact hb

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Global almost-everywhere majorants in the Euclidean averaging coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem euclideanHot_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.euclideanHot n) :=
  EuclideanFlight.density_measurable (S.normalizedHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n) q

theorem euclideanHotSource_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.euclideanHotSource n) := by
  have hm := (F.approximation n).hotNetSource_measurable hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le
  have hk : Measurable (fun z : Published.KineticPhase =>
      (S.radius n*z.1.1,PositiveIntegral.scalePhase (S.radius n) (EuclideanFlight.phaseEquiv (z.1.2,z.2)))) := by
    have hp : Measurable (fun z : Published.KineticPhase => EuclideanFlight.phaseEquiv (z.1.2,z.2)) :=
      EuclideanFlight.phaseEquiv.measurable.comp (measurable_fst.snd.prodMk measurable_snd)
    unfold PositiveIntegral.scalePhase
    have hs : Measurable (fun z : Published.KineticPhase =>
        S.radius n • (EuclideanFlight.phaseEquiv (z.1.2,z.2)).1) := by
      have hc : Measurable (fun _ : Published.KineticPhase => S.radius n) := measurable_const
      exact hc.smul hp.fst
    exact (measurable_fst.fst.const_mul _).prodMk (hs.prodMk hp.snd)
  exact ((ChartKernel.measurable_H q).comp measurable_snd).mul (hm.comp hk)

theorem eventually_euclideanHot_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ᵐ z ∂(volume : Measure Published.KineticPhase), z.1.1 ∈ Icc 0 A →
      0 ≤ S.euclideanHot (κ n) z ∧ S.euclideanHot (κ n) z ≤ (A+1)*H q z.2 := by
  filter_upwards [S.eventually_scaled_slab hs₀ hU hA] with n hslab
  let Fn := F.approximation (κ n)
  have hr := S.radius_pos hs₀ (κ n)
  have hcap := Fn.hot_spacetime_cap hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hn := (Fn.hot_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le).2.1
  have hp := (ColdDilationMeasure.spacetime_dilation_quasiMeasurePreserving hr).ae hcap
  filter_upwards [EuclideanFlight.kineticMap_measurePreserving.quasiMeasurePreserving.ae hp]
    with z hz ht
  have hb := hz (hslab z.1.1 ht)
  have hδ : DatumBounds.scale s₀ η (F.indices (κ n)+1) ≤ S.radius (κ n) := by
    dsimp [radius]
    linarith [(S.time_mem (κ n)).1]
  have hu : S.normalizedHot (κ n) (EuclideanFlight.kineticMap z) ≤ A+1 := by
    apply (div_le_iff₀ hr).mpr
    have ht' := mul_le_mul_of_nonneg_left ht.2 hr.le
    change Fn.hot (S.radius (κ n)*z.1.1,
      (S.radius (κ n) • (EuclideanFlight.phaseEquiv (z.1.2,z.2)).1,z.2)) ≤
        S.radius (κ n)*z.1.1+DatumBounds.scale s₀ η (F.indices (κ n)+1) at hb
    change Fn.hot (S.radius (κ n)*z.1.1,
      (S.radius (κ n) • (EuclideanFlight.phaseEquiv (z.1.2,z.2)).1,z.2)) ≤ _
    nlinarith
  have hl : 0 ≤ S.normalizedHot (κ n) (EuclideanFlight.kineticMap z) := div_nonneg (hn _) hr.le
  change 0 ≤ H q z.2*S.normalizedHot (κ n) (EuclideanFlight.kineticMap z) ∧
    H q z.2*S.normalizedHot (κ n) (EuclideanFlight.kineticMap z) ≤ (A+1)*H q z.2
  exact ⟨mul_nonneg (H_nonneg q z.2) hl,
    (mul_le_mul_of_nonneg_left hu (H_nonneg q z.2)).trans_eq (mul_comm _ _)⟩

theorem eventually_euclideanHotSource_bound (hcarleman : Published.GPV2009CarlemanInput)
    (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) {κ : ℕ → ℕ} (hκ : StrictMono κ) {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {a A : ℝ} (ha : 0 < a) (haA : a ≤ A) (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ᵐ z ∂(volume : Measure Published.KineticPhase), z.1.1 ∈ Icc a A →
      |S.euclideanHotSource (κ n) z| ≤ sourceEnvelope s₀ η K α γ d₀ q a A z.2*H q z.2 := by
  filter_upwards [S.eventually_rescaledHotSource_abs hcarleman hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hU ha haA hA] with n hn
  filter_upwards [EuclideanFlight.kineticMap_measurePreserving.quasiMeasurePreserving.ae hn]
    with z hz ht
  change |H q z.2*S.rescaledHotSource (κ n) (EuclideanFlight.kineticMap z)| ≤ _
  rw [abs_mul,abs_of_nonneg (H_nonneg q z.2)]
  exact (mul_le_mul_of_nonneg_left (hz ht) (H_nonneg q z.2)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Uniform positive-time bounds for the actual cold-label averages -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelDensity_le_total (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ)
    (x : JetPrototype.Space) (v : Velocity) :
    E.coldLabelDensity k a n t (x,v) ≤ S.rescaledColdDensity (E.indices n) ((t,x),v) := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  let u := (S.radius (E.indices n)*t,(S.radius (E.indices n) • x,v))
  have hs := ((F.approximation (E.indices n)).coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le).2 u
  have hb := hs.1.le_tsum (E.coldLabel k a n) (fun i _ => hc.2.1 i u)
  have hp := mul_le_mul_of_nonneg_left hb
    (mul_nonneg (S.radius_pos hs₀ (E.indices n)).le (H_nonneg q v))
  convert! hp using 1
  · simp only [coldLabelDensity,mul_assoc,u]

theorem HotLimitExtraction.eventually_coldLabelAverage_bound (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {a A B : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hB : 0 ≤ B)
    {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc a A, ∀ k σ x,
      |E.coldLabelAverage k σ n t ψ x| ≤ B*
        (escapedConstant s₀ η K α d₀*hotConstant q+JetEnvelopeGain.momentConstant K α γ/a) := by
  have hM := S.eventually_rescaledColdDensity_moment hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq E.indices_strict E.horizon_limit ha hA
  filter_upwards [hM] with n hn
  intro t ht k σ x
  have hnon (v) := (E.coldLabelDensity_bounds hs₀ hsmax hη hηmax hK hd₀.le hq k σ n t (x,v)).1
  have hm : Measurable (fun v => E.coldLabelDensity k σ n t (x,v)) :=
    (E.coldLabelDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq k σ n t).comp
      (measurable_const.prodMk measurable_id)
  have hmom : VelocityMoment.moment (fun v => E.coldLabelDensity k σ n t (x,v)) ≤
      ENNReal.ofReal (escapedConstant s₀ η K α d₀*hotConstant q+
        JetEnvelopeGain.momentConstant K α γ/a) := by
    apply le_trans _ (hn t ht x)
    apply lintegral_mono
    intro v
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (E.coldLabelDensity_le_total hs₀ hsmax hη hηmax hK hd₀.le hq k σ n t x v)
      (VelocityMoment.weight_pos v).le
  have hM0 : 0 ≤ escapedConstant s₀ η K α d₀*hotConstant q+
      JetEnvelopeGain.momentConstant K α γ/a := add_nonneg
    (mul_nonneg (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _) (hotConstant_nonneg q))
    (div_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ) ha.le)
  exact VelocityMoment.average_le_of_moment_bound hm hnon hB hM0 hmom hψB

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Joint regularity and uniform bounds for the full cold velocity averages -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def coldAverage (S : AttainedCapSequence F) (n : ℕ) (ψ : Velocity → ℝ)
    (x : ℝ × JetPrototype.Space) : ℝ :=
  ∫ v, ψ v*S.rescaledColdDensity n (x,v)

theorem coldAverage_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) : Measurable (S.coldAverage n ψ) := by
  have hm := (hψ.comp measurable_snd).mul
    (S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem coldAverage_global_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : ℝ × JetPrototype.Space) :
    |S.coldAverage n ψ x| ≤
      (B*(S.radius n*(2*(F.approximation n).amplitude)))*(∫ v, H q v) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hb := norm_integral_le_of_norm_le
    (f := fun v => ψ v*S.rescaledColdDensity n (x,v))
    ((integrable_H hq).const_mul (B*(S.radius n*(2*(F.approximation n).amplitude)))) ?_
  · simpa only [Real.norm_eq_abs,integral_const_mul,coldAverage] using hb
  · filter_upwards [] with v
    have hd := S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n (x,v)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hd.1]
    exact (mul_le_mul (hψB v) hd.2 hd.1 hB).trans_eq (by ring)

theorem coldAverage_integrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure ρ] :
    Integrable (S.coldAverage n ψ) ρ :=
  Integrable.of_bound (S.coldAverage_measurable hs₀ hsmax hη hηmax hK hd₀ hq n hψ).aestronglyMeasurable
    _ (ae_of_all _ (S.coldAverage_global_bound hs₀ hsmax hη hηmax hK hd₀ hq n hψB))

theorem HotLimitExtraction.eventually_coldAverage_bound {S : AttainedCapSequence F}
    (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {a A B : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hB : 0 ≤ B)
    {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc a A, ∀ x,
      |S.coldAverage (E.indices n) ψ (t,x)| ≤ B*
        (escapedConstant s₀ η K α d₀*hotConstant q+JetEnvelopeGain.momentConstant K α γ/a) := by
  filter_upwards [S.eventually_rescaledColdDensity_moment hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq E.indices_strict E.horizon_limit ha hA] with n hn
  intro t ht x
  have hm : Measurable (fun v => S.rescaledColdDensity (E.indices n) ((t,x),v)) :=
    (S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀.le hq (E.indices n)).comp
    (measurable_const.prodMk measurable_id)
  have hM0 : 0 ≤ escapedConstant s₀ η K α d₀*hotConstant q+
      JetEnvelopeGain.momentConstant K α γ/a := add_nonneg
    (mul_nonneg (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _) (hotConstant_nonneg q))
    (div_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ) ha.le)
  exact average_le_of_moment_bound hm
    (fun v => (S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀.le hq _ ((t,x),v)).1)
    hB hM0 (hn t ht x) hψB

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Joint time-space regularity of actual cold-label velocity averages -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelDensity_joint_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) :
    Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      E.coldLabelDensity k a n z.1.1 (z.1.2,z.2)) := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hp : Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • z.1.2,z.2))) := by fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).mul
    ((hc.1 (E.coldLabel k a n)).comp hp)).const_mul _

theorem HotLimitExtraction.coldLabelAverage_joint_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun z : ℝ × JetPrototype.Space => E.coldLabelAverage k a n z.1 ψ z.2) := by
  have hm := (hψ.comp measurable_snd).mul
    (E.coldLabelDensity_joint_measurable hs₀ hsmax hη hηmax hK hd₀ hq k a n)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem HotLimitExtraction.coldLabelAverage_global_bound (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B)
    (t : ℝ) (x : JetPrototype.Space) :
    |E.coldLabelAverage k a n t ψ x| ≤
      (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))*(∫ v, H q v) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hb := norm_integral_le_of_norm_le
    (f := fun v => ψ v*E.coldLabelDensity k a n t (x,v))
    ((integrable_H hq).const_mul (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))) ?_
  · simpa only [Real.norm_eq_abs,integral_const_mul,coldLabelAverage] using hb
  · filter_upwards [] with v
    have hd := E.coldLabelDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq k a n t (x,v)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hd.1]
    exact (mul_le_mul (hψB v) hd.2 hd.1 hB).trans_eq (by ring)

theorem HotLimitExtraction.coldLabelAverage_joint_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure ρ] :
    Integrable (fun z => E.coldLabelAverage k a n z.1 ψ z.2) ρ :=
  Integrable.of_bound
    (E.coldLabelAverage_joint_measurable hs₀ hsmax hη hηmax hK hd₀ hq k a n hψ).aestronglyMeasurable
    _ (ae_of_all _ (fun z => E.coldLabelAverage_global_bound hs₀ hsmax hη hηmax hK hd₀ hq k a n hψB z.1 z.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A finite window of actual cold labels -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

def HotLimitExtraction.meshLabels (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ) : Finset JetLattice.Label :=
  ((Finset.Icc L U).product (Finset.univ : Finset Bool)).image (fun p => E.coldLabel p.1 p.2 n)

def HotLimitExtraction.meshCold (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (u : ℝ × JetPrototype.Phase) : ℝ :=
  ∑ i ∈ E.meshLabels n L U, if i.annulus < F.indices (E.indices n) then
    (F.approximation (E.indices n)).cold i u else 0

theorem HotLimitExtraction.meshCold_sum (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (hU : U < GeometricMesh.index (s₀/S.radius (E.indices n)) η) (u : ℝ × JetPrototype.Phase) :
    E.meshCold n L U u = ∑ a : Bool, ∑ k ∈ Finset.Icc L U,
      if (E.coldLabel k a n).annulus < F.indices (E.indices n) then
        (F.approximation (E.indices n)).cold (E.coldLabel k a n) u else 0 := by
  classical
  unfold meshCold meshLabels
  rw [Finset.sum_image]
  · exact (Finset.sum_product _ _ _).trans Finset.sum_comm
  · intro p hp q hq he
    have hj := congrArg JetLattice.Label.annulus he
    have ha := congrArg JetLattice.Label.positive he
    have hpU := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2.trans_lt hU
    have hqU := (Finset.mem_Icc.mp (Finset.mem_product.mp hq).1).2.trans_lt hU
    have hh := congrArg (GeometricMesh.jetMeshIndex s₀ η (S.radius (E.indices n))) hj
    change GeometricMesh.jetMeshIndex s₀ η (S.radius (E.indices n))
        (GeometricMesh.jetIndex s₀ η (fun m => S.radius (E.indices m)) p.1 n) =
      GeometricMesh.jetMeshIndex s₀ η (S.radius (E.indices n))
        (GeometricMesh.jetIndex s₀ η (fun m => S.radius (E.indices m)) q.1 n) at hh
    rw [GeometricMesh.meshIndex_at_jetIndex s₀ η (fun m => S.radius (E.indices m)) n hpU,
      GeometricMesh.meshIndex_at_jetIndex s₀ η (fun m => S.radius (E.indices m)) n hqU] at hh
    exact Prod.ext hh ha

theorem HotLimitExtraction.meshCold_le_total (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (n : ℕ) (L U : ℤ) (u : ℝ × JetPrototype.Phase) :
    E.meshCold n L U u ≤ (F.approximation (E.indices n)).coldTotal u := by
  classical
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hs := ((F.approximation (E.indices n)).coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le).2 u
  apply (Finset.sum_le_sum (s := E.meshLabels n L U) (fun i _ => ?_)).trans
    (hs.1.sum_le_tsum _ (fun i _ => hc.2.1 i u))
  by_cases hi : i.annulus < F.indices (E.indices n)
  · exact (ite_eq_left hi).le
  · rw [ite_eq_right hi]
    exact hc.2.1 i u

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
