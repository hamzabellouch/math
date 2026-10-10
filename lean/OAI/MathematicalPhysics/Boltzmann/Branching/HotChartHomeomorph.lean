import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotSourceIntegrability
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdCentralVanishing

namespace OAI

section

/-! # A bounded Borel hot ratio preserving the actual finite-time traces -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

def boundedHotRatio (S : AttainedCapSequence F) (n : ℕ) (z : KineticPhase) : ℝ :=
  max 0 (min 2 (S.euclideanHot n z/H q z.2))

theorem boundedHotRatio_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.boundedHotRatio n) :=
  measurable_const.max (measurable_const.min
    ((S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).div
      ((ChartKernel.measurable_H q).comp measurable_snd)))

theorem boundedHotRatio_bounds (S : AttainedCapSequence F) (n : ℕ) (z : KineticPhase) :
    0 ≤ S.boundedHotRatio n z ∧ S.boundedHotRatio n z ≤ 2 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem boundedHotRatio_reconstruct (S : AttainedCapSequence F) (n : ℕ) (z : KineticPhase)
    (hn : 0 ≤ S.euclideanHot n z) (hb : S.euclideanHot n z ≤ 2*H q z.2) :
    H q z.2*S.boundedHotRatio n z = S.euclideanHot n z := by
  have hdiv := (div_le_iff₀ (H_pos q z.2)).mpr hb
  rw [boundedHotRatio,min_eq_right hdiv,max_eq_right (div_nonneg hn (H_nonneg q z.2))]
  field_simp [(H_pos q z.2).ne']

theorem euclideanHot_eq_rescaledHot (S : AttainedCapSequence F) (n : ℕ) (z : KineticPhase) :
    S.euclideanHot n z = S.rescaledHot n (z.1.1,EuclideanFlight.phaseEquiv (z.1.2,z.2)) := by
  rw [S.rescaledHot_eq_weighted]
  rfl

theorem boundedHotRatio_preserves_trace (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {t : ℝ}
    (ht : S.radius n*t ∈ Icc 0 (shrinkingHorizon F.horizonScale n)) (htmax : t ≤ 1) :
    ∀ᵐ p : Velocity × Velocity, H q p.2*S.boundedHotRatio n ((t,p.1),p.2) =
      S.euclideanHot n ((t,p.1),p.2) := by
  have hb : ∀ᵐ p : Velocity × Velocity,
      S.rescaledHot n (t,EuclideanFlight.phaseEquiv p) ≤
        (t+S.coldFraction n)*H q p.2 := by
    have h := EuclideanFlight.phaseEquiv_measurePreserving.quasiMeasurePreserving.ae
      (S.rescaledHot_bound_at hs₀ hsmax hη hηmax hK hd₀ hq n ht)
    filter_upwards [h] with p hp
    simpa only [EuclideanFlight.phaseEquiv_apply,JetPeriodicDatum.phaseMap] using hp
  have hc : t+S.coldFraction n ≤ 2 := by linarith [(S.coldFraction_mem hs₀ n).2]
  filter_upwards [hb] with p hp
  have hn : 0 ≤ S.rescaledHot n (t,EuclideanFlight.phaseEquiv p) :=
    S.rescaledHot_nonneg hs₀ hsmax hη hηmax hK hd₀ hq n _
  have hu : S.rescaledHot n (t,EuclideanFlight.phaseEquiv p) ≤ 2*H q p.2 :=
    hp.trans (mul_le_mul_of_nonneg_right hc (H_nonneg q p.2))
  apply S.boundedHotRatio_reconstruct n ((t,p.1),p.2)
  · rw [euclideanHot_eq_rescaledHot]
    exact hn
  · rw [euclideanHot_eq_rescaledHot]
    exact hu

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The bounded hot representative agrees on every admissible time slab -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem boundedHotRatio_preserves_slab (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) {A : ℝ}
    (hA : S.radius n*A ≤ shrinkingHorizon F.horizonScale n) (hAmax : A ≤ 1) :
    (fun z : KineticPhase => H q z.2*S.boundedHotRatio n z) =ᵐ[
      ((volume.restrict (Icc 0 A)).prod (volume : Measure Velocity)).prod volume]
      S.euclideanHot n := by
  let g : ℝ × (Velocity × Velocity) → KineticPhase := fun u => ((u.1,u.2.1),u.2.2)
  have hg : Measurable g := by fun_prop
  have hm : Measurable (fun u : ℝ × (Velocity × Velocity) =>
      H q u.2.2*S.boundedHotRatio n (g u)) :=
    ((ChartKernel.measurable_H q).comp measurable_snd.snd).mul
      ((S.boundedHotRatio_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp hg)
  have he : Measurable (fun u : ℝ × (Velocity × Velocity) => S.euclideanHot n (g u)) :=
    (S.euclideanHot_measurable hs₀ hsmax hη hηmax hK hd₀ hq n).comp hg
  have hprod : (fun u : ℝ × (Velocity × Velocity) => H q u.2.2*S.boundedHotRatio n (g u))
      =ᵐ[(volume.restrict (Icc 0 A)).prod volume] fun u => S.euclideanHot n (g u) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm he)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact S.boundedHotRatio_preserves_trace hs₀ hsmax hη hηmax hK hd₀ hq n
      ⟨mul_nonneg (S.radius_pos hs₀ n).le ht.1,
        (mul_le_mul_of_nonneg_left ht.2 (S.radius_pos hs₀ n).le).trans hA⟩ (ht.2.trans hAmax)
  have hp := measurePreserving_prodAssoc (volume.restrict (Icc 0 A))
    (volume : Measure Velocity) (volume : Measure Velocity)
  filter_upwards [hp.quasiMeasurePreserving.ae hprod] with z hz
  exact hz

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Integral transfer between physical cold cylinders and Euclidean hot tests -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem hotChart_global_measurePreserving : MeasurePreserving hotChart volume volume := by
  have hs : MeasurePreserving spaceEquiv (volume : Measure Velocity) volume := by
    convert JetPeriodicDatum.spatialMap_measurePreserving using 1
    funext x
    exact spaceEquiv_apply x
  have hp : MeasurePreserving hotChart
      (((volume : Measure ℝ).prod (volume : Measure Velocity)).prod volume)
      (((volume : Measure ℝ).prod (volume : Measure JetPrototype.Space)).prod volume) :=
    ((MeasurePreserving.id (volume : Measure ℝ)).prod hs).prod
      (MeasurePreserving.id (volume : Measure Velocity))
  convert hp using 1

theorem integral_hotChart_cylinder {a A R : ℝ}
    {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : ∀ z, z ∉ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R → f z = 0) :
    (∫ z, f (hotChart z)) = ∫ z, f z
      ∂(JetCopyDatum.AttainedCapSequence.coldCylinderVolume a A R).prod volume := by
  rw [hotChart_global_measurePreserving.integral_comp' f,
    JetCopyDatum.AttainedCapSequence.coldCylinderVolume_eq]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hf).symm

end BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hot_transport_cylinder_of_balance (S : AttainedCapSequence F) (n : ℕ)
    {a A R : ℝ} {χ : Published.KineticPhase → ℝ}
    (hs : ∀ z ∈ tsupport χ, EuclideanFlight.hotChart z ∈ coldCylinderSet a A R)
    (hb : (∫ z, transportDerivative χ z*S.euclideanHot n z+χ z*S.euclideanHotSource n z) = 0) :
    (∫ z, transportDerivative χ (EuclideanFlight.hotChart.symm z)*S.physicalHotDensity n z+
      χ (EuclideanFlight.hotChart.symm z)*S.hotSourceDensity a A n z
      ∂(coldCylinderVolume a A R).prod volume) = 0 := by
  let f : HotKineticPhase → ℝ := fun z =>
    transportDerivative χ (EuclideanFlight.hotChart.symm z)*S.physicalHotDensity n z+
      χ (EuclideanFlight.hotChart.symm z)*
        (VelocityWeight.H q z.2*S.rescaledHotSource n (z.1.1,(z.1.2,z.2)))
  have hf (z : HotKineticPhase) (hz : z ∉ coldCylinderSet a A R) : f z = 0 := by
    have hn : EuclideanFlight.hotChart.symm z ∉ tsupport χ := by
      intro h
      exact hz (by simpa only [MeasurableEquiv.apply_symm_apply] using hs _ h)
    dsimp only [f]
    rw [transportDerivative_eq_zero hn,image_eq_zero_of_notMem_tsupport hn,zero_mul,zero_mul,add_zero]
  have hi := EuclideanFlight.integral_hotChart_cylinder hf
  have he : (fun z => f (EuclideanFlight.hotChart z)) =
      (fun z => transportDerivative χ z*S.euclideanHot n z+χ z*S.euclideanHotSource n z) := by
    funext z
    dsimp only [f]
    rw [MeasurableEquiv.symm_apply_apply]
    rw [S.euclideanHot_eq_chart]
    rfl
  rw [he,hb] at hi
  calc
    _ = ∫ z, f z ∂(coldCylinderVolume a A R).prod volume := by
      apply integral_congr_ae
      rw [coldCylinderVolume_eq]
      filter_upwards [ae_restrict_mem (coldCylinderSet_measurable a A R)] with z hz
      dsimp only [f]
      rw [hotSourceDensity,indicator_of_mem
        (show z ∈ {z : HotKineticPhase | z.1.1 ∈ Icc a A} from hz.1.1)]
    _ = 0 := hi.symm

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Topological transport of compact kinetic tests through the hot chart -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem spaceEquiv_continuous : Continuous spaceEquiv := by
  change Continuous (fun x => spaceEquiv x)
  simp only [spaceEquiv_apply,JetPeriodicDatum.spatialMap]
  unfold transverse axial
  fun_prop

theorem spaceEquiv_symm_components (x : JetPrototype.Space) :
    transverse (spaceEquiv.symm x) = x.1 ∧ axial (spaceEquiv.symm x) = x.2 := by
  have h := spaceEquiv.apply_symm_apply x
  rw [spaceEquiv_apply] at h
  change (transverse (spaceEquiv.symm x), axial (spaceEquiv.symm x)) = x at h
  constructor
  · exact @congrArg JetPrototype.Space _
      (transverse (spaceEquiv.symm x), axial (spaceEquiv.symm x)) x (fun p => p.1) h
  · exact @congrArg JetPrototype.Space ℝ
      (transverse (spaceEquiv.symm x), axial (spaceEquiv.symm x)) x (fun p => p.2) h

theorem spaceEquiv_symm_lipschitz : LipschitzWith 2 spaceEquiv.symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm]
  change ‖spaceEquiv.symm x-spaceEquiv.symm y‖ ≤ 2*‖x-y‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hn := norm_sq_split (spaceEquiv.symm x-spaceEquiv.symm y)
  rw [PlaneChart.transverse_sub,PlaneChart.axial_sub,
    (spaceEquiv_symm_components x).1,(spaceEquiv_symm_components y).1,
    (spaceEquiv_symm_components x).2,(spaceEquiv_symm_components y).2] at hn
  have hx : ‖x.1-y.1‖ ≤ ‖x-y‖ := norm_fst_le (x-y)
  have hy : ‖x.2-y.2‖ ≤ ‖x-y‖ := norm_snd_le (x-y)
  have hx2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx
  have hy2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy
  rw [Real.norm_eq_abs,sq_abs] at hy2
  nlinarith [sq_nonneg ‖x-y‖]

def hotHomeomorph : Published.KineticPhase ≃ₜ JetCopyDatum.AttainedCapSequence.HotKineticPhase where
  toEquiv := hotChart.toEquiv
  continuous_toFun := by
    change Continuous (fun z : Published.KineticPhase => ((z.1.1,spaceEquiv z.1.2),z.2))
    exact (continuous_fst.fst.prodMk (spaceEquiv_continuous.comp continuous_fst.snd)).prodMk
      continuous_snd
  continuous_invFun := by
    change Continuous (fun z : JetCopyDatum.AttainedCapSequence.HotKineticPhase =>
      ((z.1.1,spaceEquiv.symm z.1.2),z.2))
    exact (continuous_fst.fst.prodMk
      (spaceEquiv_symm_lipschitz.continuous.comp continuous_fst.snd)).prodMk continuous_snd

theorem hotChart_symm_continuous : Continuous hotChart.symm := hotHomeomorph.symm.continuous

theorem compact_test_hotChart {χ : Published.KineticPhase → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (fun z => χ (hotChart.symm z)) :=
  hc.comp_homeomorph hotHomeomorph.symm

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
