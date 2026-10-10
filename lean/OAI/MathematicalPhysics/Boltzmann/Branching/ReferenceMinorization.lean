import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceAngularCharts
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral

namespace OAI

section

/-! # The physical two-collision law bounds the small four-angle window -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem familyWindow_subset {a δ d : ℝ} (hδ : δ ≤ a) (ha : a ≤ d) :
    Ioo (-δ) δ ×ˢ ball (0 : V) a ⊆ familyCoordinates ⁻¹' (angularSquare d ×ˢ angularSquare d) := by
  rintro ⟨t,z⟩ ⟨ht,hz⟩
  have hn : ‖z‖ < a := by simpa only [mem_ball,dist_zero_right] using hz
  have hi (i : Fin 3) : -d < z i ∧ z i < d :=
    abs_lt.mp ((PiLp.norm_apply_le z i).trans_lt (hn.trans_le ha))
  change ((-d < t ∧ t < d) ∧ (-d < z 0 ∧ z 0 < d)) ∧
    (-d < z 1 ∧ z 1 < d) ∧ (-d < z 2 ∧ z 2 < d)
  exact ⟨⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,hi 0⟩,hi 1,hi 2⟩

theorem familyWindowMap_le {a δ d : ℝ} {C : ℝ≥0∞} (hδ : δ ≤ a) (ha : a ≤ d)
    (hCt : C ≠ ⊤)
    (hout : (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability)
    (hin : (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability)
    (v : V) :
    (familyWindowMeasure a δ).map (familyWindowMap v) ≤ C^2 • twoCollisionLaw v := by
  let B := angularSquare d ×ˢ angularSquare d
  have hB : MeasurableSet B :=
    (measurableSet_Ioo.prod measurableSet_Ioo).prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hmap : (volume.restrict (familyCoordinates ⁻¹' B)).map familyCoordinates =
      (volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d)) := by
    rw [(familyCoordinates_measurePreserving.restrict_preimage hB).map_eq,Measure.prod_restrict]
    rfl
  have hle : familyWindowMeasure a δ ≤ volume.restrict (familyCoordinates ⁻¹' B) := by
    rw [familyWindowMeasure,Measure.prod_restrict]
    exact Measure.restrict_mono (familyWindow_subset hδ ha) le_rfl
  have hf : familyWindowMap v = familyChart v ∘ familyCoordinates := by
    funext w
    exact (familyChart_coordinates v w.1 w.2).symm
  apply (Measure.map_mono hle (familyWindowMap_measurable v)).trans
  rw [hf,← Measure.map_map (familyChart_measurable v) familyCoordinates.measurable,hmap]
  exact familyChart_measure_le hCt hout hin v

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform volume domination by two actual outgoing-sphere collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem twoCollisionLaw_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v ∈ ball beamAxis δ,
        volume.restrict (ball (0 : V) δ) ≤ B • twoCollisionLaw v := by
  obtain ⟨d,C,hd,hC0,hCt,hout,hin⟩ := paired_parameterSphere_dominated
  obtain ⟨a,δ,K,_ha,had,hδ,hδa,hK,hvolume⟩ := uniform_family_window_volume hd
  let I := ENNReal.ofReal (2*δ)
  let B := I⁻¹ * (K : ℝ≥0∞)^3 * C^2
  have hI0 : I ≠ 0 := by dsimp [I]; positivity
  have hIt : I ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKn : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hB0 : B ≠ 0 := mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt)
    (pow_ne_zero 3 hKn)) (pow_ne_zero 2 hC0)
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0) (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (ENNReal.pow_ne_top hCt)
  refine ⟨δ,B,hδ,hB0,hBt,?_⟩
  intro v hv
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul]
  have hlower := hvolume v hv (A ∩ ball (0 : V) δ) (hA.inter measurableSet_ball) inter_subset_right
  have hupper := familyWindowMap_le hδa had hCt hout hin v
  have hAupper : ((familyWindowMeasure a δ).map (familyWindowMap v)) (A ∩ ball (0 : V) δ) ≤
      C^2 * twoCollisionLaw v A := by
    exact (hupper _).trans (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have htotal : I * volume (A ∩ ball (0 : V) δ) ≤
      (K : ℝ≥0∞)^3 * (C^2 * twoCollisionLaw v A) := by
    exact hlower.trans (by gcongr)
  calc
    volume (A ∩ ball (0 : V) δ) = I⁻¹ * (I * volume (A ∩ ball (0 : V) δ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹ * ((K : ℝ≥0∞)^3 * (C^2 * twoCollisionLaw v A)) := by gcongr
    _ = B * twoCollisionLaw v A := by simp only [B,mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The angular window is dominated while retaining its intermediate-velocity support -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def familyWindowAngles (w : ℝ × V) : Sphere × Sphere :=
  (incomingParameterSphere (w.1,w.2 0),parameterSphere (w.2 1,w.2 2))

theorem familyWindowAngles_measurable : Measurable familyWindowAngles := by
  exact (incomingParameterSphere_measurable.comp (by fun_prop)).prodMk
    (parameterSphere_measurable.comp (by fun_prop))

def firstAngleSet (v : V) : Set (Sphere × Sphere) :=
  {p | child v (-beamAxis) (p.1 : V) ∈ localCollisionCore}

theorem firstAngleSet_measurable (v : V) : MeasurableSet (firstAngleSet v) := by
  apply localCollisionCore_measurable.preimage
  unfold child
  fun_prop

def localTwoCollisionLaw (v : V) : Measure V :=
  ((sphereProbability.prod sphereProbability).restrict (firstAngleSet v)).map (twoCollisionMap v)

theorem familyWindowAngles_le {a δ d : ℝ} {C : ℝ≥0∞} (hδ : δ ≤ a) (ha : a ≤ d)
    (hCt : C ≠ ⊤)
    (hout : (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability)
    (hin : (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability) :
    (familyWindowMeasure a δ).map familyWindowAngles ≤ C^2 • sphereProbability.prod sphereProbability := by
  let B := angularSquare d ×ˢ angularSquare d
  have hB : MeasurableSet B :=
    (measurableSet_Ioo.prod measurableSet_Ioo).prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hmap : (volume.restrict (familyCoordinates ⁻¹' B)).map familyCoordinates =
      (volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d)) := by
    rw [(familyCoordinates_measurePreserving.restrict_preimage hB).map_eq,Measure.prod_restrict]
    rfl
  have hle : familyWindowMeasure a δ ≤ volume.restrict (familyCoordinates ⁻¹' B) := by
    rw [familyWindowMeasure,Measure.prod_restrict]
    exact Measure.restrict_mono (familyWindow_subset hδ ha) le_rfl
  have hf : familyWindowAngles =
      (fun p => (incomingParameterSphere p.1,parameterSphere p.2)) ∘ familyCoordinates := rfl
  have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (incomingParameterSphere p.1,parameterSphere p.2)) :=
    incomingParameterSphere_measurable.prodMap parameterSphere_measurable
  apply (Measure.map_mono hle familyWindowAngles_measurable).trans
  rw [hf,← Measure.map_map hm familyCoordinates.measurable,hmap]
  change ((volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d))).map
    (Prod.map incomingParameterSphere parameterSphere) ≤ _
  rw [← Measure.map_prod_map _ _ incomingParameterSphere_measurable parameterSphere_measurable]
  have : IsFiniteMeasure (C • sphereProbability) := ⟨by
    rw [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact hCt.lt_top⟩
  have hh := Measure.prod_mono hin hout
  rwa [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,← pow_two] at hh

theorem familyWindowAngles_mem {ε a δ : ℝ} (ha : a ≤ ε) (hδ : δ ≤ a)
    (hgood : ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore)
    {v : V} (hv : v ∈ ball beamAxis δ) :
    ∀ᵐ p ∂(familyWindowMeasure a δ).map familyWindowAngles, p ∈ firstAngleSet v := by
  apply (ae_map_iff familyWindowAngles_measurable.aemeasurable (firstAngleSet_measurable v)).mpr
  have hmem : ∀ᵐ w ∂familyWindowMeasure a δ, w ∈ Ioo (-δ) δ ×ˢ ball (0 : V) a := by
    rw [familyWindowMeasure,Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_ball)
  filter_upwards [hmem] with w hw
  have hh := familyWindow_good ha hδ hgood hv hw.1 hw.2
  change child v (-beamAxis) (incomingParameterSphere (w.1,w.2 0) : V) ∈ localCollisionCore
  rw [incomingParameterSphere_value]
  exact hh

theorem familyWindowMap_local_le {ε a δ d : ℝ} {C : ℝ≥0∞}
    (haε : a ≤ ε) (hδ : δ ≤ a) (ha : a ≤ d) (hCt : C ≠ ⊤)
    (hgood : ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore)
    (hout : (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability)
    (hin : (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability)
    {v : V} (hv : v ∈ ball beamAxis δ) :
    (familyWindowMeasure a δ).map (familyWindowMap v) ≤ C^2 • localTwoCollisionLaw v := by
  have hmem := familyWindowAngles_mem haε hδ hgood hv
  have hre : ((familyWindowMeasure a δ).map familyWindowAngles).restrict (firstAngleSet v) =
      (familyWindowMeasure a δ).map familyWindowAngles := Measure.restrict_eq_self_of_ae_mem hmem
  have hle : (familyWindowMeasure a δ).map familyWindowAngles ≤
      C^2 • (sphereProbability.prod sphereProbability).restrict (firstAngleSet v) := by
    conv_lhs => rw [← hre]
    exact (Measure.restrict_mono (Subset.rfl) (familyWindowAngles_le hδ ha hCt hout hin)).trans_eq
      (Measure.restrict_smul _ _ _)
  have hh := Measure.map_mono hle (twoCollisionMap_measurable v)
  rw [Measure.map_map (twoCollisionMap_measurable v) familyWindowAngles_measurable,
    Measure.map_smul] at hh
  · have heq : twoCollisionMap v ∘ familyWindowAngles = familyWindowMap v := by
      funext w
      exact familyChart_coordinates v w.1 w.2
    simpa only [heq,localTwoCollisionLaw] using hh
  · exact (twoCollisionMap_measurable v).aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform entry into an arbitrarily small neighborhood of the positive beam -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamEntryMass (δ : ℝ) : ℝ := (δ/24)*sphereCapMass (δ/12)

theorem beamEntryMass_pos {δ : ℝ} (hδ : 0 < δ) : 0 < beamEntryMass δ :=
  mul_pos (div_pos hδ (by norm_num)) (sphereCapMass_pos (by positivity))

theorem reference_beam_entry {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/4)
    (v : V) (hv : ‖v‖ ≤ 5) :
    beamEntryMass δ ≤ (referenceJump beamAxis v).real (Metric.ball beamAxis δ) := by
  have he := axis_norms.2.2
  have hden : ‖v-beamAxis‖+‖v+beamAxis‖ ≤ 12 := by
    have hm := norm_sub_le v beamAxis
    have hp := norm_add_le v beamAxis
    rw [he] at hm hp
    linarith
  have hpos : 0 < ‖v-beamAxis‖+‖v+beamAxis‖ :=
    lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v beamAxis he)
  have hcap : 0 ≤ sphereCapMass (δ/12) := (sphereCapMass_pos (by positivity)).le
  rw [referenceJump_real]
  by_cases hd : δ/2 ≤ ‖v-beamAxis‖
  · have hne : v-beamAxis ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith))
    let n : Sphere := ⟨-normalize (v-beamAxis),mem_sphere_zero_iff_norm.mpr
      (by rw [norm_neg,norm_normalize hne])⟩
    have hn : child v beamAxis n.1 = beamAxis := (child_normalized_endpoints v beamAxis).2
    have hout := outgoing_endpoint_cap hδ v beamAxis beamAxis he hv n (by rw [hn,dist_self]; positivity)
    have hp : δ/24 ≤ plusProbability beamAxis v := by
      rw [plusProbability,le_div_iff₀ hpos]
      nlinarith
    have hh := mul_le_mul hp hout hcap (plusProbability_mem beamAxis v).1
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg
      (sub_nonneg.mpr (plusProbability_mem beamAxis v).2) measureReal_nonneg))
  · have hnear : v ∈ Metric.ball beamAxis (1/4) := by
      change dist v beamAxis < 1/4
      rw [dist_eq_norm]
      have hd' := lt_of_not_ge hd
      linarith
    have hdist := beam_neighborhood_distance hnear
    have hne : v-(-beamAxis) ≠ 0 := by
      rw [sub_neg_eq_add]
      exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
    let n : Sphere := ⟨normalize (v-(-beamAxis)),mem_sphere_zero_iff_norm.mpr (norm_normalize hne)⟩
    have hn : child v (-beamAxis) n.1 = v := (child_normalized_endpoints v (-beamAxis)).1
    have hout := outgoing_endpoint_cap hδ v (-beamAxis) beamAxis (by simpa using he) hv n (by
      rw [hn,dist_eq_norm]
      exact le_of_lt (lt_of_not_ge hd))
    have hp : δ/24 ≤ 1-plusProbability beamAxis v := by
      rw [minusProbability_eq beamAxis v he,le_div_iff₀ hpos]
      nlinarith
    have hh := mul_le_mul hp hout hcap (sub_nonneg.mpr (plusProbability_mem beamAxis v).2)
    exact hh.trans (le_add_of_nonneg_left (mul_nonneg (plusProbability_mem beamAxis v).1
      measureReal_nonneg))

theorem retained_beam_entry {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/4)
    (v : V) (hv : ‖v‖ ≤ 5) :
    beamEntryMass δ ≤ (retainedJump beamAxis v).real (Metric.ball beamAxis δ) := by
  have he := axis_norms.2.2
  have hp0 : 0 < (retention beamAxis v).toReal :=
    ENNReal.toReal_pos (retention_ne_zero_coarse beamAxis v he hv) (retention_ne_top beamAxis v)
  have hp1 := (retention_toReal_mem beamAxis v).2
  have hsub : Metric.ball beamAxis δ ⊆ referenceRegion := by
    intro w hw
    have ht := dist_triangle w beamAxis (0 : V)
    rw [dist_zero_right,dist_zero_right,he] at ht
    change dist w 0 ≤ 5
    rw [dist_zero_right]
    have hd : dist w beamAxis < δ := hw
    linarith
  rw [Measure.real,retainedJump_apply,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_inv,Measure.restrict_apply measurableSet_ball,inter_eq_left.mpr hsub]
  change beamEntryMass δ ≤ (retention beamAxis v).toReal⁻¹*
    (referenceJump beamAxis v).real (Metric.ball beamAxis δ)
  rw [inv_mul_eq_div]
  apply (reference_beam_entry hδ hδsmall v hv).trans
  apply (le_div_iff₀ hp0).mpr
  exact mul_le_of_le_one_right measureReal_nonneg hp1

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Two retained jumps enter a transverse velocity ball uniformly -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem retained_transverse_entry_local {ζ δ : ℝ} (hζ : 0 < ζ) (hδζ : δ ≤ ζ/2)
    (hδ : δ ≤ 1/4) {v : V} (hv : v ∈ ball beamAxis δ) :
    sphereCapMass (ζ/12)/6 ≤ (retainedJump beamAxis v).real (ball firstAxis ζ) := by
  have hv' : v ∈ ball beamAxis (1/4) := ball_subset_ball hδ hv
  have hv2 := norm_le_two_of_near_unit axis_norms.2.2 hv'
  have hp := minusProbability_lower_small beamAxis v axis_norms.2.2 hv2 (beam_neighborhood_distance hv')
  let n : Sphere := ⟨firstAxis,mem_sphere_zero_iff_norm.mpr axis_norms.1⟩
  have hn : dist (child v (-beamAxis) n.1) firstAxis ≤ ζ/2 := by
    have hh := child_lipschitz v (-beamAxis) beamAxis (-beamAxis) firstAxis axis_norms.1
    rw [child_opposite_beam,sub_self,norm_zero,add_zero] at hh
    exact (show dist (child v (-beamAxis) n.1) firstAxis ≤ dist v beamAxis from hh).trans
      (le_trans (le_of_lt hv) hδζ)
  have ho := outgoing_endpoint_cap hζ v (-beamAxis) firstAxis
    (by simpa using axis_norms.2.2) (by linarith : ‖v‖ ≤ 5) n hn
  rw [retainedJump_small beamAxis v axis_norms.2.2 (by linarith),referenceJump_real]
  have hc := (sphereCapMass_pos (by positivity : 0 < ζ/12)).le
  have hh := mul_le_mul hp ho hc (sub_nonneg.mpr (plusProbability_mem beamAxis v).2)
  have hn' := mul_nonneg (plusProbability_mem beamAxis v).1
    (measureReal_nonneg (μ := outgoing (v,beamAxis)) (s := ball firstAxis ζ))
  linarith

theorem retained_two_transverse_entry {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ v : V, ‖v‖ ≤ 5 →
      c ≤ (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v (ball firstAxis ζ) := by
  let δ := min (ζ/2) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  let I := ENNReal.ofReal (beamEntryMass δ)
  let J := ENNReal.ofReal (sphereCapMass (ζ/12)/6)
  have hI : I ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (beamEntryMass_pos hδ))
  have hJ : J ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by
    exact div_pos (sphereCapMass_pos (by positivity)) (by norm_num)))
  refine ⟨I*J,mul_ne_zero hI hJ,ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,?_⟩
  intro v hv
  have hentry : I ≤ retainedJump beamAxis v (ball beamAxis δ) :=
    (ENNReal.ofReal_le_ofReal (retained_beam_entry hδ (min_le_right _ _) v hv)).trans
      ENNReal.ofReal_toReal_le
  have hlocal (u : V) (hu : u ∈ ball beamAxis δ) :
      J ≤ retainedJump beamAxis u (ball firstAxis ζ) :=
    (ENNReal.ofReal_le_ofReal (retained_transverse_entry_local hζ (min_le_left _ _)
      (min_le_right _ _) hu)).trans ENNReal.ofReal_toReal_le
  calc
    I*J ≤ retainedJump beamAxis v (ball beamAxis δ)*J := mul_le_mul' hentry le_rfl
    _ = ∫⁻ _u in ball beamAxis δ, J ∂retainedJump beamAxis v := by
      rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ∫⁻ u in ball beamAxis δ, retainedJump beamAxis u (ball firstAxis ζ)
        ∂retainedJump beamAxis v := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
      exact hlocal u hu
    _ ≤ ∫⁻ u, retainedJump beamAxis u (ball firstAxis ζ) ∂retainedJump beamAxis v :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := (Kernel.comp_apply' _ _ _ measurableSet_ball).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Each selected small-velocity collision is dominated by the retained jump -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_plus_le_retained (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v-e‖) : outgoing (v,e) ≤ (6 : ℝ≥0∞) • retainedJump e v := by
  have hw : (1 : ℝ≥0∞) ≤ 6*ENNReal.ofReal (plusProbability e v) := by
    have hh := ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 6*plusProbability e v by
      linarith [plusProbability_lower_small e v he hv hr])
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using hh
  rw [retainedJump_small e v he (hv.trans (by norm_num)),referenceJump_measure]
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  calc
    outgoing (v,e) A = 1*outgoing (v,e) A := (one_mul _).symm
    _ ≤ (6*ENNReal.ofReal (plusProbability e v))*outgoing (v,e) A := mul_le_mul' hw le_rfl
    _ ≤ _ := by rw [mul_assoc,mul_add]; exact le_add_right le_rfl

theorem outgoing_minus_le_retained (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v+e‖) : outgoing (v,-e) ≤ (6 : ℝ≥0∞) • retainedJump e v := by
  have hw : (1 : ℝ≥0∞) ≤ 6*ENNReal.ofReal (1-plusProbability e v) := by
    have hh := ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 6*(1-plusProbability e v) by
      linarith [minusProbability_lower_small e v he hv hr])
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using hh
  rw [retainedJump_small e v he (hv.trans (by norm_num)),referenceJump_measure]
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  calc
    outgoing (v,-e) A = 1*outgoing (v,-e) A := (one_mul _).symm
    _ ≤ (6*ENNReal.ofReal (1-plusProbability e v))*outgoing (v,-e) A := mul_le_mul' hw le_rfl
    _ ≤ _ := by rw [mul_assoc,mul_add]; exact le_add_left le_rfl

theorem localCollisionCore_jump_bound {u : V} (hu : u ∈ localCollisionCore) :
    outgoing (u,beamAxis) ≤ (6 : ℝ≥0∞) • retainedJump beamAxis u :=
  outgoing_plus_le_retained _ _ axis_norms.2.2 (localCollisionCore_norm hu)
    (localCollisionCore_distance hu)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Two selected collisions are dominated by two retained reference jumps -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localTwoCollisionLaw_apply (v : V) {A : Set V} (hA : MeasurableSet A) :
    localTwoCollisionLaw v A =
      ∫⁻ u in localCollisionCore, outgoing (u,beamAxis) A ∂outgoing (v,-beamAxis) := by
  have hm : Measurable (fun n : Sphere => child v (-beamAxis) n.1) := by
    unfold child
    fun_prop
  have hq : Measurable (fun u : V => outgoing (u,beamAxis) A) :=
    (outgoing.measurable_coe hA).comp (measurable_id.prodMk measurable_const)
  rw [localTwoCollisionLaw,Measure.map_apply (twoCollisionMap_measurable v) hA,
    Measure.restrict_apply ((twoCollisionMap_measurable v) hA),
    Measure.prod_apply (((twoCollisionMap_measurable v) hA).inter (firstAngleSet_measurable v)),
    ← lintegral_indicator localCollisionCore_measurable,outgoing_apply,
    lintegral_map (hq.indicator localCollisionCore_measurable) hm]
  apply lintegral_congr
  intro n
  by_cases hn : child v (-beamAxis) n.1 ∈ localCollisionCore
  · rw [indicator_of_mem hn,outgoing_apply,
      Measure.map_apply (by unfold child; fun_prop) hA]
    congr 1
    ext m
    simp only [mem_preimage,mem_inter_iff,firstAngleSet,mem_ofPred_eq,twoCollisionMap,hn,and_true]
  · rw [indicator_of_notMem hn]
    have hz : Prod.mk n ⁻¹' (twoCollisionMap v ⁻¹' A ∩ firstAngleSet v) = ∅ := by
      ext m
      simp only [mem_preimage,mem_inter_iff,firstAngleSet,mem_ofPred_eq,hn,and_false,mem_empty_iff_false]
    rw [hz,measure_empty]

theorem localTwoCollisionLaw_le_retained {v : V} (hv : v ∈ Metric.ball beamAxis (1/4)) :
    localTwoCollisionLaw v ≤ (36 : ℝ≥0∞) •
      (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v := by
  have hm := outgoing_minus_le_retained beamAxis v axis_norms.2.2
    (norm_le_two_of_near_unit axis_norms.2.2 hv) (beam_neighborhood_distance hv)
  apply Measure.le_iff.mpr
  intro A hA
  rw [localTwoCollisionLaw_apply v hA,Measure.smul_apply,smul_eq_mul,
    Kernel.comp_apply' _ _ _ hA]
  calc
    (∫⁻ u in localCollisionCore, outgoing (u,beamAxis) A ∂outgoing (v,-beamAxis)) ≤
        ∫⁻ u in localCollisionCore, (6 : ℝ≥0∞)*retainedJump beamAxis u A ∂outgoing (v,-beamAxis) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem localCollisionCore_measurable] with u hu
      exact localCollisionCore_jump_bound hu A
    _ ≤ ∫⁻ u, (6 : ℝ≥0∞)*retainedJump beamAxis u A ∂outgoing (v,-beamAxis) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ∫⁻ u, (6 : ℝ≥0∞)*retainedJump beamAxis u A ∂((6 : ℝ≥0∞) • retainedJump beamAxis v) :=
      lintegral_mono' hm le_rfl
    _ = _ := by
      rw [lintegral_smul_measure,lintegral_const_mul' _ _ (by norm_num)]
      simp only [smul_eq_mul,← mul_assoc]
      norm_num

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform volume domination by two retained reference jumps near the beam -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem retained_two_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v ∈ ball beamAxis δ,
        volume.restrict (ball (0 : V) δ) ≤ B •
          (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v := by
  obtain ⟨d,C,hd,hC0,hCt,hout,hin⟩ := paired_parameterSphere_dominated
  obtain ⟨ε,hε,hεsmall,hgood⟩ := collision_window_good
  obtain ⟨a,δ,K,_ha,hab,hδ,hδa,hK,hvolume⟩ :=
    uniform_family_window_volume (lt_min hd hε)
  have had := hab.trans (min_le_left _ _)
  have haε := hab.trans (min_le_right _ _)
  have hδsmall := hδa.trans (haε.trans hεsmall)
  let I := ENNReal.ofReal (2*δ)
  let B := I⁻¹ * (K : ℝ≥0∞)^3 * (C^2*36)
  have hI0 : I ≠ 0 := by dsimp [I]; positivity
  have hIt : I ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKn : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hB0 : B ≠ 0 := mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt)
    (pow_ne_zero 3 hKn)) (mul_ne_zero (pow_ne_zero 2 hC0) (by norm_num))
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0) (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hCt) (by norm_num))
  refine ⟨δ,B,hδ,hδsmall,hB0,hBt,?_⟩
  intro v hv
  have hvsmall : v ∈ ball beamAxis (1/4) := (ball_subset_ball hδsmall) hv
  have hupper := (familyWindowMap_local_le haε hδa had hCt hgood hout hin hv).trans
    (smul_le_smul_left (C^2) (localTwoCollisionLaw_le_retained hvsmall))
  rw [smul_smul] at hupper
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul]
  have hlower := hvolume v hv (A ∩ ball (0 : V) δ) (hA.inter measurableSet_ball) inter_subset_right
  have hAupper : ((familyWindowMeasure a δ).map (familyWindowMap v)) (A ∩ ball (0 : V) δ) ≤
      (C^2*36) * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A := by
    exact (hupper _).trans (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have htotal : I * volume (A ∩ ball (0 : V) δ) ≤ (K : ℝ≥0∞)^3 *
      ((C^2*36) * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A) := by
    exact hlower.trans (by gcongr)
  calc
    volume (A ∩ ball (0 : V) δ) = I⁻¹ * (I * volume (A ∩ ball (0 : V) δ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹ * ((K : ℝ≥0∞)^3 *
        ((C^2*36) * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A)) := by gcongr
    _ = B * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A := by simp only [B,mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform three-jump minorization on the full retained velocity region -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem retained_three_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v ∈ referenceRegion,
        volume.restrict (ball (0 : V) δ) ≤ B •
          ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) v := by
  obtain ⟨δ,C,hδ,hδsmall,hC0,hCt,hlocal⟩ := retained_two_volume_domination
  let I := ENNReal.ofReal (beamEntryMass δ)
  have hI0 : I ≠ 0 := by dsimp [I]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (beamEntryMass_pos hδ))
  have hIt : I ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨δ,I⁻¹*C,hδ,hδsmall,mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt) hC0,
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0) hCt,?_⟩
  intro v hv
  have hvnorm : ‖v‖ ≤ 5 := by simpa only [referenceRegion,mem_closedBall,dist_zero_right] using hv
  have hentry : I ≤ retainedJump beamAxis v (ball beamAxis δ) := by
    exact (ENNReal.ofReal_le_ofReal (retained_beam_entry hδ hδsmall v hvnorm)).trans
      ENNReal.ofReal_toReal_le
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul]
  have hbound (u : V) (hu : u ∈ ball beamAxis δ) :
      volume (A ∩ ball (0 : V) δ) ≤
        C*(retainedJump beamAxis ∘ₖ retainedJump beamAxis) u A := by
    have hh := hlocal u hu A
    simpa only [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul] using hh
  have htotal : I*volume (A ∩ ball (0 : V) δ) ≤ C*
      ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) v A := by
    calc
      I*volume (A ∩ ball (0 : V) δ) ≤
          retainedJump beamAxis v (ball beamAxis δ)*volume (A ∩ ball (0 : V) δ) :=
        mul_le_mul' hentry le_rfl
      _ = ∫⁻ _u in ball beamAxis δ, volume (A ∩ ball (0 : V) δ) ∂retainedJump beamAxis v := by
        rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
      _ ≤ ∫⁻ u in ball beamAxis δ,
          C*(retainedJump beamAxis ∘ₖ retainedJump beamAxis) u A ∂retainedJump beamAxis v := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
        exact hbound u hu
      _ ≤ ∫⁻ u, C*(retainedJump beamAxis ∘ₖ retainedJump beamAxis) u A ∂retainedJump beamAxis v :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = _ := by rw [lintegral_const_mul' _ _ hCt,Kernel.comp_apply' _ _ _ hA]
  calc
    volume (A ∩ ball (0 : V) δ) = I⁻¹*(I*volume (A ∩ ball (0 : V) δ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹*(C*
        ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) v A) := by gcongr
    _ = _ := by rw [mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The retained reference law as a Markov kernel on its bounded state space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev RetainedState := {v : V // v ∈ referenceRegion}

theorem retainedState_norm (v : RetainedState) : ‖(v : V)‖ ≤ 5 := by
  simpa only [referenceRegion,Metric.mem_closedBall,dist_zero_right] using v.2

def stateKernel : Kernel RetainedState RetainedState :=
  ((retainedJump beamAxis).comap (Subtype.val : RetainedState → V) measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe referenceRegion_measurable)

instance stateKernel_isMarkov : IsMarkovKernel stateKernel := by
  apply Kernel.IsMarkovKernel.comapRight
  intro v
  rw [Kernel.comap_apply,Subtype.range_coe]
  exact retainedJump_region _ _ (retention_ne_zero_coarse _ _ axis_norms.2.2 (retainedState_norm v))

theorem stateKernel_apply (v : RetainedState) :
    stateKernel v = (retainedJump beamAxis v.1).comap (Subtype.val : RetainedState → V) := rfl

theorem stateKernel_map (v : RetainedState) :
    (stateKernel v).map (Subtype.val : RetainedState → V) = retainedJump beamAxis v.1 := by
  rw [stateKernel_apply,map_comap_subtype_coe referenceRegion_measurable]
  have hn := retention_ne_zero_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v)
  have : IsProbabilityMeasure (retainedJump beamAxis v.1) :=
    ⟨retainedJump_univ _ _ hn⟩
  exact Measure.restrict_eq_self_of_ae_mem
    ((mem_ae_iff_prob_eq_one referenceRegion_measurable).mpr (retainedJump_region _ _ hn))

theorem stateKernel_integral (v : RetainedState) {f : V → ℝ}
    (hf : AEStronglyMeasurable f (retainedJump beamAxis v.1)) :
    ∫ u, f u.1 ∂stateKernel v = ∫ u, f u ∂retainedJump beamAxis v.1 := by
  rw [← stateKernel_map v]
  exact (integral_map measurable_subtype_coe.aemeasurable (by rwa [stateKernel_map])).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A constant-rate uniformization of the retained velocity dynamics -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def stateRate (v : RetainedState) : ℝ := retainedRate beamAxis v.1

def jumpFraction (v : RetainedState) : ℝ := stateRate v/(48*Real.pi)

theorem stateRate_measurable : Measurable stateRate := by
  unfold stateRate retainedRate
  exact ((measurable_const.mul ((retention_measurable beamAxis).comp
    measurable_subtype_coe).ennreal_toReal).mul (by unfold frequency; fun_prop))

theorem stateRate_bounds (v : RetainedState) : 4*Real.pi ≤ stateRate v ∧ stateRate v ≤ 48*Real.pi := by
  have hp := retainedPotential_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v)
  have hf := frequency_lower v.1 beamAxis axis_norms.2.2
  dsimp only [retainedPotential] at hp
  exact ⟨by dsimp [stateRate]; linarith [Real.pi_pos],
    retainedRate_le _ _ axis_norms.2.2 (retainedState_norm v)⟩

theorem jumpFraction_measurable : Measurable jumpFraction := stateRate_measurable.div_const _

theorem jumpFraction_bounds (v : RetainedState) : (1/12 : ℝ) ≤ jumpFraction v ∧ jumpFraction v ≤ 1 := by
  have hb := stateRate_bounds v
  constructor
  · rw [jumpFraction,le_div_iff₀ (by positivity : 0 < 48*Real.pi)]
    linarith [hb.1]
  · rw [jumpFraction,div_le_one (by positivity : 0 < 48*Real.pi)]
    exact hb.2

def uniformizedKernel : Kernel RetainedState RetainedState :=
  Kernel.withDensity stateKernel (fun v _ => ENNReal.ofReal (jumpFraction v)) +
    Kernel.withDensity Kernel.id (fun v _ => ENNReal.ofReal (1-jumpFraction v))

theorem uniformizedKernel_apply (v : RetainedState) : uniformizedKernel v =
    ENNReal.ofReal (jumpFraction v) • stateKernel v +
      ENNReal.ofReal (1-jumpFraction v) • Measure.dirac v := by
  have hp : Measurable (Function.uncurry (fun v (_ : RetainedState) =>
      ENNReal.ofReal (jumpFraction v))) := (jumpFraction_measurable.comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : RetainedState) =>
      ENNReal.ofReal (1-jumpFraction v))) :=
    (measurable_const.sub (jumpFraction_measurable.comp measurable_fst)).ennreal_ofReal
  simp only [uniformizedKernel,add_apply,Kernel.withDensity_apply _ hp,
    Kernel.withDensity_apply _ hm,withDensity_const,Kernel.id_apply]

instance uniformizedKernel_isMarkov : IsMarkovKernel uniformizedKernel := by
  constructor
  intro v
  constructor
  rw [uniformizedKernel_apply,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
  simp only [measure_univ,Measure.dirac_apply_of_mem (mem_univ v),smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add (by linarith [(jumpFraction_bounds v).1])
    (sub_nonneg.mpr (jumpFraction_bounds v).2)]
  simp

theorem uniformizedKernel_lower (v : RetainedState) :
    ENNReal.ofReal (1/12 : ℝ) • stateKernel v ≤ uniformizedKernel v := by
  rw [uniformizedKernel_apply]
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (jumpFraction_bounds v).1) le_rfl).trans
    (le_add_right le_rfl)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The positive collision kernel after adding a constant attenuation clock -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def stateFrequency (v : RetainedState) : ℝ := frequency v.1 beamAxis

def statePotential (v : RetainedState) : ℝ := stateRate v-stateFrequency v

theorem stateFrequency_measurable : Measurable stateFrequency := by
  unfold stateFrequency frequency
  fun_prop

theorem statePotential_lower (v : RetainedState) : 11*Real.pi/6 ≤ statePotential v :=
  retainedPotential_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v)

theorem stateFrequency_bounds (v : RetainedState) :
    4*Real.pi ≤ stateFrequency v ∧ stateFrequency v ≤ 24*Real.pi :=
  ⟨frequency_lower v.1 beamAxis axis_norms.2.2,
    frequency_upper v.1 beamAxis axis_norms.2.2 (retainedState_norm v)⟩

def branchingKernel : Kernel RetainedState RetainedState :=
  Kernel.withDensity stateKernel (fun v _ => ENNReal.ofReal (stateRate v)) +
    Kernel.withDensity Kernel.id (fun v _ => ENNReal.ofReal (48*Real.pi-stateFrequency v))

instance branchingKernel_isSFinite : IsSFiniteKernel branchingKernel := by
  unfold branchingKernel
  have hr : IsSFiniteKernel (Kernel.withDensity stateKernel
      (fun v (_ : RetainedState) => ENNReal.ofReal (stateRate v))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro v u
    exact ENNReal.ofReal_ne_top
  have hs : IsSFiniteKernel (Kernel.withDensity Kernel.id
      (fun v (_ : RetainedState) => ENNReal.ofReal (48*Real.pi-stateFrequency v))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro v u
    exact ENNReal.ofReal_ne_top
  infer_instance

theorem branchingKernel_apply (v : RetainedState) : branchingKernel v =
    ENNReal.ofReal (stateRate v) • stateKernel v +
      ENNReal.ofReal (48*Real.pi-stateFrequency v) • Measure.dirac v := by
  have hr : Measurable (Function.uncurry (fun v (_ : RetainedState) => ENNReal.ofReal (stateRate v))) :=
    (stateRate_measurable.comp measurable_fst).ennreal_ofReal
  have hs : Measurable (Function.uncurry (fun v (_ : RetainedState) =>
      ENNReal.ofReal (48*Real.pi-stateFrequency v))) :=
    (measurable_const.sub (stateFrequency_measurable.comp measurable_fst)).ennreal_ofReal
  rw [branchingKernel,add_apply,Kernel.withDensity_apply _ hr,Kernel.withDensity_apply _ hs,
    withDensity_const,withDensity_const,Kernel.id_apply]

theorem uniformizedKernel_intensity (v : RetainedState) :
    ENNReal.ofReal (48*Real.pi) • uniformizedKernel v =
      ENNReal.ofReal (stateRate v) • stateKernel v +
        ENNReal.ofReal (48*Real.pi-stateRate v) • Measure.dirac v := by
  rw [uniformizedKernel_apply,smul_add,smul_smul,smul_smul,
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  have hΛ : (48*Real.pi : ℝ) ≠ 0 := by positivity
  congr 2
  · rw [jumpFraction,mul_div_cancel₀ _ hΛ]
  · unfold jumpFraction
    field_simp

theorem branchingKernel_decomposition (v : RetainedState) :
    branchingKernel v = ENNReal.ofReal (48*Real.pi) • uniformizedKernel v +
      ENNReal.ofReal (statePotential v) • Measure.dirac v := by
  have hrBound := (stateRate_bounds v).2
  have hW : 0 ≤ statePotential v := le_trans (by positivity) (statePotential_lower v)
  rw [branchingKernel_apply,uniformizedKernel_intensity,add_assoc,← add_smul,
    ← ENNReal.ofReal_add (sub_nonneg.mpr hrBound) hW]
  congr 2
  unfold statePotential
  ring_nf

theorem branchingKernel_lower (v : RetainedState) :
    ENNReal.ofReal (48*Real.pi) • uniformizedKernel v +
      ENNReal.ofReal (11*Real.pi/6) • Measure.dirac v ≤ branchingKernel v := by
  rw [branchingKernel_decomposition]
  apply add_le_add le_rfl
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (statePotential_lower v)) le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Three-step common volume on the bounded reference state space -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateKernel_map_kernel : stateKernel.map (Subtype.val : RetainedState → V) =
    (retainedJump beamAxis).comap Subtype.val measurable_subtype_coe := by
  ext1 v
  rw [Kernel.map_apply _ measurable_subtype_coe,Kernel.comap_apply,stateKernel_map]

theorem stateKernel_pow_map (n : ℕ) : (stateKernel^n).map (Subtype.val : RetainedState → V) =
    ((retainedJump beamAxis)^n).comap Subtype.val measurable_subtype_coe := by
  induction n with
  | zero =>
    simp only [pow_zero]
    change Kernel.id.map (Subtype.val : RetainedState → V) =
      Kernel.id.comap Subtype.val measurable_subtype_coe
    rw [Kernel.id_map,Kernel.id_comap]
  | succ n ih =>
    have hs : stateKernel^(n+1) = stateKernel ∘ₖ (stateKernel^n) := by
      simpa only [add_comm,pow_one] using Kernel.pow_add stateKernel 1 n
    have hr : (retainedJump beamAxis)^(n+1) =
        retainedJump beamAxis ∘ₖ ((retainedJump beamAxis)^n) := by
      simpa only [add_comm,pow_one] using Kernel.pow_add (retainedJump beamAxis) 1 n
    rw [hs,hr]
    rw [Kernel.map_comp,stateKernel_map_kernel,← Kernel.comp_map _ _ measurable_subtype_coe,ih]
    ext v A hA
    simp only [Kernel.comap_apply,Kernel.comp_apply' _ _ _ hA]

def stateBallMeasure (δ : ℝ) : Measure RetainedState :=
  (volume.restrict (ball (0 : V) δ)).comap (Subtype.val : RetainedState → V)

theorem state_three_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v : RetainedState, stateBallMeasure δ ≤ B • (stateKernel^3) v := by
  obtain ⟨δ,B,hδ,hδsmall,hB0,hBt,hbound⟩ := retained_three_volume_domination
  refine ⟨δ,B,hδ,hδsmall,hB0,hBt,?_⟩
  intro v
  have hm : ((stateKernel^3) v).map (Subtype.val : RetainedState → V) =
      ((retainedJump beamAxis)^3) v.1 := by
    rw [← Kernel.map_apply _ measurable_subtype_coe,stateKernel_pow_map,Kernel.comap_apply]
  have h3 : ((retainedJump beamAxis)^3) =
      ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) := by
    have htwo : (retainedJump beamAxis)^2 = retainedJump beamAxis ∘ₖ retainedJump beamAxis := by
      simpa only [pow_one] using Kernel.pow_add (retainedJump beamAxis) 1 1
    calc
      (retainedJump beamAxis)^3 = ((retainedJump beamAxis)^2) ∘ₖ retainedJump beamAxis := by
        simpa only [pow_one] using Kernel.pow_add (retainedJump beamAxis) 2 1
      _ = _ := by rw [htwo]
  apply Measure.le_iff.mpr
  intro A hA
  have hi := (MeasurableEmbedding.subtype_coe referenceRegion_measurable).measurableSet_image.mpr hA
  have hh := hbound v.1 v.2 ((Subtype.val : RetainedState → V) '' A)
  rw [← h3,← hm,Measure.smul_apply,smul_eq_mul,Measure.map_apply measurable_subtype_coe hi,
    Subtype.val_injective.preimage_image] at hh
  rw [stateBallMeasure,comap_subtype_coe_apply referenceRegion_measurable,Measure.smul_apply,smul_eq_mul]
  exact hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Reversal symmetry on the bounded state space and the uniformized chain -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def stateNeg : RetainedState ≃ᵐ RetainedState where
  toFun v := ⟨-v.1,by simpa [referenceRegion,mem_closedBall,dist_zero_right] using v.2⟩
  invFun v := ⟨-v.1,by simpa [referenceRegion,mem_closedBall,dist_zero_right] using v.2⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe.neg
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact measurable_subtype_coe.neg

theorem stateNeg_val (v : RetainedState) : (stateNeg v).1 = -v.1 := rfl

theorem stateKernel_neg (v : RetainedState) : (stateKernel v).map stateNeg = stateKernel (stateNeg v) := by
  apply (MeasurableEmbedding.subtype_coe referenceRegion_measurable).map_injective
  rw [Measure.map_map measurable_subtype_coe stateNeg.measurable,stateKernel_map]
  have heq : (Subtype.val : RetainedState → V) ∘ stateNeg = Neg.neg ∘ Subtype.val := rfl
  rw [heq,← Measure.map_map measurable_neg measurable_subtype_coe,stateKernel_map,
    retainedJump_neg _ _ axis_norms.2.2]
  rfl

theorem frequency_neg (e v : V) : frequency (-v) e = frequency v e := by
  have hm : ‖-v-e‖ = ‖v+e‖ := by rw [show -v-e = -(v+e) by module,norm_neg]
  have hp : ‖-v+e‖ = ‖v-e‖ := by rw [show -v+e = -(v-e) by module,norm_neg]
  simp only [frequency,hm,hp]
  rw [add_comm]

theorem stateRate_neg (v : RetainedState) : stateRate (stateNeg v) = stateRate v := by
  simp only [stateRate,stateNeg_val,retainedRate,retention_neg _ _ axis_norms.2.2,frequency_neg]

theorem jumpFraction_neg (v : RetainedState) : jumpFraction (stateNeg v) = jumpFraction v := by
  simp only [jumpFraction,stateRate_neg]

theorem uniformizedKernel_neg (v : RetainedState) :
    (uniformizedKernel v).map stateNeg = uniformizedKernel (stateNeg v) := by
  rw [uniformizedKernel_apply,uniformizedKernel_apply,Measure.map_add,Measure.map_smul,
    Measure.map_smul,stateKernel_neg,Measure.map_dirac' stateNeg.measurable,jumpFraction_neg]
  all_goals first | exact stateNeg.measurable | exact stateNeg.measurable.aemeasurable

theorem stateBallMeasure_map {δ : ℝ} (hδ : δ ≤ 5) :
    (stateBallMeasure δ).map (Subtype.val : RetainedState → V) = volume.restrict (ball (0 : V) δ) := by
  rw [stateBallMeasure,map_comap_subtype_coe referenceRegion_measurable]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_restrict_mem (μ := (volume : Measure V)) measurableSet_ball] with v hv
  change dist v 0 ≤ 5
  exact (le_of_lt hv).trans hδ

theorem volume_ball_neg (δ : ℝ) :
    (volume.restrict (ball (0 : V) δ)).map (Neg.neg : V → V) = volume.restrict (ball (0 : V) δ) := by
  have hb : (Neg.neg : V → V) ⁻¹' ball (0 : V) δ = ball (0 : V) δ := by
    ext v
    simp only [mem_preimage,mem_ball,dist_zero_right,norm_neg]
  ext A hA
  rw [Measure.map_apply measurable_neg hA,Measure.restrict_apply (measurable_neg hA),
    ← hb,← preimage_inter,Measure.measure_preimage_neg,Measure.restrict_apply hA,hb]

theorem stateBallMeasure_neg {δ : ℝ} (hδ : δ ≤ 5) :
    (stateBallMeasure δ).map stateNeg = stateBallMeasure δ := by
  apply (MeasurableEmbedding.subtype_coe referenceRegion_measurable).map_injective
  rw [Measure.map_map measurable_subtype_coe stateNeg.measurable,stateBallMeasure_map hδ]
  have heq : (Subtype.val : RetainedState → V) ∘ stateNeg = Neg.neg ∘ Subtype.val := rfl
  rw [heq,← Measure.map_map measurable_neg measurable_subtype_coe,stateBallMeasure_map hδ,volume_ball_neg]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The constant-rate chain retains the three-collision common volume -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateKernel_power_le_uniformized (n : ℕ) (v : RetainedState) :
    (ENNReal.ofReal (1/12 : ℝ))^n • (stateKernel^n) v ≤ (uniformizedKernel^n) v := by
  induction n generalizing v with
  | zero => simp only [pow_zero,one_smul]; exact le_rfl
  | succ n ih =>
    have hs : stateKernel^(n+1) = (stateKernel^n) ∘ₖ stateKernel := by
      simpa only [pow_one] using Kernel.pow_add stateKernel n 1
    have hu : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    rw [hs,hu]
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply,smul_eq_mul,Kernel.comp_apply' _ _ _ hA,Kernel.comp_apply' _ _ _ hA]
    calc
      (ENNReal.ofReal (1/12 : ℝ))^(n+1) * (∫⁻ u, (stateKernel^n) u A ∂stateKernel v) =
          ∫⁻ u, (ENNReal.ofReal (1/12 : ℝ))^n * (stateKernel^n) u A
            ∂(ENNReal.ofReal (1/12 : ℝ) • stateKernel v) := by
        rw [lintegral_smul_measure,lintegral_const_mul' _ _
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),pow_succ]
        simp only [smul_eq_mul]
        ac_rfl
      _ ≤ ∫⁻ u, (uniformizedKernel^n) u A ∂uniformizedKernel v := by
        apply lintegral_mono' (uniformizedKernel_lower v)
        intro u
        exact ih u A

theorem uniformized_three_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v : RetainedState, stateBallMeasure δ ≤ B • (uniformizedKernel^3) v := by
  obtain ⟨δ,C,hδ,hδsmall,hC0,hCt,hbound⟩ := state_three_volume_domination
  let c := (ENNReal.ofReal (1/12 : ℝ))^3
  have hc0 : c ≠ 0 := by dsimp [c]; positivity
  have hct : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨δ,C*c⁻¹,hδ,hδsmall,mul_ne_zero hC0 (ENNReal.inv_ne_zero.mpr hct),
    ENNReal.mul_ne_top hCt (ENNReal.inv_ne_top.mpr hc0),?_⟩
  intro v
  have hp := smul_le_smul_left c⁻¹ (stateKernel_power_le_uniformized 3 v)
  rw [smul_smul,show c⁻¹*(ENNReal.ofReal (1/12 : ℝ))^3 = 1 from
    ENNReal.inv_mul_cancel hc0 hct,one_smul] at hp
  exact (hbound v).trans ((smul_le_smul_left C hp).trans_eq (smul_smul _ _ _))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A nonzero symmetric common part of all three-step transition laws -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance uniformizedKernel_pow_isMarkov (n : ℕ) : IsMarkovKernel (uniformizedKernel^n) := by
  induction n with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ n ih =>
    have heq : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    rw [heq]
    let _ := ih
    infer_instance

theorem stateBallMeasure_univ {δ : ℝ} (hδ : δ ≤ 5) :
    stateBallMeasure δ univ = volume (ball (0 : V) δ) := by
  have h := congrArg (fun μ : Measure V => μ univ) (stateBallMeasure_map hδ)
  simpa only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply_univ] using h

theorem uniformized_common_part : ∃ ρ : Measure RetainedState,
    IsFiniteMeasure ρ ∧ 0 < ρ univ ∧ ρ univ ≤ 1/2 ∧ ρ.map stateNeg = ρ ∧
      ∀ v : RetainedState, ρ ≤ (uniformizedKernel^3) v := by
  obtain ⟨δ,B,hδ,hδsmall,hB0,hBt,hbound⟩ := uniformized_three_volume_domination
  let c : ℝ≥0∞ := (1/2)*B⁻¹
  let ρ : Measure RetainedState := c • stateBallMeasure δ
  have hc : 0 < c := pos_iff_ne_zero.mpr
    (mul_ne_zero (by norm_num) (ENNReal.inv_ne_zero.mpr hBt))
  have hδfive : δ ≤ 5 := hδsmall.trans (by norm_num)
  have hscaled (v : RetainedState) : ρ ≤ (1/2 : ℝ≥0∞) • (uniformizedKernel^3) v := by
    calc
      ρ ≤ c • (B • (uniformizedKernel^3) v) := smul_le_smul_left c (hbound v)
      _ = _ := by
        rw [smul_smul]
        dsimp only [c]
        rw [mul_assoc,ENNReal.inv_mul_cancel hB0 hBt,mul_one]
  have hrpos : 0 < ρ univ := by
    rw [Measure.smul_apply,smul_eq_mul,stateBallMeasure_univ hδfive]
    exact pos_iff_ne_zero.mpr (mul_ne_zero hc.ne' (measure_ball_pos volume (0 : V) hδ).ne')
  let z : RetainedState := ⟨0,by simp [referenceRegion]⟩
  have hrsmall : ρ univ ≤ 1/2 := by
    have hh := hscaled z univ
    simpa only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using hh
  have hrfinite : IsFiniteMeasure ρ := ⟨hrsmall.trans_lt (by norm_num)⟩
  refine ⟨ρ,hrfinite,hrpos,hrsmall,?_,?_⟩
  · change (c • stateBallMeasure δ).map stateNeg = c • stateBallMeasure δ
    rw [Measure.map_smul,stateBallMeasure_neg hδfive]
    exact stateNeg.measurable.aemeasurable
  · intro v
    apply Measure.le_iff.mpr
    intro A _hA
    exact (hscaled v A).trans (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact mul_le_of_le_one_left bot_le (by norm_num))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Contraction of odd observables by the actual three-step common part -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem state_odd_integral_zero {ρ : Measure RetainedState} (hρ : ρ.map stateNeg = ρ)
    {f : RetainedState → V} (hodd : ∀ v, f (stateNeg v) = -f v) : ∫ v, f v ∂ρ = 0 := by
  have hh := (show MeasurePreserving stateNeg ρ ρ from ⟨stateNeg.measurable,hρ⟩).integral_comp
    stateNeg.measurableEmbedding f
  simp_rw [hodd] at hh
  rw [integral_neg] at hh
  have htwo : (2 : ℝ) • (∫ v, f v ∂ρ) = 0 := by
    rw [two_smul]
    exact (congrArg (fun z : V => z + ∫ v, f v ∂ρ) hh.symm).trans (neg_add_cancel _)
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem integral_common_part_bound {μ ρ : Measure RetainedState} [IsProbabilityMeasure μ]
    [IsFiniteMeasure ρ] (hρ : ρ ≤ μ) (hsym : ρ.map stateNeg = ρ)
    {f : RetainedState → V} (hf : Measurable f) (hodd : ∀ v, f (stateNeg v) = -f v)
    {M : ℝ} (hM : ∀ v, ‖f v‖ ≤ M) :
    ‖∫ v, f v ∂μ‖ ≤ (1-ρ.real univ)*M := by
  have hfμ : Integrable f μ := (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ hM)
  have hfr := hfμ.mono_measure hρ
  have hfd := hfμ.mono_measure (Measure.sub_le : μ-ρ ≤ μ)
  have hm : (μ-ρ).real univ + ρ.real univ = 1 := by
    rw [← measureReal_add_apply,Measure.sub_add_cancel_of_le hρ]
    simp
  have hz := state_odd_integral_zero hsym hodd
  calc
    ‖∫ v, f v ∂μ‖ = ‖∫ v, f v ∂(μ-ρ)‖ := by
      nth_rw 1 [← Measure.sub_add_cancel_of_le hρ]
      rw [integral_add_measure hfd hfr,hz,add_zero]
    _ ≤ M*(μ-ρ).real univ := norm_integral_le_of_norm_le_const (ae_of_all _ hM)
    _ = (1-ρ.real univ)*M := by rw [show (μ-ρ).real univ = 1-ρ.real univ by linarith]; ring

theorem uniformized_three_odd_contraction : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧
    ∀ (f : RetainedState → V), Measurable f → (∀ v, f (stateNeg v) = -f v) →
      ∀ M : ℝ, (∀ v, ‖f v‖ ≤ M) → ∀ v : RetainedState,
        ‖∫ u, f u ∂(uniformizedKernel^3) v‖ ≤ (1-ε)*M := by
  obtain ⟨ρ,hρfin,hρpos,hρsmall,hρsym,hρbound⟩ := uniformized_common_part
  let _ := hρfin
  have hεpos : 0 < ρ.real univ := ENNReal.toReal_pos hρpos.ne' (measure_ne_top ρ univ)
  have hεsmall : ρ.real univ ≤ 1/2 := by
    have hh := (ENNReal.toReal_le_toReal (measure_ne_top ρ univ) (by norm_num)).mpr hρsmall
    norm_num at hh ⊢
    exact hh
  refine ⟨ρ.real univ,hεpos,hεsmall,?_⟩
  intro f hf ho M hM v
  exact integral_common_part_bound (hρbound v) hρsym hf ho hM

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Measurable symmetric averages of the actual uniformized velocity chain -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def chainAverage (n : ℕ) (f : RetainedState → V) (v : RetainedState) : V :=
  ∫ u, f u ∂(uniformizedKernel^n) v

theorem uniformizedKernel_pow_neg (n : ℕ) :
    (uniformizedKernel^n).map stateNeg =
      (uniformizedKernel^n).comap stateNeg stateNeg.measurable := by
  have hb : uniformizedKernel.map stateNeg = uniformizedKernel.comap stateNeg stateNeg.measurable := by
    ext1 v
    rw [Kernel.map_apply _ stateNeg.measurable,Kernel.comap_apply,uniformizedKernel_neg]
  induction n with
  | zero =>
    simp only [pow_zero]
    change Kernel.id.map stateNeg = Kernel.id.comap stateNeg stateNeg.measurable
    rw [Kernel.id_map,Kernel.id_comap]
  | succ n ih =>
    have hs : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    rw [hs,Kernel.map_comp,ih,← Kernel.comp_map _ _ stateNeg.measurable,hb]
    ext v A hA
    simp only [Kernel.comap_apply,Kernel.comp_apply' _ _ _ hA]

theorem chainAverage_measurable (n : ℕ) {f : RetainedState → V} (hf : Measurable f) :
    Measurable (chainAverage n f) := hf.stronglyMeasurable.integral_kernel.measurable

theorem chainAverage_odd (n : ℕ) {f : RetainedState → V}
    (hodd : ∀ v, f (stateNeg v) = -f v) :
    ∀ v, chainAverage n f (stateNeg v) = -chainAverage n f v := by
  intro v
  have hm : ((uniformizedKernel^n) v).map stateNeg = (uniformizedKernel^n) (stateNeg v) := by
    rw [← Kernel.map_apply _ stateNeg.measurable,uniformizedKernel_pow_neg,Kernel.comap_apply]
  unfold chainAverage
  rw [← hm,stateNeg.measurableEmbedding.integral_map]
  simp_rw [hodd]
  rw [integral_neg]

theorem chainAverage_bound (n : ℕ) {f : RetainedState → V} {M : ℝ}
    (hM : ∀ v, ‖f v‖ ≤ M) (v : RetainedState) : ‖chainAverage n f v‖ ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := (uniformizedKernel^n) v) (ae_of_all _ hM)
  simpa only [chainAverage,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using! h

theorem chainAverage_zero (f : RetainedState → V) (v : RetainedState) : chainAverage 0 f v = f v := by
  unfold chainAverage
  change (∫ u, f u ∂Measure.dirac v) = f v
  simp

theorem chainAverage_add (n m : ℕ) {f : RetainedState → V} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, ‖f v‖ ≤ M) (v : RetainedState) :
    chainAverage (n+m) f v = chainAverage m (chainAverage n f) v := by
  unfold chainAverage
  rw [Kernel.pow_add]
  apply Kernel.integral_comp
  exact (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ hM)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
