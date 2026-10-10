import Mathlib
import OAI.Probability.Ballisticity.Estimates.SmallTimeExponentialError
import OAI.Probability.Ballisticity.Estimates.SelectedBoundaryRestart
import OAI.Probability.Ballisticity.Crossings.BoundaryFirstHits

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

noncomputable def observedPotential (b R z : ℝ) : ℝ :=
  min ((max |z| b)^((3:ℝ)/2)) ((2*R)^((3:ℝ)/2))

lemma observedPotential_nonneg' (b R z : ℝ) (hR : 0 ≤ R) :
    0 ≤ observedPotential b R z := by
  exact le_min (Real.rpow_nonneg ((abs_nonneg _).trans (le_max_left _ _)) _)
    (Real.rpow_nonneg (by positivity) _)

lemma observedPotential_le (b R z : ℝ) : observedPotential b R z ≤ (2*R)^((3:ℝ)/2) :=
  min_le_right _ _

lemma measurable_observedPotential (b R : ℝ) : Measurable (observedPotential b R) := by
  unfold observedPotential
  fun_prop

lemma integrable_observedPotential {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (g : Ω → ℝ) (hg : Measurable g) (b R : ℝ) (hR : 0 ≤ R) :
    Integrable (fun ω => observedPotential b R (g ω)) μ := by
  apply Integrable.of_bound ((measurable_observedPotential b R).comp hg).aestronglyMeasurable
    ((2*R)^((3:ℝ)/2))
  exact Eventually.of_forall fun ω => by
    change ‖observedPotential b R (g ω)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (observedPotential_nonneg' b R (g ω) hR)]
    exact observedPotential_le _ _ _

lemma observedPotential_upper_start {b R u : ℝ} (hb : b ≤ u) (hu : 0 ≤ u) (hR : u ≤ R) :
    observedPotential b R u = u^((3:ℝ)/2) := by
  unfold observedPotential
  rw [abs_of_nonneg hu,max_eq_left hb,min_eq_left]
  apply Real.rpow_le_rpow hu _ (by norm_num)
  linarith

lemma observedPotential_lower_start {b R z : ℝ} (hb : 0 ≤ b) (hz : |z| ≤ b) (hR : b ≤ R) :
    observedPotential b R z = b^((3:ℝ)/2) := by
  unfold observedPotential
  rw [max_eq_right hz,min_eq_left]
  apply Real.rpow_le_rpow hb _ (by norm_num)
  linarith

lemma observedPotential_scaled_clip {b R u z : ℝ} (hu : 0 < u) (hR : u ≤ R) :
    u^((3:ℝ)/2)*min (|z/u|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2)) ≤
      observedPotential b R z := by
  have hp : 0 ≤ u^((3:ℝ)/2) := Real.rpow_nonneg hu.le _
  rw [mul_min_of_nonneg _ _ hp]
  apply min_le_min
  · rw [abs_div,abs_of_pos hu,Real.div_rpow (abs_nonneg _) hu.le]
    have hn := ne_of_gt (Real.rpow_pos_of_pos hu ((3:ℝ)/2))
    rw [mul_div_cancel₀ _ hn]
    exact Real.rpow_le_rpow (abs_nonneg _) (le_max_left _ _) (by norm_num)
  · rw [← Real.mul_rpow hu.le (by norm_num)]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    linarith

lemma observedPotential_lower_gain {b R z : ℝ} (hb : 0 ≤ b) (hR : b ≤ R) (hz : 2*b ≤ |z|) :
    (2*b)^((3:ℝ)/2) ≤ observedPotential b R z := by
  apply le_min
  · exact Real.rpow_le_rpow (by positivity) (hz.trans (le_max_left _ _)) (by norm_num)
  · exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)

lemma observedPotential_above_floor {b R z : ℝ} (hb : 0 ≤ b) (hR : b ≤ R) :
    b^((3:ℝ)/2) ≤ observedPotential b R z := by
  apply le_min
  · exact Real.rpow_le_rpow hb (le_max_right _ _) (by norm_num)
  · exact Real.rpow_le_rpow hb (by linarith) (by norm_num)

lemma boundaryData_endpoints {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    (boundaryData ℓ H P).endpoints =
      (P.1 (boundaryTimes ℓ H P).1,P.2 (boundaryTimes ℓ H P).2) := by
  simp [boundaryData,BoundaryData.endpoints,pairPrefix,extendPrefix_apply]

lemma selectedBoundaryData_endpoints {d : ℕ} (ℓ : Vector d)
    (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) :
    (selectedBoundaryData ℓ B P).endpoints =
      (P.1 (selectedBoundaryTimes ℓ B P).1,P.2 (selectedBoundaryTimes ℓ B P).2) := by
  simp [selectedBoundaryData,BoundaryData.endpoints,pairPrefix,extendPrefix_apply]

theorem shared_boundary_potential_drift {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {t : ℝ} (ht : 0<t) (htmax : t≤1/1000000) :
    let ℓ := realPosition (step e)
    let μ := independentConditionedPairLaw ν ℓ
    let n := fluctuationScale μ (commonIncrementProcess ℓ f 0)
    ∃ l ε R₀ : ℝ, 0<l ∧ l<1 ∧ 0<ε ∧ 0<R₀ ∧
      ∀ u, R₀≤u → n u*μ.real {P | l*u < |commonIncrementProcess ℓ f 0 P|}≤ε →
      ∀ x y, signedHeight e x=signedHeight e y → |signedCoordinate f (x-y)|=u →
      ∀ b R, b≤u → u≤R →
      let H := ⌊t*n u⌋₊
      0<H ∧ u^((3:ℝ)/2)+t/(128*commonMeanWidth ν ℓ)*u^((3:ℝ)/2) ≤
        ∫ P, observedPotential b R
          (signedCoordinate f ((boundaryData ℓ ((signedHeight e x+H:ℤ):ℝ) P).endpoints.1-
            (boundaryData ℓ ((signedHeight e x+H:ℤ):ℝ) P).endpoints.2))
          ∂sharedConditionedPairLaw ν ℓ x y := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let n := fluctuationScale μ (commonIncrementProcess ℓ f 0)
  obtain ⟨l,ε,R₀,hl,hl1,hε,hR₀,hdrift⟩ := shared_uniform_good_clipped_drift ν hue e f hef htrans ht htmax
  refine ⟨l,ε,R₀,hl,hl1,hε,hR₀,?_⟩
  intro u hu hgood x y hxy hgap b R hb hR
  obtain ⟨hH,hd⟩ := hdrift u hu hgood x y hxy hgap
  let H := ⌊t*n u⌋₊
  have hHpos : 0<H := hH
  refine ⟨hHpos,?_⟩
  have hupos : 0<u := hR₀.trans_le hu
  let Q := sharedConditionedPairLaw ν ℓ x y
  let : IsProbabilityMeasure Q := sharedConditionedPairLaw_probability ν ℓ x y
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans x y))
  let Z := fun P : Path d × Path d => physicalFirstHitGap ℓ f x y
    (H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P) P
  have hZ : Measurable Z := measurable_physicalFirstHitGap_random ℓ f x y
    (fun P => H+commonOffset ℓ (signedHeight e) (signedHeight e x+H) P)
    (measurable_const.add (measurable_commonOffset _ _ _))
  have hcl : Integrable (fun P => min (|Z P/u|^((3:ℝ)/2)) ((2:ℝ)^((3:ℝ)/2))) Q := by
    apply Integrable.of_bound (by fun_prop (disch := norm_num)) ((2:ℝ)^((3:ℝ)/2))
    exact Eventually.of_forall fun P => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg _) _) (by positivity))]
      exact min_le_right _ _
  have hbound := integral_mono_ae (hcl.const_mul (u^((3:ℝ)/2)))
    (integrable_observedPotential Q Z hZ b R (hupos.le.trans hR))
    (Eventually.of_forall fun P => observedPotential_scaled_clip hupos hR (z := Z P) (b := b))
  rw [integral_const_mul] at hbound
  have hidentity : (fun P => observedPotential b R
      (signedCoordinate f ((boundaryData ℓ ((signedHeight e x+H:ℤ):ℝ) P).endpoints.1-
        (boundaryData ℓ ((signedHeight e x+H:ℤ):ℝ) P).endpoints.2))) =ᵐ[Q]
      (fun P => observedPotential b R (Z P)) := by
    filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y,
      shared_common_boundary_exists ν hue ℓ (signed_direction_unit e) htrans (signedHeight e)
        (signedHeight_projection e) (signedHeight_step_le e) x y hxy H] with P hP hC
    rw [boundaryData_endpoints,boundaryTimes_firstHit_identity e f x y hxy H hHpos P hP.1 hP.2 hC]
  rw [integral_congr_ae hidentity]
  have hmult := mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hupos.le ((3:ℝ)/2))
  change u^((3:ℝ)/2)*(1+t/(128*commonMeanWidth ν ℓ)) ≤ _ at hmult
  nlinarith [hmult.trans hbound]

end DirectionalTransience

end

end

end OAI
