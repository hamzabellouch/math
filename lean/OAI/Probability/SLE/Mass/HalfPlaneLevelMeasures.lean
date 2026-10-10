import OAI.Probability.SLE.Mass.SignedLevelTests

namespace OAI

/-! The finite-level approximants as locally finite measures on the open
half-plane, and their signed compact tests viewed on the ambient plane. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

lemma levelMass_lt_top_of_compact
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (ω : Ω) (hBc : Continuous (fun t => B t ω))
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane) (u : ℝ) :
    levelMass κ B γ G u K ω < ⊤ := by
  obtain ⟨b,hb,hbK⟩ := compact_positive_radius_cap hK hKH
  let C := (b * Real.exp (-u)) ^ (-codimension κ)
  have hW (z : ℂ) (hz : z ∈ K) : stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u ≤ C := by
    have he : 0 < 2*z.im*Real.exp (-u) := mul_pos (mul_pos (by norm_num) (hKH hz)) (Real.exp_pos _)
    have hs := stoppedGreen_level_bound (hBc.const_mul _) hw hκ hκ8 z (hKH hz)
      (2*z.im*Real.exp (-u)) he
    rw [common_level_log_target z (hKH hz) u] at hs
    exact hs.trans (Real.rpow_le_rpow_of_nonpos (mul_pos hb (Real.exp_pos _))
      (mul_le_mul_of_nonneg_right (hbK z hz) (Real.exp_pos _).le)
      (neg_nonpos.mpr (codimension_pos κ hκ8).le))
  have hbound : levelMass κ B γ G u K ω ≤ ENNReal.ofReal C * volume K := by
    apply (setLIntegral_mono' hK.measurableSet (fun z hz => ENNReal.ofReal_le_ofReal (hW z hz))).trans_eq
    exact setLIntegral_const K (ENNReal.ofReal C)
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top)

def halfPlaneLevelMeasure {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (ω : Ω) : Measure upperHalfPlane :=
  (levelApproximation κ B γ G u t ω).comap Subtype.val

theorem halfPlaneLevelMeasure_finite_on_compacts
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (ω : Ω) (hBc : Continuous (fun t => B t ω))
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (u : ℝ) (t : ℝ≥0∞) : IsFiniteMeasureOnCompacts (halfPlaneLevelMeasure κ B γ G u t ω) := by
  constructor
  intro K hK
  have hKI : IsCompact ((Subtype.val : upperHalfPlane → ℂ) '' K) := hK.image continuous_subtype_val
  have hKH : (Subtype.val : upperHalfPlane → ℂ) '' K ⊆ upperHalfPlane := by
    rintro _ ⟨x,_,rfl⟩
    exact x.property
  rw [halfPlaneLevelMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet]
  exact (levelApproximation_apply_le κ B γ G u t ω hKI.measurableSet).trans_lt
    (levelMass_lt_top_of_compact hκ hκ8 γ G F ω hBc hw _ hKI hKH u)

def extendHalfPlaneTest (f : upperHalfPlane → ℝ) : ℂ → ℝ :=
  Function.extend (Subtype.val : upperHalfPlane → ℂ) f (fun _ => 0)

lemma extendHalfPlaneTest_apply (f : upperHalfPlane → ℝ) (x : upperHalfPlane) :
    extendHalfPlaneTest f x = f x := Subtype.val_injective.extend_apply _ _ _

lemma extendHalfPlaneTest_of_not_mem (f : upperHalfPlane → ℝ) (z : ℂ) (hz : z ∉ upperHalfPlane) :
    extendHalfPlaneTest f z = 0 := by
  apply Function.extend_apply'
  rintro ⟨x,rfl⟩
  exact hz x.property

lemma extendHalfPlaneTest_measurable (f : upperHalfPlane → ℝ) (hf : Measurable f) :
    Measurable (extendHalfPlaneTest f) :=
  (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurable_extend hf measurable_const

lemma extendHalfPlaneTest_support (f : C_c(upperHalfPlane,ℝ)) (z : ℂ)
    (hz : z ∉ (Subtype.val : upperHalfPlane → ℂ) '' tsupport f) : extendHalfPlaneTest f z = 0 := by
  by_cases hH : z ∈ upperHalfPlane
  · let x : upperHalfPlane := ⟨z,hH⟩
    change extendHalfPlaneTest f x = 0
    rw [extendHalfPlaneTest_apply]
    exact image_eq_zero_of_notMem_tsupport (fun hx => hz ⟨x,hx,rfl⟩)
  · exact extendHalfPlaneTest_of_not_mem f z hH

lemma extendHalfPlaneTest_norm_le (f : C_c(upperHalfPlane,ℝ)) (z : ℂ) :
    ‖extendHalfPlaneTest f z‖ ≤ ‖f.toBoundedContinuousFunction‖ := by
  by_cases hH : z ∈ upperHalfPlane
  · let x : upperHalfPlane := ⟨z,hH⟩
    change ‖extendHalfPlaneTest f x‖ ≤ _
    rw [extendHalfPlaneTest_apply]
    exact f.toBoundedContinuousFunction.norm_coe_le_norm x
  · rw [extendHalfPlaneTest_of_not_mem f z hH,norm_zero]
    exact norm_nonneg _

lemma integral_halfPlaneLevelMeasure
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (ω : Ω) (f : upperHalfPlane → ℝ) :
    (∫ x, f x ∂halfPlaneLevelMeasure κ B γ G u t ω) =
      levelApproximationRealTest κ B γ G u t (extendHalfPlaneTest f) ω := by
  change (∫ x : upperHalfPlane, f x ∂(levelApproximation κ B γ G u t ω).comap Subtype.val) = _
  calc
    _ = ∫ x : upperHalfPlane, extendHalfPlaneTest f x
        ∂(levelApproximation κ B γ G u t ω).comap Subtype.val := by
      congr 1
      funext x
      exact (extendHalfPlaneTest_apply f x).symm
    _ = ∫ z in upperHalfPlane, extendHalfPlaneTest f z ∂levelApproximation κ B γ G u t ω :=
      integral_subtype_comap isOpen_upperHalfPlane.measurableSet _
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (extendHalfPlaneTest_of_not_mem f)

end SLEExactGauge.Multipoint

end

end OAI
