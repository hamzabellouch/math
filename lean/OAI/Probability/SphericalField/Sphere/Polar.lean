import Mathlib
import OAI.Probability.SphericalField.Sphere.RadialBands

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

section Polar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma polar_lintegral (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ u : Metric.sphere (0:E) 1, ∫⁻ r : Ioi (0:ℝ),
        f ((r:ℝ) • (u:E)) ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂μ.toSphere := by
  let h := homeomorphUnitSphereProd E
  let F : Metric.sphere (0:E) 1 × Ioi (0:ℝ) → ℝ≥0∞ :=
    fun p => f ((p.2:ℝ) • (p.1:E))
  have hF : Measurable F := hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)
  calc
    _ = ∫⁻ x : ({(0:E)}ᶜ : Set E), f (x:E) ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫⁻ p, F p ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      convert (μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp hF) using 1
      apply lintegral_congr
      intro x
      change f (x:E) = f ((h x).2.val • (h x).1.val)
      have he := congrArg Subtype.val (h.symm_apply_apply x)
      exact congrArg f he.symm
    _ = _ := lintegral_prod _ hF.aemeasurable

lemma polar_lintegral_swap (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂μ.toSphere ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) := by
  rw [polar_lintegral μ f hf]
  exact lintegral_lintegral_swap
    (hf.comp (measurable_snd.subtype_val.smul measurable_fst.subtype_val)).aemeasurable

def normalizedAngular : Measure (Metric.sphere (0:E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

def haarRadiusMeasure : Measure (Ioi (0:ℝ)) :=
  μ.toSphere univ • Measure.volumeIoiPow (Module.finrank ℝ E - 1)

lemma angular_total_ne_zero : μ.toSphere univ ≠ 0 := by
  exact Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero μ)

lemma polar_lintegral_normalized (f : E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), ∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂normalizedAngular μ ∂haarRadiusMeasure μ := by
  rw [haarRadiusMeasure,lintegral_smul_measure]
  simp only [normalizedAngular,lintegral_smul_measure,smul_eq_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (angular_total_ne_zero μ)),← mul_assoc,
    ENNReal.mul_inv_cancel (angular_total_ne_zero μ) (measure_ne_top _ _),one_mul]
  exact polar_lintegral_swap μ f hf

lemma polar_radial_lintegral (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g ‖x‖ ∂μ) = ∫⁻ r : Ioi (0:ℝ), g r ∂haarRadiusMeasure μ := by
  rw [polar_lintegral_normalized μ (fun x => g ‖x‖) (hg.comp measurable_norm)]
  apply lintegral_congr
  intro r
  have hnorm (u : Metric.sphere (0:E) 1) : ‖(r:ℝ) • (u:E)‖ = (r:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property]
    simp
  simp only [hnorm,lintegral_const,normalizedAngular,Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.inv_mul_cancel (angular_total_ne_zero μ) (measure_ne_top _ _),mul_one]

lemma polar_weighted_lintegral (f : E → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x, g ‖x‖ * f x ∂μ) =
      ∫⁻ r : Ioi (0:ℝ), g r * (∫⁻ u : Metric.sphere (0:E) 1,
        f ((r:ℝ) • (u:E)) ∂normalizedAngular μ) ∂haarRadiusMeasure μ := by
  rw [polar_lintegral_normalized μ (fun x => g ‖x‖ * f x) ((hg.comp measurable_norm).mul hf)]
  apply lintegral_congr
  intro r
  have hnorm (u : Metric.sphere (0:E) 1) : ‖(r:ℝ) • (u:E)‖ = (r:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property]; simp
  simp only [hnorm]
  exact lintegral_const_mul _ ((hf.comp (measurable_subtype_coe.const_smul (r:ℝ))))

lemma polar_weighted_bounds (f : E → ℝ≥0∞) (hf : Measurable f)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) {L U : ℝ≥0∞}
    (hL : ∀ r : Ioi (0:ℝ), g r ≠ 0 →
      L ≤ ∫⁻ u : Metric.sphere (0:E) 1, f ((r:ℝ) • (u:E)) ∂normalizedAngular μ)
    (hU : ∀ r : Ioi (0:ℝ), g r ≠ 0 →
      (∫⁻ u : Metric.sphere (0:E) 1, f ((r:ℝ) • (u:E)) ∂normalizedAngular μ) ≤ U) :
    L * (∫⁻ x, g ‖x‖ ∂μ) ≤ (∫⁻ x, g ‖x‖ * f x ∂μ) ∧
      (∫⁻ x, g ‖x‖ * f x ∂μ) ≤ U * (∫⁻ x, g ‖x‖ ∂μ) := by
  rw [polar_radial_lintegral μ g hg,polar_weighted_lintegral μ f hf g hg]
  constructor
  · rw [← lintegral_const_mul (f := fun r : Ioi (0:ℝ) => g r) _ (hg.comp measurable_subtype_coe)]
    apply lintegral_mono
    intro r
    by_cases hr : g r = 0
    · simp [hr]
    · simpa only [mul_comm L] using mul_le_mul le_rfl (hL r hr) (by positivity) (by positivity)
  · rw [← lintegral_const_mul (f := fun r : Ioi (0:ℝ) => g r) _ (hg.comp measurable_subtype_coe)]
    apply lintegral_mono
    intro r
    by_cases hr : g r = 0
    · simp [hr]
    · simpa only [mul_comm U] using mul_le_mul le_rfl (hU r hr) (by positivity) (by positivity)

end Polar

def linearFieldFactor {n : ℕ} (ρ : Measure (Spin (n+1))) (x : Spin (n+1)) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ z x)) ∂ρ

def angularFieldFactor {n : ℕ} (ρ : Measure (Spin (n+1))) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ u : Metric.sphere (0:Spin (n+1)) 1,
    linearFieldFactor ρ (r • (u:Spin (n+1))) ∂unitSphereLaw (n+1)

lemma linearFieldFactor_measurable {n : ℕ} (ρ : Measure (Spin (n+1))) [SFinite ρ] :
    Measurable (linearFieldFactor ρ) := by
  exact Measurable.lintegral_prod_right
    ((continuous_snd.inner continuous_fst).rexp.measurable.ennreal_ofReal)

lemma angularFieldFactor_eq {n : ℕ} (ρ : Measure (Spin (n+1))) [SFinite ρ] (r : ℝ) :
    angularFieldFactor ρ r = ∫⁻ z, ENNReal.ofReal (sphericalExp n z r) ∂ρ := by
  unfold angularFieldFactor linearFieldFactor
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro z
  simp only [inner_smul_right]
  exact (ofReal_integral_eq_lintegral_ofReal
    (unitSphere_continuous_integrable (by fun_prop))
    (Eventually.of_forall fun u => (Real.exp_pos _).le)).symm

lemma angularFieldFactor_mono {n : ℕ} (ρ : Measure (Spin (n+1))) [SFinite ρ]
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    angularFieldFactor ρ r ≤ angularFieldFactor ρ s := by
  rw [angularFieldFactor_eq,angularFieldFactor_eq]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (sphericalExp_mono n z hr hrs)

lemma one_le_angularFieldFactor {n : ℕ} (ρ : Measure (Spin (n+1))) [IsProbabilityMeasure ρ]
    (r : ℝ) : 1 ≤ angularFieldFactor ρ r := by
  rw [angularFieldFactor_eq]
  calc
    (1:ℝ≥0∞) = ∫⁻ _ : Spin (n+1), (1:ℝ≥0∞) ∂ρ := by simp
    _ ≤ _ := lintegral_mono fun z => by
      simpa using ENNReal.ofReal_le_ofReal (one_le_sphericalExp n z r)

def canonicalBandRadiusWeight (n : ℕ) (b ε : ℝ) : ℝ → ℝ≥0∞ :=
  {r : ℝ | ((n+1:ℕ):ℝ)*(1-ε) ≤ r^2 ∧ r^2 ≤ ((n+1:ℕ):ℝ)*(1+ε)}.indicator
    (fun r => ENNReal.ofReal (radialNormalizer n * Real.exp (-(b/2)*r^2)))

lemma canonicalBandRadiusWeight_measurable (n : ℕ) (b ε : ℝ) :
    Measurable (canonicalBandRadiusWeight n b ε) := by
  apply Measurable.indicator (by fun_prop)
  exact (measurableSet_le measurable_const (continuous_id.pow 2).measurable).inter
    (measurableSet_le (continuous_id.pow 2).measurable measurable_const)

lemma canonicalBandRadiusWeight_integral (n : ℕ) (b ε : ℝ)
    (F : RadialSpace n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, canonicalBandRadiusWeight n b ε ‖x‖ * F x) =
      ∫⁻ x in normSquareBand n ε, F x ∂canonicalRadialMass n b := by
  rw [canonicalRadialMass,setLIntegral_withDensity_eq_setLIntegral_mul _
    (canonicalRadialDensity_continuous n b).measurable.ennreal_ofReal hF
    (normSquareBand_measurable n ε),← lintegral_indicator (normSquareBand_measurable n ε) _]
  apply lintegral_congr
  intro x
  by_cases hx : ((n+1:ℕ):ℝ)*(1-ε) ≤ ‖x‖^2 ∧ ‖x‖^2 ≤ ((n+1:ℕ):ℝ)*(1+ε)
  all_goals simp only [canonicalBandRadiusWeight,normSquareBand,Set.indicator_apply,Set.mem_ofPred_eq,hx,and_self,ite_true,ite_false,zero_mul,Pi.mul_apply,canonicalRadialDensity]

lemma canonicalBandRadiusWeight_mass (n : ℕ) (b ε : ℝ) :
    (∫⁻ x : RadialSpace n, canonicalBandRadiusWeight n b ε ‖x‖) =
      canonicalRadialMass n b (normSquareBand n ε) := by
  simpa using canonicalBandRadiusWeight_integral n b ε (fun _ => 1) measurable_const

end SphericalPerceptron
end
end
end

end OAI
