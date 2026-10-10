import OAI.MathematicalPhysics.Boltzmann.Branching.BackgroundCappedLoss
import OAI.MathematicalPhysics.Boltzmann.Branching.PerturbedFiniteBlock

namespace OAI

section

/-! # Measurable two-beam coefficients from the actual geometric cold profiles -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

def beamVelocity (θ η α γ σ : ℝ) (p : ℝ × Velocity) : Velocity :=
  PlaneChart.join 0 (AxialFlow.velocity σ α γ (scale θ η (transverse p.2))
    (max 0 p.1) (axial p.2))

def beamDensity (θ η α γ r σ : ℝ) (p : ℝ × Velocity) : ℝ :=
  4*r*AxialBackground.weight 1 α γ (scale θ η (transverse p.2))
    (max 0 p.1) σ (axial p.2)

theorem beamVelocity_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η σ : ℝ) : Measurable (beamVelocity θ η α γ σ) := by
  let f : ℤ × (ℝ × ℝ) → Velocity := fun p =>
    PlaneChart.join 0 (AxialFlow.velocity σ α γ (GeometricMesh.point θ η p.1)
      (max 0 p.2.1) p.2.2)
  have hf : Measurable f := measurable_from_prod_countable_right (fun k =>
    split.symm.measurable.comp
      (((AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ
        (GeometricMesh.point_pos hθ η k)).measurable).prodMk measurable_const))
  have hs : Measurable (fun p : ℝ × Velocity => (axial p.2,transverse p.2)) := by
    simpa only [Function.comp_def,split_apply] using split.measurable.comp
      (show Measurable (Prod.snd : ℝ × Velocity → Velocity) from measurable_snd)
  have hi : Measurable (fun p : ℝ × Velocity =>
      (GeometricMesh.index (‖transverse p.2‖/θ) η,(p.1,axial p.2))) := by
    unfold GeometricMesh.index
    exact ((hs.snd.norm.div_const θ).log.div_const η).floor.prodMk
      (measurable_fst.prodMk hs.fst)
  change Measurable (fun p : ℝ × Velocity => PlaneChart.join 0
    (AxialFlow.velocity σ α γ (GeometricMesh.point θ η (GeometricMesh.index (‖transverse p.2‖/θ) η))
      (max 0 p.1) (axial p.2)))
  simpa only [Function.comp_def,f] using hf.comp hi

theorem beamDensity_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η r σ : ℝ) : Measurable (beamDensity θ η α γ r σ) := by
  let f : ℤ × (ℝ × ℝ) → ℝ := fun p =>
    4*r*AxialBackground.weight 1 α γ (GeometricMesh.point θ η p.1)
      (max 0 p.2.1) σ p.2.2
  have hf : Measurable f := measurable_from_prod_countable_right (fun k =>
    (AxialBackground.clamped_weight_measurable hα hγ (GeometricMesh.point_pos hθ η k) 1 σ).const_mul (4*r))
  have hs : Measurable (fun p : ℝ × Velocity => (axial p.2,transverse p.2)) := by
    simpa only [Function.comp_def,split_apply] using split.measurable.comp
      (show Measurable (Prod.snd : ℝ × Velocity → Velocity) from measurable_snd)
  have hi : Measurable (fun p : ℝ × Velocity =>
      (GeometricMesh.index (‖transverse p.2‖/θ) η,(p.1,axial p.2))) := by
    unfold GeometricMesh.index
    exact ((hs.snd.norm.div_const θ).log.div_const η).floor.prodMk
      (measurable_fst.prodMk hs.fst)
  change Measurable (fun p : ℝ × Velocity => 4*r*AxialBackground.weight 1 α γ
    (GeometricMesh.point θ η (GeometricMesh.index (‖transverse p.2‖/θ) η))
      (max 0 p.1) σ (axial p.2))
  simpa only [Function.comp_def,f] using hf.comp hi

def beamCoefficients {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η r : ℝ) : ReferenceGeometry.BeamCoefficients where
  plusPartner := beamVelocity θ η α γ 1
  minusPartner := beamVelocity θ η α γ (-1)
  plusDensity := beamDensity θ η α γ r 1
  minusDensity := beamDensity θ η α γ r (-1)
  plusPartner_measurable := beamVelocity_measurable hθ hα hγ η 1
  minusPartner_measurable := beamVelocity_measurable hθ hα hγ η (-1)
  plusDensity_measurable := beamDensity_measurable hθ hα hγ η r 1
  minusDensity_measurable := beamDensity_measurable hθ hα hγ η r (-1)

theorem beamDensity_eq_relative {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 < r) (η σ : ℝ) (p : ℝ × Velocity) (ht : 0 ≤ p.1) :
    beamDensity θ η α γ r σ p = AxialBackground.relativeWeight r α γ
      (scale θ η (transverse p.2)) p.1 σ (axial p.2) := by
  unfold beamDensity
  rw [max_eq_right ht,AxialBackground.weight_eq_relative hr (scale_pos hθ η _) hα hγ ht]
  field_simp

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The actual active cold measure equals the normalized two-beam measure -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

def beamMeasure (b : BeamCoefficients) (p : ℝ × V) : Measure V :=
  ENNReal.ofReal (b.plusDensity p) • Measure.dirac (b.plusPartner p)+
    ENNReal.ofReal (b.minusDensity p) • Measure.dirac (b.minusPartner p)

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem background_eq_beamMeasure {θ K α γ r t : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (ht : 0 ≤ t) (η l : ℝ) (x : Velocity) (ha : active θ η l (transverse x)) :
    background θ η l K α γ t (transverse x,axial x) =
      ENNReal.ofReal (K/(4*r)) •
        ReferenceGeometry.beamMeasure (beamCoefficients hθ hα hγ η r) (t,x) := by
  have hfactor : 0 ≤ K/(4*r) := by positivity
  have hw (σ : ℝ) : K/(4*r)*beamDensity θ η α γ r σ (t,x) =
      AxialBackground.weight K α γ (scale θ η (transverse x)) t σ (axial x) := by
    unfold beamDensity
    rw [max_eq_right ht]
    unfold AxialBackground.weight JetCoreDensity.compressed
    field_simp
  rw [background,ite_eq_left ha]
  change AxialBackground.cell K α γ (scale θ η (transverse x)) t (axial x) = _
  rw [AxialBackground.cell,ReferenceGeometry.beamMeasure,smul_add]
  congr 1
  · change ENNReal.ofReal (AxialBackground.weight K α γ (scale θ η (transverse x)) t 1 (axial x)) •
        Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity 1 α γ (scale θ η (transverse x)) t (axial x))) =
      ENNReal.ofReal (K/(4*r)) • (ENNReal.ofReal (beamDensity θ η α γ r 1 (t,x)) •
        Measure.dirac (beamVelocity θ η α γ 1 (t,x)))
    rw [smul_smul,← ENNReal.ofReal_mul hfactor,hw]
    simp only [beamVelocity,max_eq_right ht]
  · change ENNReal.ofReal (AxialBackground.weight K α γ (scale θ η (transverse x)) t (-1) (axial x)) •
        Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity (-1) α γ (scale θ η (transverse x)) t (axial x))) =
      ENNReal.ofReal (K/(4*r)) • (ENNReal.ofReal (beamDensity θ η α γ r (-1) (t,x)) •
        Measure.dirac (beamVelocity θ η α γ (-1) (t,x)))
    rw [smul_smul,← ENNReal.ofReal_mul hfactor,hw]
    simp only [beamVelocity,max_eq_right ht]

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The selected two-beam field is the actual cold background away from null mesh circles -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem ae_not_mesh_circle (θ η : ℝ) :
    ∀ᵐ y : Transverse ∂volume, ∀ k : ℤ, ‖y‖ ≠ GeometricMesh.point θ η k := by
  apply ae_all_iff.mpr
  intro k
  apply ae_iff.mpr
  have he : {y : Transverse | ¬‖y‖ ≠ GeometricMesh.point θ η k} =
      Metric.sphere 0 (GeometricMesh.point θ η k) := by
    ext y
    simp only [not_not,mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
  rw [he]
  exact Measure.addHaar_sphere volume 0 _

theorem active_ae_above_cutoff {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (l : ℝ) :
    ∀ᵐ y : Transverse ∂volume, 0 < ‖y‖ → Real.exp η*l < ‖y‖ → active θ η l y := by
  filter_upwards [ae_not_mesh_circle θ η] with y hy hpos hcut
  have hb := GeometricMesh.cell_bounds hθ hη hpos
  have hstrict : scale θ η y < ‖y‖ :=
    lt_of_le_of_ne hb.1 (hy (GeometricMesh.index (‖y‖/θ) η)).symm
  refine ⟨?_,hstrict,hb.2⟩
  exact (mul_lt_mul_iff_right₀ (Real.exp_pos η)).mp (hcut.trans hb.2)

theorem background_eq_beamMeasure_ae {θ K α γ r : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    {η : ℝ} (hη : 0 < η) (l : ℝ) :
    ∀ᵐ y : Transverse ∂volume, 0 < ‖y‖ → Real.exp η*l < ‖y‖ →
      ∀ t : ℝ, 0 ≤ t → ∀ z : ℝ,
      background θ η l K α γ t (y,z) =
        ENNReal.ofReal (K/(4*r)) • ReferenceGeometry.beamMeasure
          (beamCoefficients hθ hα hγ η r) (t,PlaneChart.join y z) := by
  filter_upwards [active_ae_above_cutoff hθ hη l] with y hy hpos hcut t ht z
  have hh := background_eq_beamMeasure hθ hK hα hγ hr ht η l (PlaneChart.join y z)
  simpa only [PlaneChart.transverse_join,PlaneChart.axial_join] using
    hh (by simpa only [PlaneChart.transverse_join] using hy hpos hcut)

theorem beamDensity_nonneg {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η σ : ℝ) (p : ℝ × Velocity) :
    0 ≤ beamDensity θ η α γ r σ p := by
  apply mul_nonneg (mul_nonneg (by norm_num) hr)
  exact AxialBackground.weight_nonneg (by norm_num) hα hγ (scale_pos hθ η _) (le_max_left 0 _) _ _

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Both selected cold beams have a uniform positive density on compact annuli -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamDensity_compact_lower {θ η α γ r₀ R T Z : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hT : 0 ≤ T) (hZ : 0 ≤ Z) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℝ × Velocity), p.1 ∈ Icc 0 T →
      ‖transverse p.2‖ ∈ Icc r₀ R → |axial p.2| ≤ Z →
      ∀ σ : ℝ, |σ| = 1 → c ≤ beamDensity θ η α γ 1 σ p := by
  let m := r₀/Real.exp η
  let c := 4*AxialBackground.compactWeightLower 1 α γ m R T Z
  have hm : 0 < m := div_pos hr₀ (Real.exp_pos η)
  have hc : 0 < c := mul_pos (by norm_num)
    (AxialBackground.compactWeightLower_pos (by norm_num) hα hγ hR hT)
  refine ⟨c,hc,?_⟩
  intro p ht hp hz σ hσ
  have hp0 : 0 < ‖transverse p.2‖ := hr₀.trans_le hp.1
  have hb := GeometricMesh.cell_bounds hθ hη hp0
  have hμ : scale θ η (transverse p.2) ∈ Icc m R := by
    refine ⟨?_,hb.1.trans hp.2⟩
    apply (div_le_iff₀ (Real.exp_pos η)).mpr
    exact hp.1.trans (by simpa only [mul_comm,scale] using hb.2.le)
  have hh := AxialBackground.compactWeightLower_le (by norm_num : (0:ℝ) ≤ 1)
    hα hγ hm hT hZ hμ ht hσ hz
  change 4*AxialBackground.compactWeightLower 1 α γ m R T Z ≤ _
  unfold beamDensity
  rw [max_eq_right ht.1]
  norm_num only [mul_one]
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
