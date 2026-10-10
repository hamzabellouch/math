import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

open Metric Module Function Filter Topology
open scoped RealInnerProductSpace ContDiff OnePoint

namespace Problem340

def chartNorthVector : SphereAmbient := EuclideanSpace.single 2 1

@[simp] theorem norm_chartNorthVector : ‖chartNorthVector‖ = 1 := by
  simp [chartNorthVector]

theorem chartNorthVector_ne_zero : chartNorthVector ≠ 0 := by
  intro h
  simpa [h] using norm_chartNorthVector

def chartNorthPole : StandardSphere2 :=
  ⟨chartNorthVector, by simp⟩

theorem mem_chartEquator_iff (x : SphereAmbient) :
    x ∈ (ℝ ∙ chartNorthVector)ᗮ ↔ x 2 = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [chartNorthVector, EuclideanSpace.inner_single_left]

def chartEquatorLinearEquiv : ℂ ≃ₗ[ℝ] (ℝ ∙ chartNorthVector)ᗮ where
  toFun z := ⟨WithLp.toLp 2 ![z.re, z.im, 0], by
    rw [mem_chartEquator_iff]
    rfl⟩
  invFun w := (w.val 0 : ℂ) + (w.val 1 : ℂ) * Complex.I
  map_add' z w := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  map_smul' r z := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [Complex.real_smul]
  left_inv z := by
    apply Complex.ext <;> simp
  right_inv w := by
    apply Subtype.ext
    ext i
    have hw := (mem_chartEquator_iff w.val).mp w.property
    fin_cases i <;> simp [hw]

def chartEquatorEquiv : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ chartNorthVector)ᗮ where
  toLinearEquiv := chartEquatorLinearEquiv
  norm_map' z := by
    change ‖(WithLp.toLp 2 ![z.re, z.im, 0] : SphereAmbient)‖ = ‖z‖
    rw [EuclideanSpace.norm_eq, Complex.norm_def]
    congr 1
    simp [Fin.sum_univ_succ, Complex.normSq_apply, sq]

@[simp] theorem chartEquatorEquiv_apply (z : ℂ) :
    (chartEquatorEquiv z : SphereAmbient) = WithLp.toLp 2 ![z.re, z.im, 0] := rfl

@[simp] theorem chartEquatorEquiv_apply_zero (z : ℂ) :
    (chartEquatorEquiv z).val 0 = z.re := rfl

@[simp] theorem chartEquatorEquiv_apply_one (z : ℂ) :
    (chartEquatorEquiv z).val 1 = z.im := rfl

@[simp] theorem chartEquatorEquiv_apply_two (z : ℂ) :
    (chartEquatorEquiv z).val 2 = 0 := rfl

@[simp] theorem chartEquatorEquiv_symm_apply (w : (ℝ ∙ chartNorthVector)ᗮ) :
    chartEquatorEquiv.symm w = (w.val 0 : ℂ) + (w.val 1 : ℂ) * Complex.I := rfl

theorem chartEquatorEquiv_symm_projection (x : SphereAmbient) :
    chartEquatorEquiv.symm ((ℝ ∙ chartNorthVector)ᗮ.orthogonalProjectionOnto x) =
      (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  have hs := (ℝ ∙ chartNorthVector).starProjection_add_starProjection_orthogonal x
  rw [Submodule.starProjection_unit_singleton ℝ norm_chartNorthVector] at hs
  have h0 := congrArg (fun y : SphereAmbient => y 0) hs
  have h1 := congrArg (fun y : SphereAmbient => y 1) hs
  have hp0 : (((ℝ ∙ chartNorthVector)ᗮ.orthogonalProjectionOnto x).val 0) = x 0 := by
    change inner ℝ chartNorthVector x * 0 +
      ((ℝ ∙ chartNorthVector)ᗮ.orthogonalProjectionOnto x).val 0 = x 0 at h0
    simpa only [mul_zero, zero_add] using h0
  have hp1 : (((ℝ ∙ chartNorthVector)ᗮ.orthogonalProjectionOnto x).val 1) = x 1 := by
    change inner ℝ chartNorthVector x * 0 +
      ((ℝ ∙ chartNorthVector)ᗮ.orthogonalProjectionOnto x).val 1 = x 1 at h1
    simpa only [mul_zero, zero_add] using h1
  rw [chartEquatorEquiv_symm_apply, hp0, hp1]

theorem sphere_val_two_eq_one_iff (x : StandardSphere2) :
    x.val 2 = 1 ↔ x = chartNorthPole := by
  constructor
  · intro hx
    apply Subtype.ext
    apply Eq.symm
    apply (inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) norm_chartNorthVector
      (norm_eq_of_mem_sphere x)).mp
    simpa [chartNorthVector, EuclideanSpace.inner_single_left] using hx
  · rintro rfl
    simp [chartNorthPole, chartNorthVector]

def sphereOfComplex (z : ℂ) : StandardSphere2 :=
  stereoInvFun norm_chartNorthVector (chartEquatorEquiv ((2 : ℝ) • z))

theorem sphereOfComplex_val (z : ℂ) :
    (sphereOfComplex z : SphereAmbient) =
      (‖z‖ ^ 2 + 1)⁻¹ •
        ((2 : ℝ) • (chartEquatorEquiv z : SphereAmbient) +
          (‖z‖ ^ 2 - 1) • chartNorthVector) := by
  have hn : ‖(chartEquatorEquiv z : SphereAmbient)‖ = ‖z‖ :=
    chartEquatorEquiv.norm_map z
  have hd : ‖z‖ ^ 2 + 1 ≠ 0 := by positivity
  have hd' : (2 * ‖z‖) ^ 2 + 4 ≠ 0 := by positivity
  change stereoInvFunAux chartNorthVector
    (chartEquatorEquiv ((2 : ℝ) • z) : SphereAmbient) = _
  simp only [stereoInvFunAux_apply, norm_smul, Real.norm_eq_abs, show |(2 : ℝ)| = 2 by norm_num, hn,
    map_smul, Submodule.coe_smul_of_tower, smul_add, smul_smul]
  match_scalars <;> field_simp <;> ring

@[simp] theorem sphereOfComplex_val_zero (z : ℂ) :
    (sphereOfComplex z).val 0 = 2 * z.re / (‖z‖ ^ 2 + 1) := by
  rw [sphereOfComplex_val]
  simp [chartNorthVector,
    div_eq_mul_inv, mul_comm]
  left
  change 2 * z.re = z.re * 2
  ring

@[simp] theorem sphereOfComplex_val_one (z : ℂ) :
    (sphereOfComplex z).val 1 = 2 * z.im / (‖z‖ ^ 2 + 1) := by
  rw [sphereOfComplex_val]
  simp [chartNorthVector,
    div_eq_mul_inv, mul_comm]
  left
  change 2 * z.im = z.im * 2
  ring

@[simp] theorem sphereOfComplex_val_two (z : ℂ) :
    (sphereOfComplex z).val 2 = (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) := by
  rw [sphereOfComplex_val]
  simp [chartNorthVector,
    div_eq_mul_inv, mul_comm]
  right
  rfl

def sphereToComplex (x : StandardSphere2) : ℂ :=
  (1 / 2 : ℝ) • chartEquatorEquiv.symm (stereoToFun chartNorthVector x.val)

@[simp] theorem sphereToComplex_sphereOfComplex (z : ℂ) :
    sphereToComplex (sphereOfComplex z) = z := by
  unfold sphereToComplex sphereOfComplex
  rw [stereo_right_inv]
  simp

theorem sphereOfComplex_ne_north (z : ℂ) : sphereOfComplex z ≠ chartNorthPole := by
  exact stereoInvFun_ne_north_pole norm_chartNorthVector _

theorem sphereOfComplex_sphereToComplex {x : StandardSphere2} (hx : x ≠ chartNorthPole) :
    sphereOfComplex (sphereToComplex x) = x := by
  have hx' : (x : SphereAmbient) ≠ chartNorthVector := by
    intro h
    apply hx
    exact Subtype.ext h
  unfold sphereOfComplex sphereToComplex
  rw [smul_smul]
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact stereo_left_inv norm_chartNorthVector hx'

theorem continuous_sphereOfComplex : Continuous sphereOfComplex := by
  exact (continuous_stereoInvFun norm_chartNorthVector).comp
    (chartEquatorEquiv.continuous.comp (continuous_id.const_smul (2 : ℝ)))

theorem contDiff_sphereOfComplex_val {n : ℕ∞ω} :
    ContDiff ℝ n (fun z : ℂ => (sphereOfComplex z : SphereAmbient)) := by
  exact contDiff_stereoInvFunAux.comp
    ((ℝ ∙ chartNorthVector)ᗮ.subtypeL.contDiff.comp
      (chartEquatorEquiv.contDiff.comp (contDiff_id.const_smul (2 : ℝ))))

theorem sphereOfComplex_injective : Function.Injective sphereOfComplex :=
  Function.LeftInverse.injective sphereToComplex_sphereOfComplex

theorem range_sphereOfComplex : Set.range sphereOfComplex = {chartNorthPole}ᶜ := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact sphereOfComplex_ne_north z
  · intro hx
    exact ⟨sphereToComplex x, sphereOfComplex_sphereToComplex hx⟩

def sphereToComplexAmbient (x : SphereAmbient) : ℂ :=
  (1 / 2 : ℝ) • chartEquatorEquiv.symm (stereoToFun chartNorthVector x)

theorem sphereToComplexAmbient_formula (x : SphereAmbient) :
    sphereToComplexAmbient x =
      ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) / (1 - (x 2 : ℂ)) := by
  unfold sphereToComplexAmbient
  rw [stereoToFun_apply, map_smul, smul_smul, chartEquatorEquiv_symm_projection]
  simp [chartNorthVector, EuclideanSpace.inner_single_left, Complex.real_smul,
    div_eq_mul_inv]
  ring

theorem sphereToComplex_formula (x : StandardSphere2) :
    sphereToComplex x =
      ((x.val 0 : ℂ) + (x.val 1 : ℂ) * Complex.I) / (1 - (x.val 2 : ℂ)) :=
  sphereToComplexAmbient_formula x.val

theorem contDiffOn_sphereToComplexAmbient {n : ℕ∞ω} :
    ContDiffOn ℝ n sphereToComplexAmbient {x : SphereAmbient | x 2 ≠ 1} := by
  have hs : {x : SphereAmbient | x 2 ≠ 1} =
      {x : SphereAmbient | innerSL ℝ chartNorthVector x ≠ 1} := by
    ext x
    simp [chartNorthVector, EuclideanSpace.inner_single_left]
  rw [hs]
  exact ((contDiff_id.const_smul (1 / 2 : ℝ)).comp chartEquatorEquiv.symm.contDiff).comp_contDiffOn contDiffOn_stereoToFun

theorem continuousOn_sphereToComplex :
    ContinuousOn sphereToComplex {chartNorthPole}ᶜ := by
  exact ((continuous_id.const_smul (1 / 2 : ℝ)).comp
    chartEquatorEquiv.symm.continuous).comp_continuousOn
      (stereographic norm_chartNorthVector).continuousOn

def sphereComplexChart : OpenPartialHomeomorph StandardSphere2 ℂ where
  toFun := sphereToComplex
  invFun := sphereOfComplex
  source := {chartNorthPole}ᶜ
  target := Set.univ
  map_source' := by simp
  map_target' := by intro z _; exact sphereOfComplex_ne_north z
  left_inv' := by intro x hx; exact sphereOfComplex_sphereToComplex hx
  right_inv' := by intro z _; exact sphereToComplex_sphereOfComplex z
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_sphereToComplex
  continuousOn_invFun := continuous_sphereOfComplex.continuousOn

def scaledChartEquator : ℂ ≃ₜ (ℝ ∙ chartNorthVector)ᗮ :=
  (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num) : ℂ ≃ₜ ℂ).trans
    chartEquatorEquiv.toHomeomorph

def complexSphereHomeomorph : OnePoint ℂ ≃ₜ StandardSphere2 :=
  scaledChartEquator.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere norm_chartNorthVector)

@[simp] theorem complexSphereHomeomorph_coe (z : ℂ) :
    complexSphereHomeomorph (z : OnePoint ℂ) = sphereOfComplex z := by
  rfl

@[simp] theorem complexSphereHomeomorph_infty :
    complexSphereHomeomorph (∞ : OnePoint ℂ) = chartNorthPole := by
  rfl

@[simp] theorem complexSphereHomeomorph_symm_north :
    complexSphereHomeomorph.symm chartNorthPole = (∞ : OnePoint ℂ) := by
  exact complexSphereHomeomorph.symm_apply_eq.mpr complexSphereHomeomorph_infty.symm

@[simp] theorem complexSphereHomeomorph_symm_affine (z : ℂ) :
    complexSphereHomeomorph.symm (sphereOfComplex z) = (z : OnePoint ℂ) := by
  exact complexSphereHomeomorph.symm_apply_eq.mpr (complexSphereHomeomorph_coe z).symm

theorem isOpenEmbedding_sphereOfComplex : Topology.IsOpenEmbedding sphereOfComplex :=
  sphereComplexChart.symm.isOpenEmbedding (by rfl)

theorem tendsto_sphereOfComplex_iff {ι : Type*} {l : Filter ι}
    {z : ι → ℂ} {w : ℂ} :
    Tendsto (fun i => sphereOfComplex (z i)) l (𝓝 (sphereOfComplex w)) ↔
      Tendsto z l (𝓝 w) :=
  isOpenEmbedding_sphereOfComplex.isEmbedding.tendsto_nhds_iff.symm

theorem tendsto_sphereOfComplex_north_iff {ι : Type*} {l : Filter ι} {z : ι → ℂ} :
    Tendsto (fun i => sphereOfComplex (z i)) l (𝓝 chartNorthPole) ↔
      Tendsto (fun i => ‖z i‖) l atTop := by
  calc
    Tendsto (fun i => sphereOfComplex (z i)) l (𝓝 chartNorthPole) ↔
        Tendsto (fun i => (z i : OnePoint ℂ)) l (𝓝 (∞ : OnePoint ℂ)) := by
      simpa only [Function.comp_def, complexSphereHomeomorph_coe,
        complexSphereHomeomorph_infty] using
        (complexSphereHomeomorph.isEmbedding.tendsto_nhds_iff
          (f := fun i => (z i : OnePoint ℂ)) (l := l) (y := (∞ : OnePoint ℂ))).symm
    _ ↔ Tendsto z l (cocompact ℂ) := by
      rw [← coclosedCompact_eq_cocompact, ← OnePoint.comap_coe_nhds_infty]
      exact tendsto_comap_iff.symm
    _ ↔ Tendsto (fun i => ‖z i‖) l atTop := by
      rw [tendsto_norm_atTop_iff_cobounded, Metric.cobounded_eq_cocompact]

end Problem340

end

end OAI
