import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.CubeDensity
import OAI.Analysis.CoulombIonization.FieldAnalysis.CubeRotations

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

def euclideanCubeOverlap (x : CubeSpace) : ℝ := cubeOverlap (WithLp.ofLp x)

lemma euclideanCubeOverlap_measurable : Measurable euclideanCubeOverlap :=
  cubeOverlap_measurable.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable

lemma euclideanCubeOverlap_integrable : Integrable euclideanCubeOverlap :=
  ((PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp cubeOverlap_measurable.aestronglyMeasurable).2 cubeOverlap_integrable

lemma integral_euclideanCubeOverlap : (∫ x, euclideanCubeOverlap x) = 1 := by
  change (∫ x : CubeSpace, cubeOverlap (WithLp.ofLp x)) = 1
  rw [(PiLp.volume_preserving_ofLp (Fin 3)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).measurableEmbedding, integral_cubeOverlap]

lemma euclideanCubeOverlap_support (x : CubeSpace) (hx : Real.sqrt 3 ≤ ‖x‖) :
    euclideanCubeOverlap x = 0 := by
  obtain ⟨i,hi⟩ : ∃ i : Fin 3, 1 ≤ |x i| := by
    by_contra! h
    have hs : ∑ i : Fin 3, (x i)^2 < ∑ _i : Fin 3, (1:ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _
        nlinarith [abs_nonneg (x i),sq_abs (x i),h i]
      · exact ⟨0,Finset.mem_univ _,by nlinarith [abs_nonneg (x 0),sq_abs (x 0),h 0]⟩
    have hh := (Real.sqrt_le_iff.mp hx).2
    rw [EuclideanSpace.real_norm_sq_eq] at hh
    norm_num at hs
    linarith
  exact cubeOverlap_support_coord _ i hi

def vartheta : CubeSpace → ℝ := radialAverage euclideanCubeOverlap

lemma vartheta_measurable : Measurable vartheta := radialAverage_measurable euclideanCubeOverlap_measurable
lemma vartheta_integrable : Integrable vartheta := radialAverage_integrable euclideanCubeOverlap_measurable euclideanCubeOverlap_integrable
lemma vartheta_nonneg (x : CubeSpace) : 0 ≤ vartheta x := radialAverage_nonneg (fun _x => cubeOverlap_nonneg _) x
lemma vartheta_le (x : CubeSpace) : vartheta x ≤ 1 := radialAverage_le euclideanCubeOverlap_measurable
  (fun _x => cubeOverlap_nonneg _) (fun _x => cubeOverlap_le _) x
lemma integral_vartheta : (∫ x, vartheta x) = 1 := by
  rw [vartheta,integral_radialAverage euclideanCubeOverlap_measurable euclideanCubeOverlap_integrable,
    integral_euclideanCubeOverlap]
lemma vartheta_radial {x y : CubeSpace} (h : ‖x‖=‖y‖) : vartheta x=vartheta y := radialAverage_radial _ h
lemma vartheta_support (x : CubeSpace) (hx : Real.sqrt 3 ≤ ‖x‖) : vartheta x=0 :=
  radialAverage_support euclideanCubeOverlap_support x hx

def varthetaScaled (b : ℝ) (x : CubeSpace) : ℝ := b⁻¹^3*vartheta (b⁻¹ • x)

lemma varthetaScaled_measurable (b : ℝ) : Measurable (varthetaScaled b) :=
  measurable_const.mul (vartheta_measurable.comp ((continuous_id.const_smul (b⁻¹:ℝ)).measurable))
lemma varthetaScaled_integrable {b : ℝ} (hb : 0 < b) : Integrable (varthetaScaled b) :=
  (vartheta_integrable.comp_smul (inv_ne_zero hb.ne')).const_mul _
lemma varthetaScaled_nonneg {b : ℝ} (hb : 0 < b) (x : CubeSpace) : 0 ≤ varthetaScaled b x :=
  mul_nonneg (by positivity) (vartheta_nonneg _)
lemma varthetaScaled_le {b : ℝ} (hb : 0 < b) (x : CubeSpace) : varthetaScaled b x ≤ b⁻¹^3 :=
  mul_le_of_le_one_right (by positivity) (vartheta_le _)
lemma integral_varthetaScaled {b : ℝ} (hb : 0 < b) : (∫ x, varthetaScaled b x) = 1 := by
  unfold varthetaScaled
  rw [integral_const_mul,Measure.integral_comp_smul_of_nonneg volume vartheta b⁻¹ (hR := by positivity)]
  simp [integral_vartheta,hb.ne']
lemma varthetaScaled_radial (b : ℝ) {x y : CubeSpace} (h : ‖x‖=‖y‖) :
    varthetaScaled b x=varthetaScaled b y := by
  unfold varthetaScaled
  exact congrArg (fun z => b⁻¹^3*z) (vartheta_radial (x := b⁻¹ • x) (y := b⁻¹ • y) (by simp only [norm_smul,h]))
lemma varthetaScaled_support {b : ℝ} (hb : 0 < b) (x : CubeSpace)
    (hx : Real.sqrt 3*b ≤ ‖x‖) : varthetaScaled b x=0 := by
  unfold varthetaScaled
  rw [vartheta_support _ (by
    rw [norm_smul,Real.norm_of_nonneg (by positivity : 0 ≤ b⁻¹)]
    exact (le_inv_mul_iff₀ hb).2 (by simpa only [mul_comm] using hx)),mul_zero]

open MeasureTheory Set Filter
open scoped BigOperators unitInterval

variable {N : ℕ}

lemma cubeDensity_measurable :
    Measurable (fun p : (Fin 3 → ℝ) × ((Fin N → Fin 3 → ℝ) × (Fin 3 → ℝ)) => cubeDensity p.1 p.2.1 p.2.2) := by
  unfold cubeDensity
  apply Finset.measurable_sum
  intro i _
  have hm : Measurable (fun p : (Fin 3 → ℝ) × ((Fin N → Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      (p.1,(p.2.1 i,p.2.2))) := by fun_prop
  exact (sameCube_measurable (d := Fin 3)).comp hm

lemma cubeAssignment_measurable :
    Measurable (fun p : (Fin 3 → ℝ) × (Fin N → Fin 3 → ℝ) => cubeAssignment p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  exact cubeIndex_measurable.comp (((measurable_pi_apply i).comp measurable_snd).sub measurable_fst)

lemma cubePressure_measurable :
    Measurable (fun p : (Fin 3 → ℝ) × (Fin N → Fin 3 → ℝ) => cellPressure (cubeAssignment p.1 p.2)) :=
  (measurable_of_countable cellPressure).comp cubeAssignment_measurable

lemma cube_t_continuous : Continuous (fun t : Fin 3 → I => fun a => (t a:ℝ)) :=
  continuous_pi (fun a => continuous_subtype_val.comp (continuous_apply a))

lemma translation_average_pressure (x : Fin N → Fin 3 → ℝ) :
    Integrable (fun y => (∑ i, cubeOverlap (x i-y))^(5/3:ℝ)) ∧
    (∫ y, (∑ i, cubeOverlap (x i-y))^(5/3:ℝ)) ≤
      ∫ t : Fin 3 → I, cellPressure (cubeAssignment (fun a => (t a:ℝ)) x) := by
  have hm : Measurable (fun p : (Fin 3 → I) × (Fin 3 → ℝ) =>
      cubeDensity (fun a => (p.1 a:ℝ)) x p.2) :=
    cubeDensity_measurable.comp ((cube_t_continuous.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))
  have hn (t : Fin 3 → I) (y : Fin 3 → ℝ) : 0 ≤ cubeDensity (fun a => (t a:ℝ)) x y := cubeDensity_nonneg _ _ _
  have hc (t : Fin 3 → I) (y : Fin 3 → ℝ) : cubeDensity (fun a => (t a:ℝ)) x y ≤ N := cubeDensity_le _ _ _
  have hi (t : Fin 3 → I) : Integrable (fun y : Fin 3 → ℝ => cubeDensity (fun a => (t a:ℝ)) x y^(5/3:ℝ)) := cubeDensity_rpow_integrable _ _
  have hb (t : Fin 3 → I) : (∫ y : Fin 3 → ℝ, cubeDensity (fun a => (t a:ℝ)) x y^(5/3:ℝ)) ≤ (N:ℝ)^(5/3:ℝ) := by
    rw [integral_cubeDensity_rpow]
    exact cellPressure_le _
  have h := average_pressure (μ := volume) (ν := volume)
    (f := fun (t : Fin 3 → I) (y : Fin 3 → ℝ) => cubeDensity (fun a => (t a:ℝ)) x y) hm hn hc hi hb
  simpa only [integral_cubeDensity_t,integral_cubeDensity_rpow] using h

def varthetaSmear (x : Fin N → CubeSpace) (y : CubeSpace) : ℝ :=
  ∑ i, vartheta (x i-y)

def rotatedCubeCloud (R : CubeRotation) (x : Fin N → CubeSpace) : Fin N → Fin 3 → ℝ :=
  fun i => WithLp.ofLp (rotationIsometry R⁻¹ (x i))

def translatedPressureAverage (x : Fin N → Fin 3 → ℝ) : ℝ :=
  ∫ t : Fin 3 → I, cellPressure (cubeAssignment (fun a => (t a:ℝ)) x)

lemma translatedPressureAverage_measurable : Measurable (translatedPressureAverage (N := N)) := by
  exact (cubePressure_measurable.comp
    ((cube_t_continuous.measurable.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable.integral_prod_left'.measurable

lemma translatedPressureAverage_nonneg (x : Fin N → Fin 3 → ℝ) : 0 ≤ translatedPressureAverage x :=
  integral_nonneg (fun _ => cellPressure_nonneg _)
lemma translatedPressureAverage_le (x : Fin N → Fin 3 → ℝ) : translatedPressureAverage x ≤ (N:ℝ)^(5/3:ℝ) := by
  have hi : Integrable (fun t : Fin 3 → I => cellPressure (cubeAssignment (fun a => (t a:ℝ)) x)) := by
    apply (integrable_const ((N:ℝ)^(5/3:ℝ))).mono'
      ((cubePressure_measurable.comp (cube_t_continuous.measurable.prodMk measurable_const))).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by change ‖cellPressure _‖ ≤ _; rw [Real.norm_of_nonneg (cellPressure_nonneg _)]; exact cellPressure_le _)
  exact (integral_mono hi (integrable_const _) (fun _ => cellPressure_le _)).trans_eq (by simp)

lemma rotatedCubeCloud_continuous :
    Continuous (fun p : CubeRotation × (Fin N → CubeSpace) => rotatedCubeCloud p.1 p.2) := by
  apply continuous_pi
  intro i
  exact (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
    (rotationIsometry_continuous.comp ((continuous_inv.comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)))

lemma varthetaSmear_translation_rotation (x : Fin N → CubeSpace) (y : CubeSpace) :
    varthetaSmear x y = ∫ R : CubeRotation,
      (∑ i, cubeOverlap (rotatedCubeCloud R x i-WithLp.ofLp (rotationIsometry R⁻¹ y))) ∂cubeRotationMeasure := by
  have he (R : CubeRotation) (i : Fin N) :
      cubeOverlap (rotatedCubeCloud R x i-WithLp.ofLp (rotationIsometry R⁻¹ y)) =
        euclideanCubeOverlap (rotationIsometry R⁻¹ (x i-y)) := by
    unfold euclideanCubeOverlap rotatedCubeCloud
    rw [map_sub]
    rfl
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => radialAverage_section_integrable euclideanCubeOverlap_measurable (B := 1)
    (fun z => by change ‖cubeOverlap (WithLp.ofLp z)‖ ≤ 1; rw [Real.norm_of_nonneg (cubeOverlap_nonneg _)]; exact cubeOverlap_le _) (x i-y))]
  rfl

lemma cubeOverlap_sum_integrable (x : Fin N → Fin 3 → ℝ) :
    Integrable (fun y => ∑ i, cubeOverlap (x i-y)) :=
  integrable_finsetSum _ (fun i _ => cubeOverlap_integrable.comp_sub_left (x i))

lemma cubeOverlap_sum_le (x : Fin N → Fin 3 → ℝ) (y : Fin 3 → ℝ) :
    (∑ i, cubeOverlap (x i-y)) ≤ N := by
  calc
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun i _ => cubeOverlap_le _)
    _ = _ := by simp

lemma rotatedCloud_coordinates_preserving (R : CubeRotation) :
    MeasurePreserving (fun y : CubeSpace => WithLp.ofLp (rotationIsometry R⁻¹ y)) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).comp (rotationIsometry R⁻¹).measurePreserving

lemma rotatedCloud_coordinates_embedding (R : CubeRotation) :
    MeasurableEmbedding (fun y : CubeSpace => WithLp.ofLp (rotationIsometry R⁻¹ y)) :=
  (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).measurableEmbedding.comp
    (rotationIsometry R⁻¹).toHomeomorph.measurableEmbedding

lemma rotatedCloud_density_measurable (x : Fin N → CubeSpace) :
    Measurable (fun p : CubeRotation × CubeSpace =>
      ∑ i, cubeOverlap (rotatedCubeCloud p.1 x i-WithLp.ofLp (rotationIsometry p.1⁻¹ p.2))) := by
  apply Finset.measurable_sum
  intro i _
  exact cubeOverlap_measurable.comp
    (((measurable_pi_apply i).comp (rotatedCubeCloud_continuous.measurable.comp
      (measurable_fst.prodMk measurable_const))).sub
        ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp
          (rotationIsometry_continuous.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)).measurable))

def radialPressureAverage (x : Fin N → CubeSpace) : ℝ :=
  ∫ R : CubeRotation, translatedPressureAverage (rotatedCubeCloud R x) ∂cubeRotationMeasure

lemma radialPressureAverage_measurable : Measurable (radialPressureAverage (N := N)) :=
  (translatedPressureAverage_measurable.comp rotatedCubeCloud_continuous.measurable).stronglyMeasurable.integral_prod_left'.measurable

lemma radialPressureAverage_nonneg (x : Fin N → CubeSpace) : 0 ≤ radialPressureAverage x :=
  integral_nonneg (fun _ => translatedPressureAverage_nonneg _)

lemma translatedPressureAverage_rotation_integrable (x : Fin N → CubeSpace) :
    Integrable (fun R : CubeRotation => translatedPressureAverage (rotatedCubeCloud R x)) cubeRotationMeasure := by
  apply (integrable_const ((N:ℝ)^(5/3:ℝ))).mono'
    ((translatedPressureAverage_measurable.comp rotatedCubeCloud_continuous.measurable).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall (fun R => by
    change ‖translatedPressureAverage _‖ ≤ _
    rw [Real.norm_of_nonneg (translatedPressureAverage_nonneg _)]
    exact translatedPressureAverage_le _)

lemma radialPressureAverage_le (x : Fin N → CubeSpace) : radialPressureAverage x ≤ (N:ℝ)^(5/3:ℝ) := by
  exact (integral_mono (translatedPressureAverage_rotation_integrable x) (integrable_const _)
    (fun _ => translatedPressureAverage_le _)).trans_eq (by simp)

theorem varthetaSmear_pressure (x : Fin N → CubeSpace) :
    Integrable (fun y => varthetaSmear x y^(5/3:ℝ)) ∧
      (∫ y, varthetaSmear x y^(5/3:ℝ)) ≤ radialPressureAverage x := by
  let f (R : CubeRotation) (y : CubeSpace) : ℝ :=
    ∑ i, cubeOverlap (rotatedCubeCloud R x i-WithLp.ofLp (rotationIsometry R⁻¹ y))
  have hn (R : CubeRotation) (y : CubeSpace) : 0 ≤ f R y :=
    Finset.sum_nonneg (fun _ _ => cubeOverlap_nonneg _)
  have hi (R : CubeRotation) : Integrable (fun y => f R y^(5/3:ℝ)) :=
    ((rotatedCloud_coordinates_preserving R).integrable_comp
      (translation_average_pressure (rotatedCubeCloud R x)).1.aestronglyMeasurable).2
        (translation_average_pressure (rotatedCubeCloud R x)).1
  have he (R : CubeRotation) : (∫ y, f R y^(5/3:ℝ)) =
      ∫ y, (∑ i, cubeOverlap (rotatedCubeCloud R x i-y))^(5/3:ℝ) :=
    (rotatedCloud_coordinates_preserving R).integral_comp (rotatedCloud_coordinates_embedding R)
      (fun y => (∑ i, cubeOverlap (rotatedCubeCloud R x i-y))^(5/3:ℝ))
  have hb (R : CubeRotation) : (∫ y, f R y^(5/3:ℝ)) ≤ translatedPressureAverage (rotatedCubeCloud R x) := by
    rw [he]
    exact (translation_average_pressure _).2
  have hp := average_pressure (μ := cubeRotationMeasure) (rotatedCloud_density_measurable x)
    hn (fun R y => cubeOverlap_sum_le _ _)
    hi (fun R => (hb R).trans (translatedPressureAverage_le _))
  have hae (y : CubeSpace) : (∫ R, f R y ∂cubeRotationMeasure) = varthetaSmear x y :=
    (varthetaSmear_translation_rotation x y).symm
  change Integrable (fun y => (∫ R, f R y ∂cubeRotationMeasure)^(5/3:ℝ)) ∧
    (∫ y, (∫ R, f R y ∂cubeRotationMeasure)^(5/3:ℝ)) ≤
      ∫ R, (∫ y, f R y^(5/3:ℝ)) ∂cubeRotationMeasure at hp
  simp_rw [hae] at hp
  refine ⟨hp.1,hp.2.trans ?_⟩
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun R => integral_nonneg (fun y => Real.rpow_nonneg (hn R y) _)))
    (translatedPressureAverage_rotation_integrable x)
    (Eventually.of_forall hb)

end CoulombNeumann

end

end OAI
