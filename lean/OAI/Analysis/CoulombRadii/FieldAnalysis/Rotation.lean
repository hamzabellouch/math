import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.FlatDensityPower

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Set
open scoped BigOperators Matrix
namespace Coulomb
abbrev Rotation := Matrix.specialOrthogonalGroup (Fin 3) ℝ

lemma rotation_entry_sq_sum (Q : Rotation) (j : Fin 3) :
    ∑ i : Fin 3, (Q.1 i j)^2 = 1 := by
  have H := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j j) Q.prop.1.1
  simpa [Matrix.mul_apply, Matrix.star_apply, pow_two] using H

lemma rotation_entry_abs_le (Q : Rotation) (i j : Fin 3) : |Q.1 i j| ≤ 1 := by
  have H : (Q.1 i j)^2 ≤ 1 := by
    rw [← rotation_entry_sq_sum Q j]
    exact Finset.single_le_sum (fun k _ => sq_nonneg (Q.1 k j)) (Finset.mem_univ i)
  exact (sq_le_one_iff_abs_le_one _).mp H

lemma rotation_closed : IsClosed (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  change IsClosed ((unitary (Matrix (Fin 3) (Fin 3) ℝ) : Set _) ∩
    (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det) ⁻¹' {1})
  exact isClosed_unitary.inter (isClosed_singleton.preimage continuous_id.matrix_det)

lemma rotation_set_compact : IsCompact (Matrix.specialOrthogonalGroup (Fin 3) ℝ : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ _ : Fin 3 => (-1:ℝ)) (fun _ _ => (1:ℝ)) )).of_isClosed_subset rotation_closed
  intro Q hQ
  constructor <;> intro i j
  · exact (abs_le.mp (rotation_entry_abs_le ⟨Q,hQ⟩ i j)).1
  · exact (abs_le.mp (rotation_entry_abs_le ⟨Q,hQ⟩ i j)).2

noncomputable instance rotation_compact : CompactSpace Rotation :=
  isCompact_iff_compactSpace.mp rotation_set_compact

instance rotation_continuousStar : ContinuousStar Rotation where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star
instance rotation_continuousInv : ContinuousInv Rotation where
  continuous_inv := continuous_star
instance rotation_topologicalGroup : IsTopologicalGroup Rotation where

instance rotation_measurable : MeasurableSpace Rotation := borel Rotation
instance rotation_borel : BorelSpace Rotation := ⟨rfl⟩

noncomputable def rotationMeasure : Measure Rotation :=
  Measure.haarMeasure (⟨⟨univ,isCompact_univ⟩,by simp⟩ : TopologicalSpace.PositiveCompacts Rotation)

instance : IsProbabilityMeasure rotationMeasure := ⟨Measure.haarMeasure_self⟩

noncomputable def rotationIsometry (Q : Rotation) : Space ≃ₗᵢ[ℝ] Space :=
  Unitary.linearIsometryEquiv ⟨Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) Q.1, by
    constructor
    · have H := congrArg (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)) Q.prop.1.1
      simpa only [map_mul, map_star, map_one] using H
    · have H := congrArg (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)) Q.prop.1.2
      simpa only [map_mul, map_star, map_one] using H⟩

lemma rotationIsometry_apply (Q : Rotation) (x : Space) (j : Fin 3) :
    rotationIsometry Q x j = ∑ k, Q.1 j k*x k := rfl

lemma rotationIsometry_measurePreserving (Q : Rotation) :
    MeasurePreserving (rotationIsometry Q) volume volume :=
  (rotationIsometry Q).measurePreserving

lemma rotation_action_continuous : Continuous (fun p : Rotation × Space => rotationIsometry p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  change Continuous (fun p : Rotation × Space => ∑ k, p.1.1 j k * p.2 k)
  apply continuous_finsetSum
  intro k _
  have hQ : Continuous (fun p : Rotation × Space => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : Rotation × Space => p.2 k) :=
    (PiLp.continuous_apply 2 _ k).comp continuous_snd
  exact ((continuous_apply k).comp ((continuous_apply j).comp hQ)).mul hx

lemma flatFineKernel_continuous (b : ℝ) : Continuous (flatFineKernel b) := by
  apply Continuous.const_mul
  apply continuous_finsetProd
  intro j _
  exact continuous_const.max (continuous_const.sub (continuous_apply j).abs)

lemma flatFineKernel_le {b : ℝ} (hb : 0 < b) (x : Fin 3 → ℝ) :
    flatFineKernel b x ≤ (b⁻¹)^3 := by
  have H : (∏ j : Fin 3, max 0 (b-|x j|)) ≤ b^3 := by
    calc
      _ ≤ ∏ _ : Fin 3, b := Finset.prod_le_prod₀ (fun _ _ => le_max_left _ _)
        (fun i _ => max_le hb.le (sub_le_self _ (abs_nonneg _)))
      _ = _ := by simp
  apply (mul_le_mul_of_nonneg_left H (show 0 ≤ (b⁻¹)^6 by positivity)).trans_eq
  field_simp [hb.ne']

lemma flatFineKernel_eq_zero {b : ℝ} (hb : 0 < b) (x : Space)
    (hx : 3*b^2 < ‖x‖^2) : flatFineKernel b x.ofLp = 0 := by
  have hj : ∃ j : Fin 3, b ≤ |x j| := by
    by_contra! H
    have Hs : ‖x‖^2 ≤ 3*b^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        _ ≤ ∑ _ : Fin 3, b^2 := Finset.sum_le_sum (fun j _ =>
          (sq_abs _).symm.trans_le ((sq_le_sq₀ (abs_nonneg _) hb.le).mpr (H j).le))
        _ = _ := by simp
    linarith
  obtain ⟨j,hj⟩ := hj
  unfold flatFineKernel
  rw [Finset.prod_eq_zero (Finset.mem_univ j)]
  · ring
  · exact max_eq_left (by dsimp; linarith)

noncomputable def fineKernel (b : ℝ) (x : Space) : ℝ :=
  ∫ Q : Rotation, flatFineKernel b (rotationIsometry Q x).ofLp ∂rotationMeasure

lemma rotated_flatKernel_continuous (b : ℝ) :
    Continuous (fun p : Rotation × Space => flatFineKernel b (rotationIsometry p.1 p.2).ofLp) :=
  (flatFineKernel_continuous b).comp ((PiLp.continuous_ofLp 2 _).comp rotation_action_continuous)

lemma rotated_flatKernel_integrable (b : ℝ) (x : Space) :
    Integrable (fun Q : Rotation => flatFineKernel b (rotationIsometry Q x).ofLp) rotationMeasure :=
  ((rotated_flatKernel_continuous b).comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma fineKernel_nonneg (b : ℝ) (x : Space) : 0 ≤ fineKernel b x :=
  integral_nonneg (fun _ => flatFineKernel_nonneg _ _)

lemma fineKernel_le {b : ℝ} (hb : 0 < b) (x : Space) : fineKernel b x ≤ (b⁻¹)^3 := by
  calc
    _ ≤ ∫ _ : Rotation, (b⁻¹)^3 ∂rotationMeasure :=
      integral_mono (rotated_flatKernel_integrable b x) (integrable_const _)
        (fun _ => flatFineKernel_le hb _)
    _ = _ := by simp

lemma fineKernel_eq_zero {b : ℝ} (hb : 0 < b) (x : Space)
    (hx : 3*b^2 < ‖x‖^2) : fineKernel b x = 0 := by
  unfold fineKernel
  calc
    _ = ∫ _ : Rotation, (0 : ℝ) ∂rotationMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun Q => flatFineKernel_eq_zero hb _ (by simpa using hx))
    _ = 0 := integral_zero _ _

lemma rotationIsometry_mul (P Q : Rotation) (x : Space) :
    rotationIsometry (P*Q) x = rotationIsometry P (rotationIsometry Q x) := by
  ext j
  simp only [rotationIsometry_apply]
  change (∑ k, (P.val * Q.val) j k * x k) = ∑ k, P.val j k * (∑ l, Q.val k l * x l)
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

instance : Measure.IsMulLeftInvariant rotationMeasure := by
  unfold rotationMeasure
  infer_instance

instance : Measure.IsHaarMeasure rotationMeasure := by
  unfold rotationMeasure
  infer_instance

instance : Measure.IsMulRightInvariant rotationMeasure where
  map_mul_right_eq_self P := by
    have : IsProbabilityMeasure (Measure.map (· * P) rotationMeasure) := inferInstance
    have H := Measure.isMulInvariant_eq_smul_of_compactSpace
      (Measure.map (· * P) rotationMeasure) rotationMeasure
    have H1 := congrArg (fun μ : Measure Rotation => μ univ) H
    simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at H1
    have H2 : (Measure.map (· * P) rotationMeasure).haarScalarFactor rotationMeasure = 1 :=
      ENNReal.coe_injective (by simpa using H1.symm)
    rw [H2, one_smul] at H
    exact H

lemma fineKernel_rotation (b : ℝ) (P : Rotation) (x : Space) :
    fineKernel b (rotationIsometry P x) = fineKernel b x := by
  unfold fineKernel
  simp_rw [← rotationIsometry_mul]
  exact integral_mul_right_eq_self (μ := rotationMeasure) (fun Q : Rotation => flatFineKernel b (rotationIsometry Q x).ofLp) P

lemma tent_continuous (b : ℝ) : Continuous (fun x : ℝ => max 0 (b-|x|)) := by fun_prop
lemma tent_eq_zero {b : ℝ} (x : ℝ) (hx : x ∉ Icc (-b) b) : max 0 (b-|x|) = 0 := by
  apply max_eq_left
  have : b ≤ |x| := by
    by_contra! h
    exact hx ⟨by linarith [(neg_abs_le x)], by linarith [le_abs_self x]⟩
  linarith
lemma tent_integrable (b : ℝ) : Integrable (fun x : ℝ => max 0 (b-|x|)) := by
  have H := (tent_continuous b).integrableOn_Icc (μ := volume) (a := -b) (b := b)
  have he : (Icc (-b) b).indicator (fun x : ℝ => max 0 (b-|x|)) =
      (fun x : ℝ => max 0 (b-|x|)) := by
    funext x
    by_cases hx : x ∈ Icc (-b) b
    · simp [hx]
    · simp [hx, tent_eq_zero x hx]
  rw [← he]
  exact H.integrable_indicator measurableSet_Icc
lemma tent_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, max 0 (b-|x|)) = b^2 := by
  have hi (a c : ℝ) := (tent_continuous b).intervalIntegrable (μ := volume) a c
  calc
    _ = ∫ x in Icc (-b) b, max 0 (b-|x|) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => tent_eq_zero x hx)).symm
    _ = ∫ x in (-b)..b, max 0 (b-|x|) := by
      rw [intervalIntegral.integral_of_le (by linarith : -b ≤ b), integral_Icc_eq_integral_Ioc]
    _ = (∫ x in (-b)..0, max 0 (b-|x|)) + ∫ x in (0 : ℝ)..b, max 0 (b-|x|) :=
      (intervalIntegral.integral_add_adjacent_intervals (hi (-b) 0) (hi 0 b)).symm
    _ = (∫ x in (-b)..0, b+x) + ∫ x in (0 : ℝ)..b, b-x := by
      congr 1 <;> apply intervalIntegral.integral_congr
      · intro x hx
        dsimp only
        rw [uIcc_of_le (by linarith)] at hx
        rw [abs_of_nonpos hx.2, sub_neg_eq_add, max_eq_right (by linarith [hx.1])]
      · intro x hx
        dsimp only
        rw [uIcc_of_le hb.le] at hx
        rw [abs_of_nonneg hx.1, max_eq_right (by linarith [hx.2])]
    _ = b^2 := by
      rw [intervalIntegral.integral_add (intervalIntegrable_const (c := b)) (show IntervalIntegrable (fun x : ℝ => x) volume _ _ from continuous_id.intervalIntegrable _ _),
        intervalIntegral.integral_sub (intervalIntegrable_const (c := b)) (show IntervalIntegrable (fun x : ℝ => x) volume _ _ from continuous_id.intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
      ring

lemma flatFineKernel_integrable (b : ℝ) : Integrable (flatFineKernel b) := by
  exact ((Integrable.fintype_prod_dep (fun _ : Fin 3 => tent_integrable b)).const_mul ((b⁻¹)^6))

lemma flatFineKernel_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : Fin 3 → ℝ, flatFineKernel b x) = 1 := by
  unfold flatFineKernel
  rw [integral_const_mul,
    integral_fintype_prod_volume_eq_prod (fun (_ : Fin 3) (u : ℝ) => max 0 (b-|u|))]
  simp_rw [tent_integral hb]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hb.ne']

lemma flatFineKernel_space_integrable (b : ℝ) :
    Integrable (fun x : Space => flatFineKernel b x.ofLp) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).integrable_comp_of_integrable (flatFineKernel_integrable b)

lemma flatFineKernel_space_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : Space, flatFineKernel b x.ofLp) = 1 := by
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp' (flatFineKernel b)).trans
    (flatFineKernel_integral hb)

lemma rotated_flatKernel_space_integrable (b : ℝ) (Q : Rotation) :
    Integrable (fun x : Space => flatFineKernel b (rotationIsometry Q x).ofLp) :=
  (rotationIsometry Q).measurePreserving.integrable_comp_of_integrable (flatFineKernel_space_integrable b)

lemma rotated_flatKernel_space_integral {b : ℝ} (hb : 0 < b) (Q : Rotation) :
    (∫ x : Space, flatFineKernel b (rotationIsometry Q x).ofLp) = 1 := by
  exact ((show MeasurePreserving (rotationIsometry Q).toHomeomorph.toMeasurableEquiv volume volume from
    (rotationIsometry Q).measurePreserving).integral_comp' (fun x : Space => flatFineKernel b x.ofLp)).trans
    (flatFineKernel_space_integral hb)

lemma rotated_flatKernel_integrable_prod {b : ℝ} (hb : 0 < b) :
    Integrable (fun p : Rotation × Space => flatFineKernel b (rotationIsometry p.1 p.2).ofLp)
      (rotationMeasure.prod volume) := by
  apply (integrable_prod_iff (rotated_flatKernel_continuous b).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun Q => rotated_flatKernel_space_integrable b Q)
  · simp_rw [Real.norm_of_nonneg (flatFineKernel_nonneg ..)]
    simp_rw [rotated_flatKernel_space_integral hb]
    exact integrable_const _

lemma fineKernel_integrable {b : ℝ} (hb : 0 < b) : Integrable (fineKernel b) :=
  (rotated_flatKernel_integrable_prod hb).integral_prod_right

lemma fineKernel_integral {b : ℝ} (hb : 0 < b) : (∫ x, fineKernel b x) = 1 := by
  unfold fineKernel
  rw [← integral_integral_swap (rotated_flatKernel_integrable_prod hb)]
  simp_rw [rotated_flatKernel_space_integral hb]
  simp

lemma rpow_five_thirds_le_linear {a A : ℝ} (ha : 0 ≤ a) (hA : a ≤ A) :
    a^(5/3 : ℝ) ≤ A^(2/3 : ℝ)*a := by
  calc
    _ = a^(2/3 : ℝ)*a := by
      rw [show (5/3 : ℝ) = 2/3 + 1 by norm_num, Real.rpow_add_one' ha (by norm_num)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha hA (by norm_num)) ha

lemma fineKernel_measurable (b : ℝ) : Measurable (fineKernel b) :=
  (rotated_flatKernel_continuous b).stronglyMeasurable.integral_prod_left'.measurable

noncomputable def fineDensity {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) : ℝ :=
  ∑ i, fineKernel b (y-x i)
noncomputable def rotatedFlatDensity {n : ℕ} (b : ℝ) (Q : Rotation) (x : Fin n → Space) (y : Space) : ℝ :=
  ∑ i, flatFineKernel b (rotationIsometry Q (y-x i)).ofLp

lemma fineDensity_nonneg {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) :
    0 ≤ fineDensity b x y := Finset.sum_nonneg (fun _ _ => fineKernel_nonneg ..)
lemma fineDensity_le {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) (y : Space) :
    fineDensity b x y ≤ n*(b⁻¹)^3 := by
  calc
    _ ≤ ∑ _ : Fin n, (b⁻¹)^3 := Finset.sum_le_sum (fun _ _ => fineKernel_le hb _)
    _ = _ := by simp
lemma rotatedFlatDensity_nonneg {n : ℕ} (b : ℝ) (Q : Rotation) (x : Fin n → Space) (y : Space) :
    0 ≤ rotatedFlatDensity b Q x y := Finset.sum_nonneg (fun _ _ => flatFineKernel_nonneg ..)
lemma rotatedFlatDensity_le {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) (y : Space) :
    rotatedFlatDensity b Q x y ≤ n*(b⁻¹)^3 := by
  calc
    _ ≤ ∑ _ : Fin n, (b⁻¹)^3 := Finset.sum_le_sum (fun _ _ => flatFineKernel_le hb _)
    _ = _ := by simp

lemma fineDensity_measurable {n : ℕ} (b : ℝ) (x : Fin n → Space) :
    Measurable (fineDensity b x) :=
  Finset.measurable_sum _ (fun _ _ => (fineKernel_measurable b).comp (measurable_id.sub_const _))

lemma rotatedFlatDensity_continuous {n : ℕ} (b : ℝ) (x : Fin n → Space) :
    Continuous (fun p : Rotation × Space => rotatedFlatDensity b p.1 x p.2) := by
  apply continuous_finsetSum
  intro i _
  have hs : Continuous (fun p : Rotation × Space => (p.1, p.2 - x i)) :=
    continuous_fst.prodMk (continuous_snd.sub continuous_const)
  have hc := (rotated_flatKernel_continuous b).comp hs
  dsimp only [Function.comp_def] at hc
  exact hc

lemma fineDensity_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    Integrable (fineDensity b x) := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_sub_right volume (x i)).integrable_comp_of_integrable (fineKernel_integrable hb)

lemma fineDensity_integral {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    (∫ y, fineDensity b x y) = (n : ℝ) := by
  have hi (i : Fin n) : Integrable (fun y : Space => fineKernel b (y - x i)) :=
    (measurePreserving_sub_right volume (x i)).integrable_comp_of_integrable (fineKernel_integrable hb)
  unfold fineDensity
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_sub_right_eq_self, fineKernel_integral hb]
  simp

lemma rotatedFlatDensity_integrable {n : ℕ} (b : ℝ) (Q : Rotation) (x : Fin n → Space) :
    Integrable (rotatedFlatDensity b Q x) := by
  apply integrable_finsetSum
  intro i _
  exact (measurePreserving_sub_right volume (x i)).integrable_comp_of_integrable
    (rotated_flatKernel_space_integrable b Q)

lemma rotatedFlatDensity_integral {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) :
    (∫ y, rotatedFlatDensity b Q x y) = (n : ℝ) := by
  have hi (i : Fin n) : Integrable (fun y : Space => flatFineKernel b (rotationIsometry Q (y-x i)).ofLp) :=
    (measurePreserving_sub_right volume (x i)).integrable_comp_of_integrable
      (rotated_flatKernel_space_integrable b Q)
  unfold rotatedFlatDensity
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have hrot (i : Fin n) : (∫ y : Space, flatFineKernel b (rotationIsometry Q (y-x i)).ofLp) = 1 := by
    change (∫ y : Space, (fun z : Space => flatFineKernel b (rotationIsometry Q z).ofLp) (y-x i)) = 1
    exact (integral_sub_right_eq_self (fun z : Space => flatFineKernel b (rotationIsometry Q z).ofLp) (x i)).trans
      (rotated_flatKernel_space_integral hb Q)
  simp_rw [hrot]
  simp

lemma rotatedFlatDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) :
    Integrable (fun y => rotatedFlatDensity b Q x y ^ (5/3 : ℝ)) := by
  apply ((rotatedFlatDensity_integrable b Q x).const_mul ((n*(b⁻¹)^3)^(2/3:ℝ))).mono'
  · exact (((rotatedFlatDensity_continuous b x).comp (continuous_const.prodMk continuous_id)).measurable.pow_const _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)]
      exact rpow_five_thirds_le_linear (rotatedFlatDensity_nonneg ..) (rotatedFlatDensity_le hb ..))

lemma rotatedFlatDensity_power_integral_le {n : ℕ} {b : ℝ} (hb : 0 < b) (Q : Rotation) (x : Fin n → Space) :
    (∫ y, rotatedFlatDensity b Q x y ^ (5/3 : ℝ)) ≤ ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n := by
  calc
    _ ≤ ∫ y, ((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ) * rotatedFlatDensity b Q x y :=
      integral_mono (rotatedFlatDensity_power_integrable hb Q x)
        ((rotatedFlatDensity_integrable b Q x).const_mul _) (fun _ =>
          rpow_five_thirds_le_linear (rotatedFlatDensity_nonneg ..) (rotatedFlatDensity_le hb ..))
    _ = _ := by rw [integral_const_mul, rotatedFlatDensity_integral hb]

lemma rotatedFlatDensity_power_integrable_prod {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    Integrable (fun p : Rotation × Space => rotatedFlatDensity b p.1 x p.2^(5/3:ℝ))
      (rotationMeasure.prod volume) := by
  have hm := (rotatedFlatDensity_continuous b x).measurable.pow_const (5/3:ℝ)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun Q => rotatedFlatDensity_power_integrable hb Q x)
  · simp_rw [Real.norm_of_nonneg (Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)]
    apply (integrable_const (((n:ℝ)*(b⁻¹)^3)^(2/3:ℝ)*n)).mono'
      hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun Q => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _))]
      exact rotatedFlatDensity_power_integral_le hb Q x)

lemma fineDensity_eq_angularAverage {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) :
    fineDensity b x y = ∫ Q, rotatedFlatDensity b Q x y ∂rotationMeasure := by
  unfold fineDensity fineKernel rotatedFlatDensity
  exact (integral_finsetSum _ (fun _ _ => rotated_flatKernel_integrable b _)).symm

lemma rotatedFlatDensity_angular_integrable {n : ℕ} (b : ℝ) (x : Fin n → Space) (y : Space) :
    Integrable (fun Q => rotatedFlatDensity b Q x y) rotationMeasure :=
  integrable_finsetSum _ (fun _ _ => rotated_flatKernel_integrable b _)

lemma rotatedFlatDensity_power_angular_integrable {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) (y : Space) :
    Integrable (fun Q => rotatedFlatDensity b Q x y^(5/3:ℝ)) rotationMeasure := by
  apply (integrable_const (((n:ℝ)*(b⁻¹)^3)^(5/3:ℝ))).mono'
  · exact (((rotatedFlatDensity_continuous b x).comp (continuous_id.prodMk continuous_const)).measurable.pow_const _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun Q => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (rotatedFlatDensity_nonneg ..) _)]
      exact Real.rpow_le_rpow (rotatedFlatDensity_nonneg ..) (rotatedFlatDensity_le hb ..) (by norm_num))

lemma fineDensity_Jensen {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) (y : Space) :
    fineDensity b x y^(5/3:ℝ) ≤ ∫ Q, rotatedFlatDensity b Q x y^(5/3:ℝ) ∂rotationMeasure := by
  rw [fineDensity_eq_angularAverage]
  exact (convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).map_integral_le
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun _ => rotatedFlatDensity_nonneg ..))
    (rotatedFlatDensity_angular_integrable b x y)
    (rotatedFlatDensity_power_angular_integrable hb x y)

noncomputable def fineDensityPower {n : ℕ} (b : ℝ) (x : Fin n → Space) : ℝ :=
  ∫ y, fineDensity b x y^(5/3:ℝ)

lemma fineDensityPower_le_angularAverage {n : ℕ} {b : ℝ} (hb : 0 < b) (x : Fin n → Space) :
    fineDensityPower b x ≤ ∫ Q, ∫ y, rotatedFlatDensity b Q x y^(5/3:ℝ) ∂volume ∂rotationMeasure := by
  have hi := rotatedFlatDensity_power_integrable_prod hb x
  have hm := (fineDensity_measurable b x).pow_const (5/3:ℝ)
  have hl := hi.integral_prod_right.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (fineDensity_nonneg ..) _)]
      exact fineDensity_Jensen hb x y))
  exact (integral_mono hl hi.integral_prod_right (fun y => fineDensity_Jensen hb x y)).trans_eq
    (integral_integral_swap hi).symm

lemma rotatedFlatDensityPower_eq {n : ℕ} (b : ℝ) (Q : Rotation) (x : Configuration n) :
    (∫ y, rotatedFlatDensity b Q (position x) y ^ (5/3:ℝ)) =
      flatDensityPower b (commonIsometry (rotationIsometry Q) x).ofLp := by
  let f : Space → ℝ := fun y => (∑ i : Fin n, flatFineKernel b
    (y.ofLp - (rotationIsometry Q (position x i)).ofLp)) ^ (5/3:ℝ)
  have hrot := (show MeasurePreserving (rotationIsometry Q).toHomeomorph.toMeasurableEquiv volume volume from
    (rotationIsometry Q).measurePreserving).integral_comp' f
  have hpi := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun y : Fin 3 → ℝ => (∑ i : Fin n, flatFineKernel b
      (y - (rotationIsometry Q (position x i)).ofLp)) ^ (5/3:ℝ))
  calc
    _ = ∫ y, f (rotationIsometry Q y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only [f, rotatedFlatDensity]
        simp only [map_sub]
        rfl)
    _ = ∫ y, f y := hrot
    _ = _ := by
      convert hpi using 1 <;> rfl

end Coulomb

end

end OAI
