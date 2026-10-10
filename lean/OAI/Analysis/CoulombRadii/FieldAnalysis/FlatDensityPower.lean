import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.GridIndex

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
namespace Coulomb
open scoped Classical
open scoped Classical
open Filter
open scoped Convolution
open ContinuousLinearMap

lemma finiteCubeMeasure_real_univ {b : ℝ} (hb : 0 < b) (I : Type*) [Fintype I] :
    (finiteCubeMeasure b I).real univ = b ^ Fintype.card I := by
  simp [Measure.real, finiteCubeMeasure, Measure.pi_univ, hb.le]

lemma finiteCubeMeasure_neZero {b : ℝ} (hb : 0 < b) (I : Type*) [Fintype I] :
    NeZero (finiteCubeMeasure b I) := by
  constructor
  intro h
  have H := finiteCubeMeasure_real_univ hb I
  rw [h] at H
  simp only [Measure.real, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero] at H
  exact (pow_pos hb _).ne' H.symm

lemma translatedGridDensity_nonneg {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    0 ≤ translatedGridDensity b t x y := by
  apply mul_nonneg (pow_nonneg (inv_nonneg.mpr hb.le) _)
  exact Finset.sum_nonneg (fun _ _ => sameGridCell_nonneg ..)

lemma translatedGridDensity_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    translatedGridDensity b t x y ≤ (b⁻¹)^3*n := by
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.mpr hb.le) _)
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => sameGridCell_le_one ..)
    _ = _ := by simp

lemma translatedGridDensity_measurable {n : ℕ} (b : ℝ)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    Measurable (fun t => translatedGridDensity b t x y) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun _ _ => sameGridCell_measurable ..)

lemma translatedGridDensity_integrable {n : ℕ} (b : ℝ)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    Integrable (fun t => translatedGridDensity b t x y) (finiteCubeMeasure b (Fin 3)) := by
  exact Integrable.const_mul
    (integrable_finsetSum _ (fun _ _ => sameGridCell_integrable ..)) _

lemma translatedGridDensity_power_integrable_translation {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    Integrable (fun t => translatedGridDensity b t x y ^ (5/3:ℝ))
      (finiteCubeMeasure b (Fin 3)) := by
  apply (integrable_const (((b⁻¹)^3*n) ^ (5/3 : ℝ))).mono'
  · exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).measurable.comp
      (translatedGridDensity_measurable b x y)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (translatedGridDensity_nonneg hb ..) _)]
      exact Real.rpow_le_rpow (translatedGridDensity_nonneg hb ..)
        (translatedGridDensity_le hb ..) (by norm_num))

lemma flatFineKernel_Jensen {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) (y : Fin 3 → ℝ) :
    (∑ i : Fin n, flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ) ≤
      (b⁻¹)^3 * ∫ t, translatedGridDensity b t x y ^ (5/3:ℝ)
        ∂finiteCubeMeasure b (Fin 3) := by
  have := finiteCubeMeasure_neZero hb (Fin 3)
  have H := (convexOn_rpow (by norm_num : (1:ℝ) ≤ 5/3)).map_average_le
    (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 5/3)).continuousOn
    isClosed_Ici
    (Filter.Eventually.of_forall (fun t => translatedGridDensity_nonneg hb t x y))
    (translatedGridDensity_integrable b x y)
    (translatedGridDensity_power_integrable_translation hb x y)
  simp only [average_eq, finiteCubeMeasure_real_univ hb, Fintype.card_fin,
    ← inv_pow, smul_eq_mul, translatedGridDensity_integral hb] at H
  exact H

lemma gridCellDensity_power_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    (k : GridAssignment n) : Integrable (fun y => gridCellDensity b k y ^ (5/3 : ℝ)) := by
  let w : Set.range (gridCell k) → ℝ := fun c => (b⁻¹)^3 *
    (Fintype.card {i : Fin n // Set.rangeFactorization (gridCell k) i = c} : ℝ)
  have hd : Pairwise (fun c d : Set.range (gridCell k) =>
      Disjoint (gridBox b c.val) (gridBox b d.val)) := by
    intro c d hcd
    exact gridBox_disjoint hb (fun he => hcd (Subtype.ext he))
  have he : (fun y => gridCellDensity b k y ^ (5/3 : ℝ)) = fun y =>
      ∑ c : Set.range (gridCell k), (gridBox b c.val).indicator
        (fun _ => (w c)^(5/3 : ℝ)) y := by
    funext y
    exact sum_indicator_rpow_disjoint (fun c : Set.range (gridCell k) => gridBox b c.val)
      hd w (by norm_num) y
  rw [he]
  apply integrable_finsetSum
  intro c _
  exact (integrableOn_const (by rw [gridBox_volume]; finiteness)).integrable_indicator
    (gridBox_measurable b c.val)

lemma translatedGridDensity_power_integrable_space {n : ℕ} {b : ℝ} (hb : 0 < b)
    (t : Fin 3 → ℝ) (x : (Fin n × Fin 3) → ℝ) :
    Integrable (fun y => translatedGridDensity b t x y ^ (5/3:ℝ)) := by
  simp_rw [translatedGridDensity_eq_cell hb]
  exact (measurePreserving_add_right volume t).integrable_comp
    (gridCellDensity_power_integrable hb _).aestronglyMeasurable |>.mpr
      (gridCellDensity_power_integrable hb _)

lemma sameCell1_measurable_pair (b : ℝ) :
    Measurable (fun p : ℝ × ℝ => sameCell1 b p.1 p.2) := by
  unfold sameCell1
  exact measurable_const.ite
    (measurableSet_eq_fun (Int.measurable_ceil.comp (measurable_fst.div_const b))
      (Int.measurable_ceil.comp (measurable_snd.div_const b))) measurable_const

lemma translatedGridDensity_measurable_pair {n : ℕ} (b : ℝ)
    (x : (Fin n × Fin 3) → ℝ) :
    Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      translatedGridDensity b p.1 x p.2) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_prod
  intro j _
  have hjt : Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 j) :=
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j).comp measurable_fst
  have hjy : Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.2 j) :=
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j).comp measurable_snd
  exact (sameCell1_measurable_pair b).comp
    ((hjt.const_add (x (i,j))).prodMk (hjy.add hjt))

lemma translatedGridDensity_power_integrable_prod {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      translatedGridDensity b p.1 x p.2 ^ (5/3:ℝ))
      ((finiteCubeMeasure b (Fin 3)).prod volume) := by
  have hm := (translatedGridDensity_measurable_pair b x).pow_const (5/3:ℝ)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t => translatedGridDensity_power_integrable_space hb t x)
  · have he (t : Fin 3 → ℝ) :
        (∫ y, ‖translatedGridDensity b t x y ^ (5/3:ℝ)‖) =
          (b⁻¹)^2 * gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) := by
      simp_rw [Real.norm_of_nonneg (Real.rpow_nonneg (translatedGridDensity_nonneg hb ..) _)]
      exact translatedGridDensity_power_integral hb t x
    simp_rw [he]
    have hki : Measurable (fun t : Fin 3 → ℝ =>
        gridIndex b (fun ij : Fin n × Fin 3 => x ij+t ij.2)) := by
      apply (gridIndex_measurable b).comp
      apply Measurable.of_eval
      intro ij
      exact (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) ij.2).const_add (x ij)
    have hk := (measurable_of_countable (gridLeadingCount (n := n))).comp hki
    apply (integrable_const ((b⁻¹)^2*(n:ℝ)^(5/3:ℝ))).mono'
      (hk.const_mul _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by
      dsimp only [Function.comp_apply, gridLeadingCount]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (groupLeadingCount_nonneg _))]
      exact mul_le_mul_of_nonneg_left (groupLeadingCount_le _) (sq_nonneg _))

lemma flatFineKernel_measurable (b : ℝ) : Measurable (flatFineKernel b) := by
  apply Measurable.const_mul
  apply Finset.measurable_prod
  intro j _
  exact measurable_const.max (measurable_const.sub
    (measurable_pi_apply (X := fun _ : Fin 3 => ℝ) j).abs)

lemma flatFineKernel_nonneg (b : ℝ) (y : Fin 3 → ℝ) : 0 ≤ flatFineKernel b y :=
  mul_nonneg (by positivity) (Finset.prod_nonneg (fun _ _ => le_max_left _ _))

lemma flatFineKernel_power_integral_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    (x : (Fin n × Fin 3) → ℝ) :
    (∫ y : Fin 3 → ℝ, (∑ i : Fin n,
      flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ)) ≤
    (b⁻¹)^5 * ∫ t, gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2))
      ∂finiteCubeMeasure b (Fin 3) := by
  have hi := translatedGridDensity_power_integrable_prod hb x
  have hr := hi.integral_prod_right.const_mul ((b⁻¹)^3)
  have hlm : Measurable (fun y : Fin 3 → ℝ => (∑ i : Fin n,
      flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ)) := by
    apply Measurable.pow_const
    exact Finset.measurable_sum _ (fun i _ =>
      (flatFineKernel_measurable b).comp (measurable_id.sub_const _))
  have hnon (y : Fin 3 → ℝ) : 0 ≤
      (∑ i : Fin n, flatFineKernel b (y-(fun j => x (i,j)))) ^ (5/3:ℝ) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun _ _ => flatFineKernel_nonneg ..)) _
  have hl := hr.mono' hlm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_of_nonneg (hnon y)]
      exact flatFineKernel_Jensen hb x y))
  calc
    _ ≤ ∫ y : Fin 3 → ℝ, (b⁻¹)^3 * ∫ t,
        translatedGridDensity b t x y ^ (5/3:ℝ) ∂finiteCubeMeasure b (Fin 3) :=
      integral_mono hl hr (fun y => flatFineKernel_Jensen hb x y)
    _ = (b⁻¹)^3 * ∫ t, (b⁻¹)^2 *
        gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2))
          ∂finiteCubeMeasure b (Fin 3) := by
      rw [integral_const_mul, ← integral_integral_swap hi]
      simp_rw [translatedGridDensity_power_integral hb]
    _ = _ := by rw [integral_const_mul, ← mul_assoc, ← pow_add]

lemma shifted_grid_count_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) (t : Fin 3 → ℝ) :
    (b⁻¹)^2 * thomasFermiCoefficient *
      (∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
        gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) *
          ‖ψ.value s (WithLp.toLp 2 x)‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  have H := grid_count_expectation_kinetic_lower hn
    (ψ.translate (commonShift (-t))) (hψ.translate_common (-t)) hb
  rw [mass_translate, kinetic_translate] at H
  convert H using 1
  congr 2
  congr 1
  funext s
  have he := integral_add_right_eq_self (μ := volume) (fun x => gridLeadingCount (gridIndex b x) *
      ‖(ψ.translate (commonShift (-t))).value s (WithLp.toLp 2 x)‖^2)
    (fun ij => t ij.2)
  have hf (x : (Fin n × Fin 3) → ℝ) :
      (ψ.translate (commonShift (-t))).value s (WithLp.toLp 2 (x+(fun ij => t ij.2))) =
        ψ.value s (WithLp.toLp 2 x) := by
    change ψ.value s (_ + _) = _
    congr 1
    ext ij
    simp [commonShift]
  simp only [hf] at he
  convert he using 1

lemma translated_count_measurable {n : ℕ} (b : ℝ) :
    Measurable (fun p : (Fin 3 → ℝ) × ((Fin n × Fin 3) → ℝ) =>
      gridLeadingCount (gridIndex b (fun ij => p.2 ij + p.1 ij.2))) := by
  apply (measurable_of_countable (gridLeadingCount (n := n))).comp
  apply (gridIndex_measurable b).comp
  apply Measurable.of_eval
  intro ij
  exact ((measurable_pi_apply (X := fun _ : Fin n × Fin 3 => ℝ) ij).comp measurable_snd).add
    ((measurable_pi_apply (X := fun _ : Fin 3 => ℝ) ij.2).comp measurable_fst)

lemma translated_count_integrable {n : ℕ} {b : ℝ} (_hb : 0 < b)
    {w : ((Fin n × Fin 3) → ℝ) → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun p : (Fin 3 → ℝ) × ((Fin n × Fin 3) → ℝ) =>
      gridLeadingCount (gridIndex b (fun ij => p.2 ij+p.1 ij.2)) * w p.2)
      ((finiteCubeMeasure b (Fin 3)).prod volume) := by
  have hwm := hw.aestronglyMeasurable.comp_snd (μ := finiteCubeMeasure b (Fin 3))
  have hm := (translated_count_measurable b).aestronglyMeasurable.mul hwm
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun t => by
      apply (hw.const_mul ((n:ℝ)^(5/3:ℝ))).mono'
        (((translated_count_measurable b).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul hw.aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun x => by
        change ‖gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x‖ ≤ _
        simp only [gridLeadingCount]
        rw [Real.norm_of_nonneg (mul_nonneg (groupLeadingCount_nonneg _) (hw0 x))]
        exact mul_le_mul_of_nonneg_right (groupLeadingCount_le _) (hw0 x)))
  · have H (t : Fin 3 → ℝ) :
        ∫ x, ‖gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x‖ ≤
          (n:ℝ)^(5/3:ℝ) * ∫ x, w x := by
      rw [← integral_const_mul]
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
      · exact hw.const_mul _
      · exact Filter.Eventually.of_forall (fun x => by
          change ‖gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x‖ ≤ _
          simp only [gridLeadingCount]
          rw [Real.norm_of_nonneg (mul_nonneg (groupLeadingCount_nonneg _) (hw0 x))]
          exact mul_le_mul_of_nonneg_right (groupLeadingCount_le _) (hw0 x))
    apply (integrable_const ((n:ℝ)^(5/3:ℝ) * ∫ x, w x)).mono'
      hm.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact H t)

noncomputable def flatDensityPower {n : ℕ} (b : ℝ) (x : (Fin n × Fin 3) → ℝ) : ℝ :=
  ∫ y : Fin 3 → ℝ, (∑ i : Fin n,
    flatFineKernel b (y-(fun j => x (i,j))))^(5/3:ℝ)

lemma flatDensityPower_nonneg {n : ℕ} (b : ℝ) (x : (Fin n × Fin 3) → ℝ) :
    0 ≤ flatDensityPower b x := by
  apply integral_nonneg
  intro y
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg (fun _ _ => flatFineKernel_nonneg ..)

lemma flatDensityPower_measurable {n : ℕ} (b : ℝ) :
    Measurable (flatDensityPower (n := n) b) := by
  have hm : Measurable (fun p : ((Fin n × Fin 3) → ℝ) × (Fin 3 → ℝ) =>
      (∑ i : Fin n, flatFineKernel b (p.2-(fun j => p.1 (i,j))))^(5/3:ℝ)) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    apply (flatFineKernel_measurable b).comp
    apply measurable_snd.sub
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply (X := fun _ : Fin n × Fin 3 => ℝ) (i,j)).comp measurable_fst
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma weighted_flatDensityPower_integrable {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : ((Fin n × Fin 3) → ℝ) → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    Integrable (fun x => flatDensityPower b x * w x) := by
  have hi := translated_count_integrable hb hw hw0
  apply (hi.integral_prod_right.const_mul ((b⁻¹)^5)).mono'
    ((flatDensityPower_measurable b).aestronglyMeasurable.mul hw.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    change ‖flatDensityPower b x * w x‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (flatDensityPower_nonneg b x) (hw0 x))]
    have H := mul_le_mul_of_nonneg_right (flatFineKernel_power_integral_le hb x) (hw0 x)
    dsimp only [flatDensityPower] at *
    rw [integral_mul_const]
    nlinarith [H])

lemma weighted_flatDensityPower_le {n : ℕ} {b : ℝ} (hb : 0 < b)
    {w : ((Fin n × Fin 3) → ℝ) → ℝ} (hw : Integrable w) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x, flatDensityPower b x * w x) ≤
      (b⁻¹)^5 * ∫ t, (∫ x, gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x)
        ∂finiteCubeMeasure b (Fin 3) := by
  have hi := translated_count_integrable hb hw hw0
  calc
    _ ≤ ∫ x, (b⁻¹)^5 * ∫ t,
        gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w x
          ∂finiteCubeMeasure b (Fin 3) := by
      apply integral_mono (weighted_flatDensityPower_integrable hb hw hw0)
        (hi.integral_prod_right.const_mul _)
      intro x
      dsimp only
      rw [integral_mul_const]
      exact (mul_le_mul_of_nonneg_right (flatFineKernel_power_integral_le hb x) (hw0 x)).trans_eq
        (mul_assoc ..)
    _ = _ := by rw [integral_const_mul, ← integral_integral_swap hi]

theorem flat_fine_density_kinetic_lower {n : ℕ} (hn : 0 < n) (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) {b : ℝ} (hb : 0 < b) :
    thomasFermiCoefficient *
      (∑ s, ∫ x : (Fin n × Fin 3) → ℝ,
        flatDensityPower b x * ‖ψ.value s (WithLp.toLp 2 x)‖^2) -
      ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ ≤
      kinetic ψ := by
  let w (s : Spins n) (x : (Fin n × Fin 3) → ℝ) := ‖ψ.value s (WithLp.toLp 2 x)‖^2
  have hw (s : Spins n) : Integrable (w s) :=
    (((ψ.value_L2 s).comp_measurePreserving
      (PiLp.volume_preserving_toLp (Fin n × Fin 3))).integrable_norm_pow (p := 2) (by decide))
  have hw0 (s : Spins n) (x) : 0 ≤ w s x := sq_nonneg _
  let B (t : Fin 3 → ℝ) := ∑ s, ∫ x,
    gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w s x
  have hBs (s : Spins n) : Integrable (fun t : Fin 3 → ℝ =>
      ∫ x, gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w s x)
        (finiteCubeMeasure b (Fin 3)) :=
    (translated_count_integrable hb (hw s) (hw0 s)).integral_prod_left
  have hB : Integrable B (finiteCubeMeasure b (Fin 3)) :=
    integrable_finsetSum _ (fun s _ => hBs s)
  have hL : (∑ s, ∫ x, flatDensityPower b x * w s x) ≤
      (b⁻¹)^5 * ∫ t, B t ∂finiteCubeMeasure b (Fin 3) := by
    calc
      _ ≤ ∑ s, (b⁻¹)^5 * ∫ t, (∫ x,
          gridLeadingCount (gridIndex b (fun ij => x ij+t ij.2)) * w s x)
            ∂finiteCubeMeasure b (Fin 3) :=
        Finset.sum_le_sum (fun s _ => weighted_flatDensityPower_le hb (hw s) (hw0 s))
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact (integral_finsetSum _ (fun s _ => hBs s)).symm
  let e := ((b⁻¹)^2 * ((Real.pi^2/2)*neumannBoundary) * (n : ℝ)^(4/3 : ℝ)) * mass ψ
  have Hp (t : Fin 3 → ℝ) : (b⁻¹)^2 * thomasFermiCoefficient * B t - e ≤ kinetic ψ :=
    shifted_grid_count_kinetic_lower hn ψ hψ hb t
  have H := integral_mono ((hB.const_mul _).sub (integrable_const e))
    (integrable_const (kinetic ψ)) Hp
  change (∫ t, (b⁻¹)^2 * thomasFermiCoefficient * B t - e ∂finiteCubeMeasure b (Fin 3)) ≤
    ∫ t, kinetic ψ ∂finiteCubeMeasure b (Fin 3) at H
  rw [integral_sub (hB.const_mul _) (integrable_const e), integral_const_mul,
    integral_const, integral_const, finiteCubeMeasure_real_univ hb, Fintype.card_fin,
    smul_eq_mul] at H
  simp only [smul_eq_mul] at H
  have HS := mul_le_mul_of_nonneg_left H (show 0 ≤ (b⁻¹)^3 by positivity)
  have Hscaled : thomasFermiCoefficient * ((b⁻¹)^5 * ∫ t, B t ∂finiteCubeMeasure b (Fin 3)) - e ≤
      kinetic ψ := by
    have hs3 : (b⁻¹)^3 * b^3 = 1 := by field_simp [hb.ne']
    have hleft : (b⁻¹)^3 * ((b⁻¹)^2 * thomasFermiCoefficient *
        (∫ t, B t ∂finiteCubeMeasure b (Fin 3)) - b^3 * e) =
        thomasFermiCoefficient * ((b⁻¹)^5 * ∫ t, B t ∂finiteCubeMeasure b (Fin 3)) - e := by
      rw [mul_sub, ← mul_assoc _ (b^3) e, hs3, one_mul]
      congr 1
      ring
    rw [hleft, ← mul_assoc ((b⁻¹)^3) (b^3) (kinetic ψ), hs3, one_mul] at HS
    exact HS
  exact (sub_le_sub_right (mul_le_mul_of_nonneg_left hL thomasFermiCoefficient_pos.le) e).trans Hscaled

noncomputable def commonIsometry {n : ℕ} (L : Space ≃ₗᵢ[ℝ] Space) :
    Configuration n ≃ₗᵢ[ℝ] Configuration n where
  toFun := fun x => WithLp.toLp 2 (fun ij => L (position x ij.1) ij.2)
  invFun := fun x => WithLp.toLp 2 (fun ij => L.symm (position x ij.1) ij.2)
  left_inv := by
    intro x
    ext ij
    change L.symm (L (position x ij.1)) ij.2 = x ij
    simp [position]
  right_inv := by
    intro x
    ext ij
    change L (L.symm (position x ij.1)) ij.2 = x ij
    simp [position]
  map_add' := by
    intro x y
    ext ij
    change L (position x ij.1 + position y ij.1) ij.2 = _
    rw [map_add]
    rfl
  map_smul' := by
    intro c x
    ext ij
    change L (c • position x ij.1) ij.2 = _
    rw [map_smul]
    rfl
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ j, (L (position x i) j)^2) = ∑ j, (position x i j)^2
    rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq, L.norm_map]

end Coulomb

end

end OAI
