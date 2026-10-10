import Mathlib.MeasureTheory.Constructions.Pi
import OAI.NumberTheory.Catalan.Analysis.RealFactoredIntegral

namespace OAI

noncomputable section

namespace InternalCatalan

open MeasureTheory Set

def realCoordinateMeasure : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (4 * |x| / (1 + x ^ 2) ^ 2))

private theorem realCoordinateWeight_nonneg (x : ℝ) :
    0 ≤ 4 * |x| / (1 + x ^ 2) ^ 2 :=
  div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (sq_nonneg _)

private theorem measurable_realCoordinateDensity :
    Measurable (fun x : ℝ => ENNReal.ofReal (4 * |x| / (1 + x ^ 2) ^ 2)) := by
  fun_prop

theorem integrable_realCoordinateMeasure_iff (f : ℝ → ℝ) :
    Integrable f realCoordinateMeasure ↔
      Integrable (fun x => (4 * |x| / (1 + x ^ 2) ^ 2) * f x)
        (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  simpa only [realCoordinateMeasure,
    ENNReal.toReal_ofReal (realCoordinateWeight_nonneg _), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' measurable_realCoordinateDensity
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (g := f))

theorem integral_realCoordinateMeasure (f : ℝ → ℝ) :
    (∫ x, f x ∂realCoordinateMeasure) =
      ∫ x in Ioo (-1 : ℝ) 1, (4 * |x| / (1 + x ^ 2) ^ 2) * f x := by
  simpa only [realCoordinateMeasure,
    ENNReal.toReal_ofReal (realCoordinateWeight_nonneg _), smul_eq_mul] using
    (integral_withDensity_eq_integral_toReal_smul measurable_realCoordinateDensity
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f)

theorem realCoordinateMeasure_univ : realCoordinateMeasure univ = 2 := by
  have hi : Integrable (fun x : ℝ => 4 * |x| / (1 + x ^ 2) ^ 2)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    simpa only [mul_one] using
      (integrable_realPlaceMeasure_coordinate_iff (fun _ => (1 : ℝ))).mp
        (integrable_const 1)
  have hv : (∫ x in Ioo (-1 : ℝ) 1, 4 * |x| / (1 + x ^ 2) ^ 2) = 2 := by
    have h := integral_realPlaceMeasure_coordinate (fun _ => (1 : ℝ))
    norm_num [integral_const, measureReal_def, realPlaceMeasure_univ] at h
    exact h.symm
  rw [realCoordinateMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall realCoordinateWeight_nonneg), hv]
  norm_num

instance : IsFiniteMeasure realCoordinateMeasure where
  measure_univ_lt_top := by rw [realCoordinateMeasure_univ]; norm_num

theorem integral_realPlace_eq_coordinate (f : ℝ → ℝ) :
    (∫ t, f t ∂realPlaceMeasure) =
      ∫ x, f (realCoordinateInv x) ∂realCoordinateMeasure := by
  rw [integral_realCoordinateMeasure, integral_realPlaceMeasure_coordinate]

theorem integrable_realPlace_eq_coordinate_iff (f : ℝ → ℝ) :
    Integrable f realPlaceMeasure ↔
      Integrable (fun x => f (realCoordinateInv x)) realCoordinateMeasure := by
  rw [integrable_realCoordinateMeasure_iff,
    integrable_realPlaceMeasure_coordinate_iff]

theorem map_realCoordinateInv :
    Measure.map realCoordinateInv realCoordinateMeasure = realPlaceMeasure := by
  apply Measure.ext
  intro s hs
  have hr : (Measure.map realCoordinateInv realCoordinateMeasure).real s =
      realPlaceMeasure.real s := by
    rw [← integral_indicator_one hs, ← integral_indicator_one hs]
    exact (integral_map_of_stronglyMeasurable
      (μ := realCoordinateMeasure) (φ := realCoordinateInv)
      (f := s.indicator (1 : ℝ → ℝ))
      continuous_realCoordinateInv.measurable
      (stronglyMeasurable_const.indicator hs)).trans
        (integral_realPlace_eq_coordinate (s.indicator (1 : ℝ → ℝ))).symm
  have he := congrArg ENNReal.ofReal hr
  simpa only [measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using he

theorem measurePreserving_realCoordinateInv :
    MeasurePreserving realCoordinateInv realCoordinateMeasure realPlaceMeasure :=
  ⟨continuous_realCoordinateInv.measurable, map_realCoordinateInv⟩

theorem ae_realPlace_ne_zero : ∀ᵐ t ∂realPlaceMeasure, t ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  change realPlaceMeasure ({0} : Set ℝ) = 0
  unfold realPlaceMeasure
  exact measure_singleton _

theorem ae_realPlace_list_ne_zero (N : ℕ) :
    ∀ᵐ t ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure),
      ∀ i, t i ≠ 0 :=
  Filter.eventually_all.2 (fun i =>
    (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (n N) => realPlaceMeasure) (i := i)).eventually
        ae_realPlace_ne_zero)

theorem ae_realPlace_list_mem_ne_zero (N : ℕ) :
    ∀ᵐ t ∂Measure.pi (fun _ : Fin (n N) => realPlaceMeasure),
      ∀ i, t i ∈ Ioo (-1 : ℝ) 1 ∧ t i ≠ 0 :=
  Filter.eventually_all.2 (fun i =>
    (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (n N) => realPlaceMeasure) (i := i)).eventually
        (ae_realPlace_mem.and ae_realPlace_ne_zero))

theorem ae_realCoordinate_mem :
    ∀ᵐ x ∂realCoordinateMeasure, x ∈ Ioo (-1 : ℝ) 1 := by
  unfold realCoordinateMeasure
  apply (ae_withDensity_iff (by fun_prop)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact fun _ => hx

theorem ae_realCoordinate_ne_zero : ∀ᵐ x ∂realCoordinateMeasure, x ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  change realCoordinateMeasure ({0} : Set ℝ) = 0
  unfold realCoordinateMeasure
  exact measure_singleton _

theorem ae_realCoordinate_list_regular (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure),
      ∀ i, x i ∈ Ioo (-1 : ℝ) 1 ∧ x i ≠ 0 :=
  Filter.eventually_all.2 (fun i =>
    (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (n N) => realCoordinateMeasure) (i := i)).eventually
        (ae_realCoordinate_mem.and ae_realCoordinate_ne_zero))

open MeasureTheory Set

def realCoordinateListPairMeasure (N : ℕ) :
    Measure ((Fin (n N) → ℝ) × (Fin (n N) → ℝ)) :=
  (Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure)).prod
    (Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))

theorem measurePreserving_realCoordinate_list (N : ℕ) :
    MeasurePreserving (fun x : Fin (n N) → ℝ => fun i => realCoordinateInv (x i))
      (Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (Measure.pi (fun _ : Fin (n N) => realPlaceMeasure)) :=
  measurePreserving_pi _ _ (fun _ => measurePreserving_realCoordinateInv)

theorem measurePreserving_realCoordinate_pair (N : ℕ) :
    MeasurePreserving
      (fun p : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) =>
        ((fun i => realCoordinateInv (p.1 i)), p.2))
      (realCoordinateListPairMeasure N) (realListPairMeasure N) := by
  exact (measurePreserving_realCoordinate_list N).prod (MeasurePreserving.id _)

theorem integrable_coordinate_productRealIntegrand (N : ℕ) :
    Integrable (fun p =>
      productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2)
      (realCoordinateListPairMeasure N) :=
  (measurePreserving_realCoordinate_pair N).integrable_comp_of_integrable
    (integrable_productRealIntegrand N)

theorem integral_coordinate_productRealIntegrand (N : ℕ) :
    (∫ p, productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2
      ∂realCoordinateListPairMeasure N) =
      ∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N := by
  have hm := measurePreserving_realCoordinate_pair N
  have hsm : AEStronglyMeasurable
      (fun p => productRealIntegrand N p.1 p.2)
      (Measure.map
        (fun p : (Fin (n N) → ℝ) × (Fin (n N) → ℝ) =>
          ((fun i => realCoordinateInv (p.1 i)), p.2))
        (realCoordinateListPairMeasure N)) := by
    rw [hm.map_eq]
    exact (integrable_productRealIntegrand N).aestronglyMeasurable
  have he := (integral_map hm.aemeasurable hsm).symm
  rw [hm.map_eq] at he
  exact he

theorem determinant_eq_coordinateProductIntegral (N : ℕ) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ x, (∫ s, productRealIntegrand N (fun i => realCoordinateInv (x i)) s
        ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
        ∂Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure) := by
  rw [determinant_eq_productRealIntegral N]
  congr 1
  calc
    _ = ∫ p, productRealIntegrand N p.1 p.2 ∂realListPairMeasure N :=
      (integral_prod _ (integrable_productRealIntegrand N)).symm
    _ = ∫ p, productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2
        ∂realCoordinateListPairMeasure N :=
      (integral_coordinate_productRealIntegrand N).symm
    _ = _ := integral_prod _ (integrable_coordinate_productRealIntegrand N)

end InternalCatalan

end

end OAI
