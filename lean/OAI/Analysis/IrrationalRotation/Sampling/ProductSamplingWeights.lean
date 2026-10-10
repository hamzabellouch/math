import OAI.Analysis.IrrationalRotation.Analysis.ScalarEndpointKernelBounds
import OAI.Analysis.IrrationalRotation.Product.ProductTailTrimming

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.SamplingWeights

open ScalarSampling

def coordinateWeight (I : Finset ℕ) (h α : ℝ) (i : ℕ) (s t : ℝ) : ℝ :=
  if i ∈ I then triangularKernel s t else rawKernel h α s t

def orbitWeight (D I : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (x : Base) : ℝ :=
  ∏ i ∈ D, coordinateWeight I h α i (circleRepresentative (x i))
    (Int.fract ((n : ℝ) * θ i))

def prefixWeight (D I : Finset ℕ) (h α : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (x : D → Circle) : ℝ :=
  ∏ i : D, coordinateWeight I h α i (circleRepresentative (x i))
    (Int.fract ((n : ℝ) * θ i))

def height (h α : ℝ) : ℝ := max 1 (h * α)⁻¹

theorem measurable_triangularKernel :
    Measurable (fun p : ℝ × ℝ => triangularKernel p.1 p.2) := by
  unfold triangularKernel
  simp only [Set.indicator_apply, mem_Ioo]
  exact Measurable.ite
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_const.sub measurable_fst)))
    measurable_const measurable_const

theorem measurable_coordinateWeight (I : Finset ℕ) (h α : ℝ) (i : ℕ) :
    Measurable (fun p : ℝ × ℝ => coordinateWeight I h α i p.1 p.2) := by
  by_cases hi : i ∈ I
  · simpa only [coordinateWeight, ite_eq_left hi] using measurable_triangularKernel
  · simpa only [coordinateWeight, ite_eq_right hi] using measurable_rawKernel_pair h α

theorem coordinateWeight_bounds (I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (i : ℕ) (s t : ℝ) :
    0 ≤ coordinateWeight I h α i s t ∧
      coordinateWeight I h α i s t ≤ height h α := by
  by_cases hi : i ∈ I
  · simp only [coordinateWeight, ite_eq_left hi, triangularKernel, Set.indicator_apply]
    split_ifs
    · exact ⟨zero_le_one, le_max_left _ _⟩
    · exact ⟨le_rfl, (by unfold height; positivity)⟩
  · simp only [coordinateWeight, ite_eq_right hi]
    exact ⟨(rawKernel_height hh hα).1,
      (rawKernel_height hh hα).2.trans (le_max_right _ _)⟩

theorem coordinateWeight_ne_zero_imp (I : Finset ℕ) {h α s t : ℝ}
    (hh : h ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1) (i : ℕ)
    (hw : coordinateWeight I h α i s t ≠ 0) :
    0 < t ∧ t < 1 - s := by
  by_cases hi : i ∈ I
  · simp only [coordinateWeight, ite_eq_left hi, triangularKernel] at hw
    by_contra hn
    exact hw (Set.indicator_of_notMem (show t ∉ Ioo 0 (1 - s) from hn) _)
  · simp only [coordinateWeight, ite_eq_right hi, rawKernel] at hw
    split_ifs at hw with hc
    · have ht : t ∈ Ioo 0 (h * delta s) := by
        by_contra hn
        exact hw (Set.indicator_of_notMem hn _)
      refine ⟨ht.1, ht.2.trans_le ?_⟩
      calc
        h * delta s ≤ 1 * delta s :=
          mul_le_mul_of_nonneg_right hh (delta_nonneg hs)
        _ ≤ 1 - s := by simpa only [one_mul, delta] using min_le_right s (1 - s)
    · exact (hw rfl).elim

theorem measurable_orbitWeight (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) : Measurable (orbitWeight D I h α θ n) := by
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_coordinateWeight I h α i).comp
    ((ProductCocycle.measurable_representative.comp (measurable_pi_apply i)).prodMk
      measurable_const)

theorem measurable_prefixWeight (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) : Measurable (prefixWeight D I h α θ n) := by
  apply Finset.measurable_prod
  intro i hi
  exact (measurable_coordinateWeight I h α i).comp
    ((ProductCocycle.measurable_representative.comp (measurable_pi_apply i)).prodMk
      measurable_const)

@[simp] theorem prefixWeight_restrict (D I : Finset ℕ) (h α : ℝ)
    (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    prefixWeight D I h α θ n (fun i : D => x i) = orbitWeight D I h α θ n x := by
  unfold prefixWeight orbitWeight
  rw [Finset.prod_coe_sort_eq_attach]
  exact Finset.prod_attach D (fun i => coordinateWeight I h α i
    (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)))

theorem orbitWeight_bounds (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    0 ≤ orbitWeight D I h α θ n x ∧
      orbitWeight D I h α θ n x ≤ height h α ^ D.card := by
  constructor
  · exact Finset.prod_nonneg fun i hi => (coordinateWeight_bounds I hh hα i _ _).1
  · calc
      orbitWeight D I h α θ n x ≤ ∏ _i ∈ D, height h α :=
        Finset.prod_le_prod₀ (fun i hi => (coordinateWeight_bounds I hh hα i _ _).1)
          (fun i hi => (coordinateWeight_bounds I hh hα i _ _).2)
      _ = _ := by simp

theorem orbitWeight_ne_zero_prefix_order (D I : Finset ℕ) {h α : ℝ}
    (hh : h ≤ 1) (θ : ℕ → ℝ) (n : ℕ) (x : Base)
    (hw : orbitWeight D I h α θ n x ≠ 0) :
    ∀ i ∈ D, circleRepresentative (x i) <
      circleRepresentative (rotationIterate θ (n : ℤ) x i) := by
  intro i hi
  have hs := ProductCocycle.representative_mem_Ico (x i)
  have hwi := (Finset.prod_ne_zero_iff.mp hw) i hi
  have ht := coordinateWeight_ne_zero_imp I hh ⟨hs.1, hs.2.le⟩ i hwi
  change ProductCocycle.representative (x i) <
    ProductCocycle.representative (x i + (((n : ℝ) * θ i : ℝ) : Circle))
  rw [ProductCocycle.representative_add,
    TailTrimming.fract_add_eq_fract_add_fract]
  rw [Int.fract_eq_self.mpr ⟨by linarith [ht.1, hs.1], by linarith [ht.2]⟩]
  linarith [ht.1]

theorem orbitWeight_ae_prefix_order (D I : Finset ℕ) {h α : ℝ}
    (hh : h ≤ 1) (θ : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure.withDensity (fun x => ENNReal.ofReal (orbitWeight D I h α θ n x)),
      ∀ i ∈ D, circleRepresentative (x i) ≤
        circleRepresentative (rotationIterate θ (n : ℤ) x i) := by
  apply (ae_withDensity_iff (measurable_orbitWeight D I h α θ n).ennreal_ofReal).2
  filter_upwards [] with x hx
  have hw : orbitWeight D I h α θ n x ≠ 0 := by
    intro hz
    exact hx (by rw [hz, ENNReal.ofReal_zero])
  exact fun i hi => (orbitWeight_ne_zero_prefix_order D I hh θ n x hw i hi).le

theorem memLp_orbitWeight (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (orbitWeight D I h α θ n) p baseMeasure := by
  apply MemLp.of_bound (measurable_orbitWeight D I h α θ n).aestronglyMeasurable
    (height h α ^ D.card)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (orbitWeight_bounds D I hh hα θ n x).1]
  exact (orbitWeight_bounds D I hh hα θ n x).2

theorem orbitWeight_finite (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) :
    IsFiniteMeasure (baseMeasure.withDensity
      (fun x => ENNReal.ofReal (orbitWeight D I h α θ n x))) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ x, ENNReal.ofReal (orbitWeight D I h α θ n x) ∂baseMeasure) ≤
        ∫⁻ _x : Base, ENNReal.ofReal (height h α ^ D.card) ∂baseMeasure :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (orbitWeight_bounds D I hh hα θ n x).2
    _ < ∞ := by simp

theorem orbitPairMeasure_finite (D I : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) (n : ℕ) :
    IsFiniteMeasure (TailTrimming.orbitPairMeasure θ n
      (fun x => ENNReal.ofReal (orbitWeight D I h α θ n x))) := by
  let := orbitWeight_finite D I hh hα θ n
  unfold TailTrimming.orbitPairMeasure
  infer_instance

theorem orbitAverageMeasure_finite (D I N : Finset ℕ) {h α : ℝ}
    (hh : 0 < h) (hα : 0 < α) (θ : ℕ → ℝ) :
    IsFiniteMeasure (TailTrimming.orbitAverageMeasure θ N
      (fun n x => ENNReal.ofReal (orbitWeight D I h α θ n x))) := by
  let (n : ℕ) := orbitPairMeasure_finite D I hh hα θ n
  unfold TailTrimming.orbitAverageMeasure
  by_cases hN : N = ∅
  · simp only [hN, Finset.card_empty, Nat.cast_zero, Finset.sum_empty,
      smul_zero]
    infer_instance
  · have hcard : (N.card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hN))
    exact Measure.smul_finite _ (ENNReal.inv_ne_top.mpr hcard)

theorem manuscript_orbitWeight_construction (D I : Finset ℕ) {m : ℕ}
    (hm : 200 ≤ m) (θ : ℕ → ℝ) (n : ℕ) :
    Measurable (orbitWeight D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) θ n) ∧
    (∀ x, 0 ≤ orbitWeight D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) θ n x) ∧
    IsFiniteMeasure (baseMeasure.withDensity (fun x => ENNReal.ofReal
      (orbitWeight D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) θ n x))) ∧
    (∀ᵐ x ∂baseMeasure.withDensity (fun x => ENNReal.ofReal
      (orbitWeight D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2) θ n x)),
      ∀ i ∈ D, circleRepresentative (x i) ≤
        circleRepresentative (rotationIterate θ (n : ℤ) x i)) := by
  obtain ⟨hh, hh1, hα, _⟩ := manuscript_parameters hm
  exact ⟨measurable_orbitWeight _ _ _ _ _ _,
    fun x => (orbitWeight_bounds D I hh hα θ n x).1,
    orbitWeight_finite D I hh hα θ n,
    orbitWeight_ae_prefix_order D I hh1 θ n⟩

end Invariant233.ProductModel.SamplingWeights

end

end OAI
