import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestAlmostSure
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingCylinderWeights
import OAI.Analysis.IrrationalRotation.Product.ProductBaseDynamics
import OAI.Analysis.IrrationalRotation.Rotation.CircleRepresentative

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace Invariant233.ProductModel.SamplingWeights

private theorem indicator_one_eq_of_mem_iff {E F : Set ℝ} {s : ℝ}
    (h : s ∈ E ↔ s ∈ F) : E.indicator (fun _ => (1 : ℝ)) s =
      F.indicator (fun _ => (1 : ℝ)) s := by
  by_cases he : s ∈ E
  · rw [Set.indicator_of_mem he, Set.indicator_of_mem (h.mp he)]
  · have hf : s ∉ F := fun hf => he (h.mpr hf)
    rw [Set.indicator_of_notMem he, Set.indicator_of_notMem hf]

theorem measurePreserving_fract_add_unit (s : ℝ) :
    MeasurePreserving (fun t : ℝ => Int.fract (s + t))
      (volume.restrict (Ico (0 : ℝ) 1)) (volume.restrict (Ico (0 : ℝ) 1)) := by
  have hm : MeasurePreserving (fun t : ℝ => (t : UnitAddCircle))
      (volume.restrict (Ico (0 : ℝ) 1)) volume := by
    rw [restrict_Ico_eq_restrict_Ioc]
    simpa using UnitAddCircle.measurePreserving_mk 0
  have h := CocycleSupport.measurePreserving_circleRepresentative.comp
    ((measurePreserving_add_left (volume : Measure UnitAddCircle)
      (s : UnitAddCircle)).comp hm)
  convert h using 1
  funext t
  simp only [Function.comp_def, ← AddCircle.coe_add]
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (s + t)).symm

theorem testedProduct_first_congr_ae (D I : Finset ℕ) (h α : ℝ)
    {E E' F F' : ℕ → Set ℝ}
    (hE : ∀ i, E i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] E' i)
    (hF : ∀ i, F i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] F' i)
    (θ : ℕ → ℝ) (n : ℕ) :
    testedProduct false D I h α E F θ n =ᵐ[baseMeasure]
      testedProduct false D I h α E' F' θ n := by
  have he : ∀ᵐ x ∂baseMeasure, ∀ i,
      (circleRepresentative (x i) ∈ E i) =
        (circleRepresentative (x i) ∈ E' i) :=
    ae_all_iff.mpr fun i =>
      (CocycleSupport.measurePreserving_productRepresentative i).quasiMeasurePreserving.ae (hE i)
  have hf : ∀ᵐ x ∂baseMeasure, ∀ i,
      (circleRepresentative (rotationIterate θ (n : ℤ) x i) ∈ F i) =
        (circleRepresentative (rotationIterate θ (n : ℤ) x i) ∈ F' i) :=
    ae_all_iff.mpr fun i =>
      ((CocycleSupport.measurePreserving_productRepresentative i).comp
        (measurePreserving_rotationIterate θ (n : ℤ))).quasiMeasurePreserving.ae (hF i)
  filter_upwards [he, hf] with x hx hy
  unfold testedProduct
  apply Finset.prod_congr rfl
  intro i hi
  rw [first_testedCoordinateWeight_eq, first_testedCoordinateWeight_eq, hx i, hy i]

theorem testedIdeal_first_congr_ae (D I : Finset ℕ) (h α : ℝ)
    {E E' F F' : ℕ → Set ℝ}
    (hE : ∀ i, E i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] E' i)
    (hF : ∀ i, F i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] F' i) :
    testedIdeal false D I h α E F =ᵐ[baseMeasure]
      testedIdeal false D I h α E' F' := by
  have he : ∀ᵐ x ∂baseMeasure, ∀ i,
      (circleRepresentative (x i) ∈ E i) =
        (circleRepresentative (x i) ∈ E' i) :=
    ae_all_iff.mpr fun i =>
      (CocycleSupport.measurePreserving_productRepresentative i).quasiMeasurePreserving.ae (hE i)
  filter_upwards [he] with x hx
  unfold testedIdeal
  apply Finset.prod_congr rfl
  intro i hi
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← restrict_Ico_eq_restrict_Ioc]
  apply integral_congr_ae
  have hf := (measurePreserving_fract_add_unit (circleRepresentative (x i))).quasiMeasurePreserving.ae (hF i)
  filter_upwards [hf] with t ht
  simp only [testedCoordinateWeight, Bool.false_eq_true, ↓reduceIte]
  rw [indicator_one_eq_of_mem_iff (iff_of_eq (hx i)),
    indicator_one_eq_of_mem_iff (iff_of_eq ht)]

theorem sourceTestedError_first_congr_ae (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (I : Finset ℕ) {E E' F F' : ℕ → Set ℝ}
    (hE : ∀ i, E i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] E' i)
    (hF : ∀ i, F i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] F' i)
    (n : ℕ) (θ : ℕ → ℝ) :
    sourceTestedError p N false I E F n θ =ᵐ[baseMeasure]
      sourceTestedError p N false I E' F' n θ := by
  have hp : ∀ᵐ x ∂baseMeasure, ∀ k,
      testedProduct false (Finset.range (p.prefixCount (n + 1))) I
        ((p.m n : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m n : ℝ) ^ 2) E F θ k x =
      testedProduct false (Finset.range (p.prefixCount (n + 1))) I
        ((p.m n : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m n : ℝ) ^ 2) E' F' θ k x :=
    ae_all_iff.mpr fun k => testedProduct_first_congr_ae _ _ _ _ hE hF θ k
  have hi := testedIdeal_first_congr_ae (Finset.range (p.prefixCount (n + 1))) I
    ((p.m n : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m n : ℝ) ^ 2) hE hF
  filter_upwards [hp, hi] with x hx hy
  simp only [sourceTestedError, hx, hy]

theorem integral_sq_sourceTestedError_first_congr (p : ProductScaleData)
    (N : ℕ → Finset ℕ) (I : Finset ℕ) {E E' F F' : ℕ → Set ℝ}
    (hE : ∀ i, E i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] E' i)
    (hF : ∀ i, F i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] F' i)
    (n : ℕ) (θ : ℕ → ℝ) :
    (∫ x, (sourceTestedError p N false I E F n θ x) ^ 2 ∂baseMeasure) =
      ∫ x, (sourceTestedError p N false I E' F' n θ x) ^ 2 ∂baseMeasure := by
  apply integral_congr_ae
  filter_upwards [sourceTestedError_first_congr_ae p N I hE hF n θ] with x hx
  rw [hx]

theorem cylinderCoordinateSet_ae_Ico
    (t : SamplingCylinderWeak.CylinderTest (Bool × ℕ)) (b : Bool) (i : ℕ) :
    ∃ a c : ℚ, cylinderCoordinateSet t b i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
      Ico (a : ℝ) (c : ℝ) := by
  rcases cylinderCoordinateSet_normal_form t b i with hu | ⟨a, c, hac⟩
  · refine ⟨0, 1, ?_⟩
    rw [hu, Rat.cast_zero, Rat.cast_one]
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with x hx
    change (x ∈ (univ : Set ℝ)) = (x ∈ Ico (0 : ℝ) 1)
    exact propext ⟨fun _ => hx, fun _ => mem_univ x⟩
  · refine ⟨a, c, ?_⟩
    rw [hac]
    exact Ioo_ae_eq_Ico

theorem exists_cylinderTest_first_error_rationalIco
    (t : SamplingCylinderWeak.CylinderTest (Bool × ℕ)) :
    ∃ a b c d : ℕ → ℚ,
      (∀ i, cylinderCoordinateSet t false i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
        Ico (a i : ℝ) (b i : ℝ)) ∧
      (∀ i, cylinderCoordinateSet t true i =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
        Ico (c i : ℝ) (d i : ℝ)) ∧
      ∀ (p : ProductScaleData) (N : ℕ → Finset ℕ) (I : Finset ℕ) (n : ℕ) (θ : ℕ → ℝ),
        sourceTestedError p N false I (cylinderCoordinateSet t false)
          (cylinderCoordinateSet t true) n θ =ᵐ[baseMeasure]
        sourceTestedError p N false I (fun i => Ico (a i : ℝ) (b i : ℝ))
          (fun i => Ico (c i : ℝ) (d i : ℝ)) n θ := by
  choose a b hab using fun i => cylinderCoordinateSet_ae_Ico t false i
  choose c d hcd using fun i => cylinderCoordinateSet_ae_Ico t true i
  exact ⟨a, b, c, d, hab, hcd, fun p N I n θ =>
    sourceTestedError_first_congr_ae p N I hab hcd n θ⟩

end Invariant233.ProductModel.SamplingWeights

end

end OAI
