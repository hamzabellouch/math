import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.MassVersionsCore

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Set Filter CompactlySupported
open scoped ENNReal NNReal Topology

namespace SLEExactGauge.MassVersions

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]

 

theorem isSFiniteKernel_of_pointwise_finite (κ : Kernel Ω X)
    [∀ ω, IsFiniteMeasure (κ ω)] : IsSFiniteKernel κ := by
  let r : Ω → ℝ≥0∞ := fun ω => κ ω univ + 1
  have hr : Measurable r := (κ.measurable_coe MeasurableSet.univ).add_const 1
  have hr0 (ω : Ω) : r ω ≠ 0 := by simp [r]
  have hrtop (ω : Ω) : r ω ≠ ∞ := by simp [r, measure_ne_top]
  let η : Kernel Ω X := ⟨fun ω => (r ω)⁻¹ • κ ω, by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.smul_apply, smul_eq_mul]
    exact hr.inv.mul (κ.measurable_coe hA)⟩
  have hη : IsFiniteKernel η := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun ω => ?_⟩⟩
    change (r ω)⁻¹ * κ ω univ ≤ 1
    calc
      _ ≤ (r ω)⁻¹ * r ω := mul_le_mul_of_nonneg_left (le_add_right le_rfl) zero_le
      _ = 1 := ENNReal.inv_mul_cancel (hr0 ω) (hrtop ω)
  have he : κ = η.withDensity (fun ω _ => r ω) := by
    apply Kernel.ext
    intro ω
    rw [Kernel.withDensity_apply η (f := fun ω (_ : X) => r ω)
      (hr.comp measurable_fst), withDensity_const]
    change κ ω = r ω • ((r ω)⁻¹ • κ ω)
    rw [smul_smul, ENNReal.mul_inv_cancel (hr0 ω) (hrtop ω), one_smul]
  rw [he]
  exact Kernel.IsSFiniteKernel.withDensity η (fun ω _ => hrtop ω)

variable [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [BorelSpace X]

 

theorem isSFiniteKernel_of_locally_finite (κ : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (κ ω)] : IsSFiniteKernel κ := by
  let K := CompactExhaustion.choice X
  let V := disjointed (fun n => K n)
  have hV (n : ℕ) : MeasurableSet (V n) :=
    MeasurableSet.disjointed (fun n => (K.isCompact n).measurableSet) n
  let η : ℕ → Kernel Ω X := fun n => κ.restrict (hV n)
  have hη (n : ℕ) : IsSFiniteKernel (η n) := by
    have (ω : Ω) : IsFiniteMeasure (η n ω) := by
      refine ⟨?_⟩
      rw [show η n ω = (κ ω).restrict (V n) from rfl, Measure.restrict_apply_univ]
      exact (measure_mono (disjointed_subset _ _)).trans_lt (K.isCompact n).measure_lt_top
    exact isSFiniteKernel_of_pointwise_finite (η n)
  have he : Kernel.sum η = κ := by
    apply Kernel.ext
    intro ω
    change Measure.sum (fun n => (κ ω).restrict (V n)) = κ ω
    rw [← Measure.restrict_iUnion (disjoint_disjointed _) (fun n => hV n)]
    simp only [iUnion_disjointed, K.iUnion_eq, Measure.restrict_univ]
  rw [← he]
  exact Kernel.isSFiniteKernel_sum

 

theorem average_finiteOnCompacts (κ : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (κ ω)] (W : Measure Ω)
    (hκ : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂κ ω) W) :
    IsFiniteMeasureOnCompacts (κ ∘ₘ W) := by
  constructor
  intro K hK
  obtain ⟨g,hg1,-,hgc,hg01⟩ := exists_continuous_one_zero_of_isCompact
    hK isClosed_empty (disjoint_empty K)
  let f : C_c(X,ℝ) := ⟨g,hgc⟩
  rw [Measure.bind_apply hK.measurableSet κ.aemeasurable]
  apply lt_of_le_of_lt _ (hκ f).lintegral_lt_top
  apply lintegral_mono
  intro ω
  exact f.integrable.measure_le_integral (Eventually.of_forall (fun x => (hg01 x).1))
    (fun x hx => le_of_eq ((hg1 hx).symm))

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma average_integrable_compact_test (κ : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (κ ω)] (W : Measure Ω)
    (hκ : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂κ ω) W)
    (f : C_c(X,ℝ)) : Integrable f (κ ∘ₘ W) := by
  let g : C_c(X,ℝ) := ⟨⟨fun x => ‖f x‖, f.continuous.norm⟩, f.hasCompactSupport.norm⟩
  apply (Measure.integrable_comp_iff f.continuous.measurable.aestronglyMeasurable).mpr
  exact ⟨Eventually.of_forall (fun _ => f.integrable), hκ g⟩

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma average_compact_eval (κ : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (κ ω)] (W : Measure Ω)
    (hκ : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂κ ω) W)
    (f : C_c(X,ℝ)) :
    (∫x, f x ∂(κ ∘ₘ W)) = ∫ω, (∫x, f x ∂κ ω) ∂W := by
  have hf := average_integrable_compact_test κ W hκ f
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  exact Kernel.integral_comp hf

variable [TopologicalSpace.PseudoMetrizableSpace X]

 

theorem average_eq_of_compact_tests (κ η : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (κ ω)] [∀ ω, IsFiniteMeasureOnCompacts (η ω)]
    (W : Measure Ω)
    (hκ : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂κ ω) W)
    (hη : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂η ω) W)
    (he : ∀ f : C_c(X,ℝ), (∫ω, (∫x, f x ∂κ ω) ∂W) = ∫ω, (∫x, f x ∂η ω) ∂W) :
    κ ∘ₘ W = η ∘ₘ W := by
  have := average_finiteOnCompacts κ W hκ
  have := average_finiteOnCompacts η W hη
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  simpa only [average_compact_eval _ _ hκ, average_compact_eval _ _ hη] using he f

omit mΩ [MeasurableSpace X] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
lemma prod_sigma_le {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    (n : MeasurableSpace X) : m.prod n ≤ m₀.prod n :=
  sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl

 

theorem conditional_product_eq_of_compact_tests (κ η : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (κ ω)] [∀ ω, IsFiniteMeasureOnCompacts (η ω)]
    (W : Measure Ω) [SFinite W]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hκ : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂κ ω) W)
    (hη : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂η ω) W)
    (he : ∀ U : Set Ω, MeasurableSet[m] U → ∀ f : C_c(X,ℝ),
      (∫ω in U, (∫x, f x ∂κ ω) ∂W) = ∫ω in U, (∫x, f x ∂η ω) ∂W) :
    (W ⊗ₘ κ).trim (prod_sigma_le hm _) = (W ⊗ₘ η).trim (prod_sigma_le hm _) := by
  let : MeasurableSpace Ω := mΩ
  have := isSFiniteKernel_of_locally_finite κ
  have := isSFiniteKernel_of_locally_finite η
  have havg (U : Set Ω) (hU : MeasurableSet[m] U) :
      κ ∘ₘ (W.restrict U) = η ∘ₘ (W.restrict U) :=
    average_eq_of_compact_tests κ η (W.restrict U)
      (fun f => (hκ f).restrict) (fun f => (hη f).restrict) (he U hU)
  have hrect (U : Set Ω) (hU : MeasurableSet[m] U) (A : Set X) (hA : MeasurableSet A) :
      (W ⊗ₘ κ).trim (prod_sigma_le hm _) (U ×ˢ A) =
        (W ⊗ₘ η).trim (prod_sigma_le hm _) (U ×ˢ A) := by
    rw [trim_measurableSet_eq _ (hU.prod hA), trim_measurableSet_eq _ (hU.prod hA),
      Measure.compProd_apply_prod (hm _ hU) hA, Measure.compProd_apply_prod (hm _ hU) hA,
      ← Measure.bind_apply hA κ.aemeasurable, ← Measure.bind_apply hA η.aemeasurable, havg U hU]
  let K := CompactExhaustion.choice X
  have := average_finiteOnCompacts κ W hκ
  have hfin (n : ℕ) : (W ⊗ₘ κ).trim (prod_sigma_le hm _) (univ ×ˢ K n) ≠ ∞ := by
    rw [trim_measurableSet_eq _ (MeasurableSet.univ.prod (K.isCompact n).measurableSet),
      Measure.compProd_apply_prod MeasurableSet.univ (K.isCompact n).measurableSet,
      setLIntegral_univ, ← Measure.bind_apply (K.isCompact n).measurableSet κ.aemeasurable]
    exact (K.isCompact n).measure_lt_top.ne
  let : MeasurableSpace Ω := m
  apply Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set Ω | MeasurableSet U} {A : Set X | MeasurableSet A})
    (fun n => univ ×ˢ K n) generateFrom_prod.symm isPiSystem_prod
  · ext p
    simp only [mem_iUnion, mem_prod, mem_univ, true_and, iff_true]
    exact K.exists_mem p.2
  · intro n
    exact ⟨univ, MeasurableSet.univ, K n, (K.isCompact n).measurableSet, rfl⟩
  · exact hfin
  · rintro _ ⟨U, hU, A, hA, rfl⟩
    exact hrect U hU A hA

 

theorem conditional_lintegral_eq_of_compact_tests (κ η : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (κ ω)] [∀ ω, IsFiniteMeasureOnCompacts (η ω)]
    (W : Measure Ω) [SFinite W]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (hκ : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂κ ω) W)
    (hη : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x, f x ∂η ω) W)
    (he : ∀ U : Set Ω, MeasurableSet[m] U → ∀ f : C_c(X,ℝ),
      (∫ω in U, (∫x, f x ∂κ ω) ∂W) = ∫ω in U, (∫x, f x ∂η ω) ∂W)
    (H : Ω × X → ℝ≥0∞) (hH : Measurable[m.prod ‹MeasurableSpace X›] H) :
    (∫⁻ω, ∫⁻x, H (ω,x) ∂κ ω ∂W) = ∫⁻ω, ∫⁻x, H (ω,x) ∂η ω ∂W := by
  let : MeasurableSpace Ω := mΩ
  have := isSFiniteKernel_of_locally_finite κ
  have := isSFiniteKernel_of_locally_finite η
  have hH₀ : Measurable H := hH.mono (prod_sigma_le hm _) le_rfl
  rw [← Measure.lintegral_compProd hH₀, ← Measure.lintegral_compProd hH₀,
    ← lintegral_trim (prod_sigma_le hm _) hH,
    ← lintegral_trim (μ := W ⊗ₘ η) (prod_sigma_le hm _) hH,
    conditional_product_eq_of_compact_tests κ η W m hm hκ hη he]

end SLEExactGauge.MassVersions

namespace SLEExactGauge.MassVersions

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [BorelSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X]

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [BorelSpace X] [TopologicalSpace.PseudoMetrizableSpace X] in
lemma average_mono (κ : Kernel Ω X) {W V : Measure Ω} (h : V ≤ W) : κ ∘ₘ V ≤ κ ∘ₘ W := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA κ.aemeasurable, Measure.bind_apply hA κ.aemeasurable]
  exact lintegral_mono' h le_rfl

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
lemma average_restrict_finite (κ : Kernel Ω X) (W : Measure Ω)
    [IsFiniteMeasureOnCompacts (κ ∘ₘ W)] (U : Set Ω) :
    IsFiniteMeasureOnCompacts (κ ∘ₘ W.restrict U) := by
  constructor
  intro K hK
  exact ((average_mono κ Measure.restrict_le_self) K).trans_lt hK.measure_lt_top

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace.PseudoMetrizableSpace X] in
lemma average_compact_eval_of_average_finite (κ : Kernel Ω X) (W : Measure Ω)
    [IsFiniteMeasureOnCompacts (κ ∘ₘ W)] (f : C_c(X, ℝ)) :
    (∫x, f x ∂(κ ∘ₘ W)) = ∫ω, (∫x, f x ∂κ ω) ∂W := by
  have hf : Integrable f (κ ∘ₘ W) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  exact Kernel.integral_comp hf

 

theorem conditional_product_eq_of_average_finite (κ η : Kernel Ω X)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (W : Measure Ω) [SFinite W]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    [IsFiniteMeasureOnCompacts (κ ∘ₘ W)] [IsFiniteMeasureOnCompacts (η ∘ₘ W)]
    (he : ∀ U : Set Ω, MeasurableSet[m] U → ∀ f : C_c(X,ℝ),
      (∫ω in U, (∫x, f x ∂κ ω) ∂W) = ∫ω in U, (∫x, f x ∂η ω) ∂W) :
    (W ⊗ₘ κ).trim (prod_sigma_le hm _) = (W ⊗ₘ η).trim (prod_sigma_le hm _) := by
  let : MeasurableSpace Ω := mΩ
  have havg (U : Set Ω) (hU : MeasurableSet[m] U) :
      κ ∘ₘ (W.restrict U) = η ∘ₘ (W.restrict U) := by
    have := average_restrict_finite κ W U
    have := average_restrict_finite η W U
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    simpa only [average_compact_eval_of_average_finite] using he U hU f
  have hrect (U : Set Ω) (hU : MeasurableSet[m] U) (A : Set X) (hA : MeasurableSet A) :
      (W ⊗ₘ κ).trim (prod_sigma_le hm _) (U ×ˢ A) =
        (W ⊗ₘ η).trim (prod_sigma_le hm _) (U ×ˢ A) := by
    rw [trim_measurableSet_eq _ (hU.prod hA), trim_measurableSet_eq _ (hU.prod hA),
      Measure.compProd_apply_prod (hm _ hU) hA, Measure.compProd_apply_prod (hm _ hU) hA,
      ← Measure.bind_apply hA κ.aemeasurable, ← Measure.bind_apply hA η.aemeasurable, havg U hU]
  let K := CompactExhaustion.choice X
  have hfin (n : ℕ) : (W ⊗ₘ κ).trim (prod_sigma_le hm _) (univ ×ˢ K n) ≠ ∞ := by
    rw [trim_measurableSet_eq _ (MeasurableSet.univ.prod (K.isCompact n).measurableSet),
      Measure.compProd_apply_prod MeasurableSet.univ (K.isCompact n).measurableSet,
      setLIntegral_univ, ← Measure.bind_apply (K.isCompact n).measurableSet κ.aemeasurable]
    exact (K.isCompact n).measure_lt_top.ne
  let : MeasurableSpace Ω := m
  apply Measure.ext_of_generateFrom_of_iUnion
    (image2 (· ×ˢ ·) {U : Set Ω | MeasurableSet U} {A : Set X | MeasurableSet A})
    (fun n => univ ×ˢ K n) generateFrom_prod.symm isPiSystem_prod
  · ext p
    simp only [mem_iUnion, mem_prod, mem_univ, true_and, iff_true]
    exact K.exists_mem p.2
  · intro n
    exact ⟨univ, MeasurableSet.univ, K n, (K.isCompact n).measurableSet, rfl⟩
  · exact hfin
  · rintro _ ⟨U, hU, A, hA, rfl⟩
    exact hrect U hU A hA

theorem conditional_lintegral_eq_of_average_finite (κ η : Kernel Ω X)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (W : Measure Ω) [SFinite W]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    [IsFiniteMeasureOnCompacts (κ ∘ₘ W)] [IsFiniteMeasureOnCompacts (η ∘ₘ W)]
    (he : ∀ U : Set Ω, MeasurableSet[m] U → ∀ f : C_c(X,ℝ),
      (∫ω in U, (∫x, f x ∂κ ω) ∂W) = ∫ω in U, (∫x, f x ∂η ω) ∂W)
    (H : Ω × X → ℝ≥0∞) (hH : Measurable[m.prod ‹MeasurableSpace X›] H) :
    (∫⁻ω, ∫⁻x, H (ω,x) ∂κ ω ∂W) = ∫⁻ω, ∫⁻x, H (ω,x) ∂η ω ∂W := by
  let : MeasurableSpace Ω := mΩ
  have hH₀ : Measurable H := hH.mono (prod_sigma_le hm _) le_rfl
  rw [← Measure.lintegral_compProd hH₀, ← Measure.lintegral_compProd hH₀,
    ← lintegral_trim (prod_sigma_le hm _) hH,
    ← lintegral_trim (μ := W ⊗ₘ η) (prod_sigma_le hm _) hH,
    conditional_product_eq_of_average_finite κ η W m hm he]

end SLEExactGauge.MassVersions

namespace SLEExactGauge.MassVersions
open MeasureTheory ProbabilityTheory Set CompactlySupported
variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [BorelSpace X]

omit [BorelSpace X] in
lemma finiteOnCompacts_of_integrable_tests (ν : Measure X)
    (hν : ∀ f : C_c(X,ℝ), Integrable f ν) : IsFiniteMeasureOnCompacts ν := by
  constructor
  intro K hK
  obtain ⟨g,hg1,-,hgc,hg01⟩ := exists_continuous_one_zero_of_isCompact
    hK isClosed_empty (disjoint_empty K)
  let f : C_c(X,ℝ) := ⟨g,hgc⟩
  exact ((hν f).measure_le_integral (Eventually.of_forall (fun x => (hg01 x).1))
    (fun x hx => le_of_eq ((hg1 hx).symm))).trans_lt ENNReal.ofReal_lt_top

omit [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X] in
lemma average_add (κ η : Kernel Ω X) (W : Measure Ω) :
    (κ + η) ∘ₘ W = κ ∘ₘ W + η ∘ₘ W := by
  rw [Measure.comp_eq_comp_const_apply, Kernel.comp_add_left,
    add_apply, ← Measure.comp_eq_comp_const_apply, ← Measure.comp_eq_comp_const_apply]

end SLEExactGauge.MassVersions
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

instance upperArea_finiteOnCompacts : IsFiniteMeasureOnCompacts upperArea := by
  constructor
  intro K hK
  rw [upperArea, upper_embedding.comap_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top

lemma survivingGreen_joint_measurable (a : ℝ) (ha : 1/4<a) (t : ℝ≥0) :
    Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane => survivingGreen a t p.1 p.2.1) :=
  (actual_surviving_green a ha t).1.mono (prod_sigma_le (rawFiltration.le t) _) le_rfl

lemma survivingGreen_spatial_measurable (a : ℝ) (ha : 1/4<a) (t : ℝ≥0)
    (b : ExactSLEGenerator.Driver) : Measurable (fun z : UpperPlane => survivingGreen a t b z.1) :=
  (survivingGreen_joint_measurable a ha t).comp (measurable_const.prodMk measurable_id)

 
noncomputable def survivingKernel (a : ℝ) (_ha : 1/4<a) (t : ℝ≥0) :
    Kernel ExactSLEGenerator.Driver UpperPlane :=
  (Kernel.const ExactSLEGenerator.Driver upperArea).withDensity
    (fun b z => ENNReal.ofReal (survivingGreen a t b z.1))

instance survivingKernel_sfinite (a : ℝ) (ha : 1/4<a) (t : ℝ≥0) :
    IsSFiniteKernel (survivingKernel a ha t) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

lemma survivingKernel_apply (a : ℝ) (ha : 1/4<a) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    survivingKernel a ha t b = upperArea.withDensity (fun z => ENNReal.ofReal (survivingGreen a t b z.1)) :=
  Kernel.withDensity_apply _ (survivingGreen_joint_measurable a ha t).ennreal_ofReal b

lemma survivingKernel_compact_eval (a : ℝ) (ha : 1/4<a) (t : ℝ≥0)
    (b : ExactSLEGenerator.Driver) (f : C_c(UpperPlane,ℝ)) :
    (∫z, f z ∂survivingKernel a ha t b) = ∫z, f z * survivingGreen a t b z.1 ∂upperArea := by
  rw [survivingKernel_apply, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (survivingGreen_nonneg _ _ _ _), smul_eq_mul, mul_comm]
  · exact (survivingGreen_spatial_measurable a ha t b).ennreal_ofReal
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

lemma surviving_compact_spatial_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (f : C_c(UpperPlane,ℝ)) :
    Integrable (fun p : UpperPlane × ExactSLEGenerator.Driver => f p.1*survivingGreen a t p.2 p.1.1)
      ((upperArea.restrict (tsupport f)).prod W) := by
  obtain ⟨c,hc,hcK⟩ := upper_compact_lower (tsupport f) f.hasCompactSupport
  obtain ⟨B,hB,hBf⟩ := upperExtension_bounded f
  exact (actual_remaining_spatial_L1 a ha W hW t (tsupport f) f.hasCompactSupport.measurableSet
    f.hasCompactSupport.measure_lt_top (c/2) (by positivity)
    (fun z hz => by have := hcK z hz; linarith) f f.continuous.measurable B hB
    (fun z hz => by simpa only [upperExtension_apply] using hBf z.1 ⟨z,hz,rfl⟩)
    (fun n : ℕ => 1/((n:ℝ)+1))
    (fun n => ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])⟩)
    tendsto_one_div_add_atTop_nhds_zero_nat).1

lemma survivingKernel_compact_mean_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (f : C_c(UpperPlane,ℝ)) :
    Integrable (fun b => ∫z, f z ∂survivingKernel a ha t b) W := by
  simp_rw [survivingKernel_compact_eval]
  convert (surviving_compact_spatial_integrable a ha W hW t f).integral_prod_right using 1
  funext b
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul])).symm

lemma survivingKernel_compact_ae_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (f : C_c(UpperPlane,ℝ)) :
    ∀ᵐ b ∂W, Integrable f (survivingKernel a ha t b) := by
  filter_upwards [(surviving_compact_spatial_integrable a ha W hW t f).prod_left_ae] with b hb
  rw [survivingKernel_apply, integrable_withDensity_iff_integrable_smul'
    (survivingGreen_spatial_measurable a ha t b).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (survivingGreen_nonneg _ _ _ _), smul_eq_mul]
  have hs : Function.support (fun z : UpperPlane => f z * survivingGreen a t b z.1) ⊆ tsupport f :=
    (Function.support_mul_subset_left _ _).trans (subset_tsupport f)
  simpa only [mul_comm] using (integrableOn_iff_integrable_of_support_subset hs).mp hb

lemma survivingKernel_average_compact_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (f : C_c(UpperPlane,ℝ)) :
    Integrable f (survivingKernel a ha t ∘ₘ W) := by
  let g : C_c(UpperPlane,ℝ) := ⟨⟨fun z => ‖f z‖,f.continuous.norm⟩,f.hasCompactSupport.norm⟩
  apply (Measure.integrable_comp_iff f.continuous.measurable.aestronglyMeasurable).mpr
  exact ⟨survivingKernel_compact_ae_integrable a ha W hW t f,
    survivingKernel_compact_mean_integrable a ha W hW t g⟩

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma survivingKernel_average_finiteOnCompacts (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) : IsFiniteMeasureOnCompacts (survivingKernel a ha t ∘ₘ W) :=
  finiteOnCompacts_of_integrable_tests _ (survivingKernel_average_compact_integrable a ha W hW t)

 

theorem compact_conditional_to_random_tests (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (μ ν : Kernel ExactSLEGenerator.Driver UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (μ b)] [∀ b, IsFiniteMeasureOnCompacts (ν b)]
    (hμ : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z, f z ∂μ b) W)
    (hν : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z, f z ∂ν b) W)
    (he : ∀ f : C_c(UpperPlane,ℝ), ∀ U : Set ExactSLEGenerator.Driver,
      MeasurableSet[rawFiltration t] U →
      (∫b in U, (∫z, f z ∂ν b) - (∫z, f z ∂μ b) ∂W) =
        ∫b in U, (∫z, f z*survivingGreen a t b z.1 ∂upperArea) ∂W)
    (H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞)
    (hH : Measurable[(rawFiltration t).prod (inferInstance : MeasurableSpace UpperPlane)] H) :
    (∫⁻b, ∫⁻z, H (b,z) ∂ν b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ b ∂W) +
      ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a t b z.1) ∂upperArea ∂W := by
  have := isSFiniteKernel_of_locally_finite μ
  have := isSFiniteKernel_of_locally_finite ν
  have := average_finiteOnCompacts μ W hμ
  have := average_finiteOnCompacts ν W hν
  have := survivingKernel_average_finiteOnCompacts a ha W hW t
  have : IsFiniteMeasureOnCompacts ((μ + survivingKernel a ha t) ∘ₘ W) := by
    rw [SLEExactGauge.MassVersions.average_add]
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩
  have hidentity := conditional_lintegral_eq_of_average_finite ν (μ + survivingKernel a ha t) W
    (rawFiltration t) (rawFiltration.le t) ?_ H hH
  · rw [hidentity]
    have hH₀ : Measurable H := hH.mono (prod_sigma_le (rawFiltration.le t) _) le_rfl
    have heval (b : ExactSLEGenerator.Driver) :
        (∫⁻z, H (b,z) ∂(μ+survivingKernel a ha t) b) =
          (∫⁻z, H (b,z) ∂μ b) + ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a t b z.1) ∂upperArea := by
      have hHb : Measurable (fun z : UpperPlane => H (b,z)) :=
        hH₀.comp ((measurable_const (a := b)).prodMk measurable_id)
      rw [add_apply, lintegral_add_measure, survivingKernel_apply]
      congr 1
      exact (lintegral_withDensity_eq_lintegral_mul upperArea
        (survivingGreen_spatial_measurable a ha t b).ennreal_ofReal hHb).trans
          (lintegral_congr (fun _ => mul_comm _ _))
    simp_rw [heval]
    rw [lintegral_add_left]
    exact hH₀.lintegral_kernel_prod_right'
  · intro U hU f
    have hadd : (fun b => ∫z, f z ∂(μ+survivingKernel a ha t) b) =ᵐ[W]
        (fun b => (∫z, f z ∂μ b)+(∫z, f z ∂survivingKernel a ha t b)) := by
      filter_upwards [survivingKernel_compact_ae_integrable a ha W hW t f] with b hb
      exact integral_add_measure f.integrable hb
    rw [integral_congr_ae (ae_restrict_of_ae hadd),
      integral_add (hμ f).restrict (survivingKernel_compact_mean_integrable a ha W hW t f).restrict]
    have hf := he f U hU
    rw [integral_sub (hν f).restrict (hμ f).restrict] at hf
    simp_rw [survivingKernel_compact_eval]
    linarith

end ExactSLEGreen
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem actual_raw_mass_extraction (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass a ha s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ (t i) b) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → ∀ f : C_c(UpperPlane,ℝ),
        (∫b, (∫z,f z∂μ (t i) b) ∂W) = ∫z : UpperPlane,
          f z * (Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ → ∀ f : C_c(UpperPlane,ℝ),
        ∀ U : Set ExactSLEGenerator.Driver, MeasurableSet[rawFiltration v] U →
        (∫b in U, (∫z,f z∂μ (t j) b)-(∫z,f z∂μ (t i) b) ∂W) =
          ∫b in U, (∫z : UpperPlane,f z*survivingGreen a v b z.1 ∂upperArea) ∂W) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂W) = (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂W) +
          ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen a v b z.1) ∂upperArea ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i≤t j → μ (t i) b≤μ (t j) b) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k, c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫z,f z∂μ (t i) b))) := by
  obtain ⟨s,c,ν,hs,hc,hsum,hν,hmom,hL1,hmean,-,hcond,h⟩ :=
    actual_radon_compact_conditional a ha W hW t
  let μ := recoveredMass a ha s c hc
  have hμ (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
      IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular :=
    ⟨radonLimit_finite _, radonLimit_regular _⟩
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) := (hμ v b).1
  have hmeas (v : ℝ≥0∞) : Measurable (μ v) := recoveredMass_measurable a ha s c hc v
  have he : ∀ᵐ b ∂W, ∀ i, μ (t i) b = ν b i := by
    filter_upwards [h] with b hb
    intro i
    have := (hν b i).2
    apply radonLimit_eq
    intro f
    simpa only [actualMassFunctionals_apply] using hb.2 i f
  have heI (i : ℕ) (f : C_c(UpperPlane,ℝ)) :
      (fun b => ∫z,f z∂μ (t i) b) =ᵐ[W] (fun b => ∫z,f z∂ν b i) := by
    filter_upwards [he] with b hb
    rw [hb i]
  have hmoment (i : ℕ) (f : C_c(UpperPlane,ℝ)) (m : ℕ) :
      MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) W :=
    (memLp_congr_ae (heI i f)).mpr (hmom i f m)
  have hcompact (i j : ℕ) (v : ℝ≥0) (hi : t i=v) (hj : t j=∞)
      (f : C_c(UpperPlane,ℝ)) (U : Set ExactSLEGenerator.Driver)
      (hU : MeasurableSet[rawFiltration v] U) :
      (∫b in U, (∫z,f z∂μ (t j) b)-(∫z,f z∂μ (t i) b) ∂W) =
        ∫b in U, (∫z : UpperPlane,f z*survivingGreen a v b z.1 ∂upperArea) ∂W :=
    (integral_congr_ae (ae_restrict_of_ae ((heI j f).sub (heI i f)))).trans
      (hcond i j v hi hj f U hU)
  refine ⟨s,c,hc,hs,hsum,hμ,hmeas,recoveredMass_progressive a ha s c hc,hmoment,?_,?_,hcompact,?_,?_⟩
  · intro i f
    have hnorm (k : ℕ) :
        eLpNorm (fun b => (∑ j∈s k, c k j *
          ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b) - ∫z,f z∂μ (t i) b) 1 W =
        eLpNorm (fun b => (∑ j∈s k, c k j *
          ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b) - ∫z,f z∂ν b i) 1 W :=
      eLpNorm_congr_ae (EventuallyEq.sub (Filter.EventuallyEq.refl _ _) (heI i f))
    dsimp only [μ] at hnorm
    simpa only [hnorm] using hL1 i f
  · intro i hi f
    exact (integral_congr_ae (heI i f)).trans (hmean i hi f)
  · intro i j v hi hj H hH
    let K : ℝ≥0∞ → Kernel ExactSLEGenerator.Driver UpperPlane := fun r => ⟨μ r,hmeas r⟩
    exact compact_conditional_to_random_tests a ha W hW v (K (t i)) (K (t j))
      (fun f => by
        change Integrable (fun b => ∫z,f z∂μ (t i) b) W
        exact memLp_one_iff_integrable.mp (by simpa only [Nat.cast_one] using hmoment i f 1))
      (fun f => by
        change Integrable (fun b => ∫z,f z∂μ (t j) b) W
        exact memLp_one_iff_integrable.mp (by simpa only [Nat.cast_one] using hmoment j f 1))
      (hcompact i j v hi hj) H hH
  · filter_upwards [he,h] with b hb hb'
    dsimp only [μ] at hb
    simpa only [hb] using hb'

end ExactSLEGreen
end

end OAI
