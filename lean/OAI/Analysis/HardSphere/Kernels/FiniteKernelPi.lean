import Mathlib

namespace OAI

section

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HardSphere.Comparison

private theorem exists_kernel_pi_fin {α : Type*} [MeasurableSpace α] (n : ℕ)
    (β : Fin n → Type*) [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] :
    ∃ η : Kernel α (∀ i, β i), IsFiniteKernel η ∧
      ∀ a, η a = Measure.pi (fun i ↦ κ i a) := by
  induction n with
  | zero =>
    let η : Kernel α (∀ i, β i) := Kernel.deterministic (fun _ i ↦ Fin.elim0 i) measurable_const
    refine ⟨η, inferInstance, fun a ↦ ?_⟩
    rw [Kernel.deterministic_apply, Measure.pi_of_empty (fun i ↦ κ i a) (fun i ↦ Fin.elim0 i)]
  | succ n ih =>
    obtain ⟨η, hη, heq⟩ := ih (fun i ↦ β ((0 : Fin (n+1)).succAbove i))
      (fun i ↦ κ ((0 : Fin (n+1)).succAbove i))
    let := hη
    let e := (MeasurableEquiv.piFinSuccAbove β 0).symm
    refine ⟨((κ 0).prod η).map e, inferInstance, fun a ↦ ?_⟩
    rw [Kernel.map_apply _ e.measurable, Kernel.prod_apply, heq]
    exact ((measurePreserving_piFinSuccAbove (fun i ↦ κ i a) 0).symm
      (MeasurableEquiv.piFinSuccAbove β 0)).map_eq

theorem exists_kernel_pi {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (β : ι → Type*) [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] :
    ∃ η : Kernel α (∀ i, β i), IsFiniteKernel η ∧
      ∀ a, η a = Measure.pi (fun i ↦ κ i a) := by
  classical
  let e := (Fintype.equivFin ι).symm
  obtain ⟨η, hη, heq⟩ := exists_kernel_pi_fin (Fintype.card ι)
    (fun i ↦ β (e i)) (fun i ↦ κ (e i))
  let := hη
  let E := MeasurableEquiv.piCongrLeft β e
  refine ⟨η.map E, inferInstance, fun a ↦ ?_⟩
  rw [Kernel.map_apply _ E.measurable, heq]
  exact (measurePreserving_piCongrLeft (fun i ↦ κ i a) e).map_eq

noncomputable def finiteKernelPi {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] : Kernel α (∀ i, β i) :=
  (exists_kernel_pi β κ).choose

instance {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] :
    IsFiniteKernel (finiteKernelPi κ) := (exists_kernel_pi β κ).choose_spec.1

lemma finiteKernelPi_apply {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] (a : α) :
    finiteKernelPi κ a = Measure.pi (fun i ↦ κ i a) :=
  (exists_kernel_pi β κ).choose_spec.2 a

private lemma lintegral_fin_prod {n : ℕ} {β : Fin n → Type*}
    [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, β i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  induction n with
  | zero => simp [Measure.pi_of_empty μ]
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove μ 0).symm
      (MeasurableEquiv.piFinSuccAbove β 0)
    rw [← hp.lintegral_comp (f := fun x ↦ ∏ i, f i (x i)) (Finset.measurable_prod _ fun i _ ↦
      (hf i).comp (measurable_pi_apply i))]
    have heq : (fun z ↦ ∏ i, f i ((MeasurableEquiv.piFinSuccAbove β 0).symm z i)) =
        (fun z ↦ f 0 z.1 * ∏ j, f ((0 : Fin (n+1)).succAbove j) (z.2 j)) := by
      funext z
      rw [Fin.prod_univ_succAbove _ 0]
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [heq]
    have hm : Measurable (fun z : ∀ j : Fin n, β ((0 : Fin (n+1)).succAbove j) ↦
        ∏ j, f ((0 : Fin (n+1)).succAbove j) (z j)) :=
      Finset.measurable_prod _ fun i _ ↦
        (hf ((0 : Fin (n+1)).succAbove i)).comp (measurable_pi_apply i)
    rw [lintegral_prod_mul (hf 0).aemeasurable hm.aemeasurable]
    rw [ih _ _ (fun i ↦ hf ((0 : Fin (n+1)).succAbove i))]
    exact (Fin.prod_univ_succAbove (fun i ↦ ∫⁻ x, f i x ∂μ i) 0).symm

lemma lintegral_finite_prod {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, β i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp (f := fun x ↦ ∏ i, f i (x i))
    (Finset.measurable_prod _ fun i _ ↦ (hf i).comp (measurable_pi_apply i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ _ (fun i ↦ hf (e i))

section CoordinateKernels
variable {ι : Type*} [Fintype ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

def coordinateKernel : Kernel (∀ i, X i) (∀ i, Z i) :=
  finiteKernelPi (fun i ↦ (κ i).comap (fun x ↦ x i) (measurable_pi_apply (i : ι)))

instance : IsFiniteKernel (coordinateKernel κ) := by
  unfold coordinateKernel
  infer_instance

lemma coordinateKernel_apply (x : ∀ i, X i) :
    coordinateKernel κ x = Measure.pi (fun i ↦ κ i (x i)) := by
  simp only [coordinateKernel, finiteKernelPi_apply, Kernel.comap_apply]

lemma pi_compProd (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)] :
    Measure.map (fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i))
      ((Measure.pi μ).compProd (coordinateKernel κ)) =
    Measure.pi (fun i ↦ (μ i).compProd (κ i)) := by
  classical
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i)) := by
    fun_prop
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),
    Measure.compProd_apply (hm (MeasurableSet.univ_pi hs))]
  have heq (x : ∀ i, X i) : (Prod.mk x ⁻¹'
      ((fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i)) ⁻¹' Set.pi Set.univ s)) =
      Set.pi Set.univ (fun i ↦ Prod.mk (x i) ⁻¹' s i) := by
    ext z
    simp
  simp_rw [heq, coordinateKernel_apply, Measure.pi_pi]
  rw [lintegral_finite_prod _ _ (fun i ↦ Kernel.measurable_kernel_prodMk_left (hs i))]
  congr 1
  funext i
  exact (Measure.compProd_apply (hs i)).symm

lemma measurable_kernelPi_integral {f : (∀ i, X i) × (∀ i, Z i) → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (fun x ↦ ∫⁻ z, f (x,z) ∂Measure.pi (fun i ↦ κ i (x i))) := by
  simpa only [coordinateKernel_apply] using
    (hf.lintegral_kernel_prod_right' (κ := coordinateKernel κ))

lemma lintegral_pi_compProd (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    {f : (∀ i, X i × Z i) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂Measure.pi (fun i ↦ (μ i).compProd (κ i))) =
    ∫⁻ x, ∫⁻ z, f (fun i ↦ (x i,z i)) ∂Measure.pi (fun i ↦ κ i (x i)) ∂Measure.pi μ := by
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i)) := by
    fun_prop
  rw [← pi_compProd κ μ, lintegral_map hf hm]
  rw [Measure.lintegral_compProd (f := fun p : (∀ i, X i) × (∀ i, Z i) ↦ f (fun i ↦ (p.1 i, p.2 i)))
    (hf.comp hm)]
  simp only [coordinateKernel_apply]

end CoordinateKernels
end HardSphere.Comparison

noncomputable section
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators

end
end
end
end

end OAI
