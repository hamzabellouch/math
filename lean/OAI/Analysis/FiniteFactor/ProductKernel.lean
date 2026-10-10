import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset MeasurableSpace
open scoped ENNReal
noncomputable section

/-- Products of Markov kernels, with measurability proved on the generating
finite cylinders and extended to the entire product sigma algebra. -/
def independentKernel {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel (∀ i, X i) (∀ i, Y i) where
  toFun x := Measure.infinitePi (fun i => κ i (x i))
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_squareCylinders.symm
      (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
    rintro _ ⟨I, S, hS, rfl⟩
    have hs (i : ι) : MeasurableSet (S i) := hS i (Set.mem_univ i)
    simp_rw [Measure.infinitePi_pi _ (fun i _ => hs i)]
    exact Finset.measurable_prod _ fun i _ => ((κ i).measurable_coe (hs i)).comp (measurable_pi_apply i)

instance independentKernel_markov {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (independentKernel κ) := ⟨fun x => by
      change IsProbabilityMeasure (Measure.infinitePi (fun i => κ i (x i)))
      infer_instance⟩

theorem independentKernel_pi {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (x : ∀ i, X i) (I : Finset ι) (S : ∀ i, Set (Y i))
    (hS : ∀ i ∈ I, MeasurableSet (S i)) :
    independentKernel κ x (Set.pi (I : Set ι) S) = ∏ i ∈ I, κ i (x i) (S i) :=
  Measure.infinitePi_pi _ hS

theorem lintegral_infinitePi_finset_prod {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i ∈ I, f i (x i) ∂Measure.infinitePi μ) = ∏ i ∈ I, ∫⁻ t, f i t ∂μ i := by
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun I
    (fun (i : ι) (x : ∀ i, X i) => f i (x i)) (iIndepFun_infinitePi (P := μ) (X := f) hf)
    (fun i => (hf i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval_infinitePi μ i).lintegral_comp (hf i)

/-- Full-vector disintegration commutes with an arbitrary independent product.
The equality is of measures on all measurable sets, not just rectangles. -/
theorem independentKernel_compProd {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    ((Measure.infinitePi μ) ⊗ₘ (independentKernel κ)).map
      (fun z i => (z.1 i, z.2 i)) = Measure.infinitePi (fun i => (μ i) ⊗ₘ (κ i)) := by
  have hm : Measurable (fun z : (∀ i, X i) × (∀ i, Y i) => fun i => (z.1 i, z.2 i)) := by
    fun_prop
  apply Measure.eq_infinitePi
  intro I S hS
  rw [Measure.map_apply hm (MeasurableSet.pi I.countable_toSet (fun i _ => hS i)),
    Measure.compProd_apply (hm (MeasurableSet.pi I.countable_toSet (fun i _ => hS i)))]
  have he (x : ∀ i, X i) : Prod.mk x ⁻¹' ((fun (z : (∀ i, X i) × (∀ i, Y i)) i => (z.1 i, z.2 i)) ⁻¹' Set.pi (I : Set ι) S) =
      Set.pi (I : Set ι) (fun i => Prod.mk (x i) ⁻¹' S i) := rfl
  simp_rw [he, independentKernel_pi κ _ I _ (fun i _ => measurable_prodMk_left (hS i))]
  rw [lintegral_infinitePi_finset_prod μ I
    (fun i t => κ i t (Prod.mk t ⁻¹' S i)) (fun i => Kernel.measurable_kernel_prodMk_left (hS i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (Measure.compProd_apply (hS i)).symm

end
end FiniteFactor

end OAI
