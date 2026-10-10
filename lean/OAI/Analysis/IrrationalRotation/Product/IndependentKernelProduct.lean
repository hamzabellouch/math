import OAI.Analysis.IrrationalRotation.Model.IndependentKernelProduct
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Conditional

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Invariant233.KernelProduct

variable {ι : Type*} {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

instance independent_isMarkov (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (independent κ) :=
  ⟨fun _ => inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))⟩

@[simp] theorem independent_apply (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)] (x : ∀ i, A i) :
    independent κ x = Measure.infinitePi (fun i => κ i (x i)) := rfl

theorem compProd_map_pairCoordinates (μ : ∀ i, Measure (A i))
    [∀ i, IsProbabilityMeasure (μ i)] (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)] :
    ((Measure.infinitePi μ) ⊗ₘ independent κ).map pairCoordinates =
      Measure.infinitePi (fun i => μ i ⊗ₘ κ i) := by
  apply Measure.eq_infinitePi
  intro s t ht
  have hpair : Measurable (pairCoordinates (A := A) (B := B)) :=
    pairCoordinates.measurable
  have hset : MeasurableSet (Set.pi (s : Set ι) t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply hpair hset, Measure.compProd_apply (hpair hset)]
  have hsection (x : ∀ i, A i) :
      Prod.mk x ⁻¹' (pairCoordinates ⁻¹' Set.pi (s : Set ι) t) =
        Set.pi (s : Set ι) (fun i => Prod.mk (x i) ⁻¹' t i) := by
    ext y
    rfl
  simp_rw [hsection, independent_apply,
    Measure.infinitePi_pi _ (fun i _ => measurable_prodMk_left (ht i))]
  have hg (i : ι) : Measurable (fun a : A i => κ i a (Prod.mk a ⁻¹' t i)) :=
    Kernel.measurable_kernel_prodMk_left (ht i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun (μ := Measure.infinitePi μ) s
    (fun i (x : ∀ i, A i) => κ i (x i) (Prod.mk (x i) ⁻¹' t i))
    (iIndepFun_infinitePi hg) (fun i => (hg i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.compProd_apply (ht i)]
  exact (measurePreserving_eval_infinitePi μ i).lintegral_comp (hg i)

theorem independent_coordinates (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)] (x : ∀ i, A i) :
    iIndepFun (fun i (y : ∀ i, B i) => y i) (independent κ x) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

end Invariant233.KernelProduct

namespace Invariant233.KernelProduct
variable {ι : Type*} {X A : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (A i)]

theorem coordinate_disintegration (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (obs : ∀ i, X i → A i)
    (hobs : ∀ i, Measurable (obs i)) (κ : ∀ i, Kernel (A i) (X i))
    [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, (μ i).map (obs i) ⊗ₘ κ i =
      (μ i).map (fun z => (obs i z, z))) :
    ((Measure.infinitePi μ).map (fun z i => obs i (z i))) ⊗ₘ independent κ =
      (Measure.infinitePi μ).map (fun z => (fun i => obs i (z i), z)) := by
  let (index : ι) : IsProbabilityMeasure ((μ index).map (obs index)) := inferInstance
  apply (pairCoordinates (A := A) (B := X)).map_measurableEquiv_injective
  rw [Measure.infinitePi_map_pi μ hobs, compProd_map_pairCoordinates]
  rw [Measure.map_map pairCoordinates.measurable (by fun_prop)]
  change Measure.infinitePi (fun i => (μ i).map (obs i) ⊗ₘ κ i) =
    (Measure.infinitePi μ).map (fun z i => (obs i (z i), z i))
  rw [Measure.infinitePi_map_pi μ (f := fun i z => (obs i z, z))
    (fun i => (hobs i).prodMk measurable_id)]
  congr 1
  funext i
  exact hκ i

variable [Countable ι] [∀ i, StandardBorelSpace (X i)] [∀ i, Nonempty (X i)]

theorem condDistrib_coordinates (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (obs : ∀ i, X i → A i)
    (hobs : ∀ i, Measurable (obs i)) :
    condDistrib id (fun z i => obs i (z i)) (Measure.infinitePi μ)
      =ᵐ[(Measure.infinitePi μ).map (fun z i => obs i (z i))]
        independent (fun i => condDistrib id (obs i) (μ i)) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (by fun_prop) measurable_id
  exact (coordinate_disintegration μ obs hobs
    (fun i => condDistrib id (obs i) (μ i))
    (fun index => compProd_map_condDistrib (hobs index).aemeasurable
      measurable_id.aemeasurable)).symm

end Invariant233.KernelProduct

namespace Invariant233.KernelProduct
variable {ι : Type*} {X A B : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (A i)]
  [∀ i, MeasurableSpace (B i)]

theorem coordinate_pair_disintegration (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (obs : ∀ i, X i → A i)
    (val : ∀ i, X i → B i) (hobs : ∀ i, Measurable (obs i))
    (hval : ∀ i, Measurable (val i)) (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, (μ i).map (obs i) ⊗ₘ κ i =
      (μ i).map (fun z => (obs i z, val i z))) :
    ((Measure.infinitePi μ).map (fun z i => obs i (z i))) ⊗ₘ independent κ =
      (Measure.infinitePi μ).map
        (fun z => (fun i => obs i (z i), fun i => val i (z i))) := by
  let (index : ι) : IsProbabilityMeasure ((μ index).map (obs index)) := inferInstance
  apply (pairCoordinates (A := A) (B := B)).map_measurableEquiv_injective
  rw [Measure.infinitePi_map_pi μ hobs, compProd_map_pairCoordinates]
  rw [Measure.map_map pairCoordinates.measurable (by fun_prop)]
  change Measure.infinitePi (fun i => (μ i).map (obs i) ⊗ₘ κ i) =
    (Measure.infinitePi μ).map (fun z i => (obs i (z i), val i (z i)))
  rw [Measure.infinitePi_map_pi μ (f := fun i z => (obs i z, val i z))
    (fun i => (hobs i).prodMk (hval i))]
  congr 1
  funext i
  exact hκ i

variable [Countable ι] [∀ i, StandardBorelSpace (B i)] [∀ i, Nonempty (B i)]

theorem condDistrib_of_coordinate_disintegration (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (obs : ∀ i, X i → A i)
    (val : ∀ i, X i → B i) (hobs : ∀ i, Measurable (obs i))
    (hval : ∀ i, Measurable (val i)) (κ : ∀ i, Kernel (A i) (B i))
    [∀ i, IsMarkovKernel (κ i)]
    (hκ : ∀ i, (μ i).map (obs i) ⊗ₘ κ i =
      (μ i).map (fun z => (obs i z, val i z))) :
    condDistrib (fun z i => val i (z i)) (fun z i => obs i (z i))
      (Measure.infinitePi μ)
      =ᵐ[(Measure.infinitePi μ).map (fun z i => obs i (z i))] independent κ := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) (by fun_prop)
  exact (coordinate_pair_disintegration μ obs val hobs hval κ hκ).symm

end Invariant233.KernelProduct

end

end OAI
