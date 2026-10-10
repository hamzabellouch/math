import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.KernelProduct

variable {ι : Type*} {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

def independent (κ : ∀ i, Kernel (A i) (B i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel (∀ i, A i) (∀ i, B i) where
  toFun x := Measure.infinitePi (fun i => κ i (x i))
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_squareCylinders.symm
      (isPiSystem_squareCylinders
        (fun _ => MeasurableSpace.isPiSystem_measurableSet) (by simp))
    rintro _ ⟨s, t, ht, rfl⟩
    simp only [Set.mem_univ_pi, Set.mem_ofPred_eq] at ht
    simp_rw [Measure.infinitePi_pi _ (fun i _ => ht i)]
    exact Finset.measurable_fun_prod s (fun i _ =>
      (Kernel.measurable_coe (κ i) (ht i)).comp (measurable_pi_apply i))

end Invariant233.KernelProduct

namespace Invariant233.KernelProduct
variable {ι : Type*} {A B : ι → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

def pairCoordinates : ((∀ i, A i) × (∀ i, B i)) ≃ᵐ (∀ i, A i × B i) where
  toFun p i := (p.1 i, p.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv p := rfl
  right_inv z := rfl
  measurable_toFun := by
    change Measurable (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ∀ i, A i × B i => (fun i => (z i).1, fun i => (z i).2))
    fun_prop

end Invariant233.KernelProduct

end

end OAI
