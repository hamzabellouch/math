import Mathlib
import OAI.Analysis.HardSphere.Kernels.ParameterSuccess

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E U X Y : Type*} [MeasurableSpace E] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]

def parameterPairedKernel (Q : Kernel E U) [IsFiniteKernel Q]
    (κ : Kernel (E×U) X) (η : Kernel (E×U) Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y))
    (hS : MeasurableSet S) (hT : MeasurableSet T) : Kernel E (U×(X×Y)) :=
  Q.compProd ((parameterSuccessKernel κ S hS).prod (parameterSuccessKernel η T hT))

lemma parameterPairedKernel_mass (Q : Kernel E U) [IsMarkovKernel Q]
    (κ : Kernel (E×U) X) (η : Kernel (E×U) Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (e : E)
    (hκ : ∀ᵐu ∂Q e,0 < κ (e,u) (Prod.mk (e,u) ⁻¹' S))
    (hη : ∀ᵐu ∂Q e,0 < η (e,u) (Prod.mk (e,u) ⁻¹' T)) :
    parameterPairedKernel Q κ η S T hS hT e univ=1 := by
  rw [parameterPairedKernel,Kernel.compProd_apply MeasurableSet.univ]
  have hea : (fun u ↦ ((parameterSuccessKernel κ S hS).prod
      (parameterSuccessKernel η T hT)) (e,u) (Prod.mk u ⁻¹' univ))=ᵐ[Q e] fun _ ↦ 1 := by
    filter_upwards [hκ,hη] with u hu hv
    simp only [preimage_univ,Kernel.prod_apply]
    rw [show (Set.univ : Set (X×Y))=(Set.univ:Set X)×ˢ(Set.univ:Set Y) from Set.univ_prod_univ.symm,
      Measure.prod_prod,parameterSuccessKernel_mass κ S hS hu,
      parameterSuccessKernel_mass η T hT hv,one_mul]
  rw [lintegral_congr_ae hea]
  simp

lemma parameterPairedKernel_markov (Q : Kernel E U) [IsMarkovKernel Q]
    (κ : Kernel (E×U) X) (η : Kernel (E×U) Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y))
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀e,∀ᵐu ∂Q e,0 < κ (e,u) (Prod.mk (e,u) ⁻¹' S))
    (hη : ∀e,∀ᵐu ∂Q e,0 < η (e,u) (Prod.mk (e,u) ⁻¹' T)) :
    IsMarkovKernel (parameterPairedKernel Q κ η S T hS hT) :=
  ⟨fun e ↦ ⟨parameterPairedKernel_mass Q κ η S T hS hT e (hκ e) (hη e)⟩⟩

lemma parameterPairedKernel_fst (Q : Kernel E U) [IsFiniteKernel Q]
    (κ : Kernel (E×U) X) (η : Kernel (E×U) Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y))
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hη : ∀e,∀ᵐu ∂Q e,0 < η (e,u) (Prod.mk (e,u) ⁻¹' T)) :
    (parameterPairedKernel Q κ η S T hS hT).map (fun p ↦ (p.1,p.2.1))=
      Q.compProd (parameterSuccessKernel κ S hS) := by
  have hm : Measurable (fun p : U×(X×Y) ↦ (p.1,p.2.1)) := by fun_prop
  apply Kernel.ext
  intro e
  ext B hB
  rw [Kernel.map_apply' _ hm _ hB,parameterPairedKernel,
    Kernel.compProd_apply (hB.preimage hm),Kernel.compProd_apply hB]
  apply lintegral_congr_ae
  filter_upwards [hη e] with u hu
  rw [Kernel.prod_apply]
  have he : (fun p : X×Y ↦ (u,p))⁻¹' ((fun p : U×(X×Y) ↦ (p.1,p.2.1))⁻¹' B)=
      (Prod.mk u ⁻¹' B)×ˢ(univ : Set Y) := by ext p; simp
  rw [he,Measure.prod_prod,parameterSuccessKernel_mass η T hT hu,mul_one]

lemma parameterPairedKernel_snd (Q : Kernel E U) [IsFiniteKernel Q]
    (κ : Kernel (E×U) X) (η : Kernel (E×U) Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y))
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hκ : ∀e,∀ᵐu ∂Q e,0 < κ (e,u) (Prod.mk (e,u) ⁻¹' S)) :
    (parameterPairedKernel Q κ η S T hS hT).map (fun p ↦ (p.1,p.2.2))=
      Q.compProd (parameterSuccessKernel η T hT) := by
  have hm : Measurable (fun p : U×(X×Y) ↦ (p.1,p.2.2)) := by fun_prop
  apply Kernel.ext
  intro e
  ext B hB
  rw [Kernel.map_apply' _ hm _ hB,parameterPairedKernel,
    Kernel.compProd_apply (hB.preimage hm),Kernel.compProd_apply hB]
  apply lintegral_congr_ae
  filter_upwards [hκ e] with u hu
  rw [Kernel.prod_apply]
  have he : (fun p : X×Y ↦ (u,p))⁻¹' ((fun p : U×(X×Y) ↦ (p.1,p.2.2))⁻¹' B)=
      (univ : Set X)×ˢ(Prod.mk u ⁻¹' B) := by ext p; simp
  rw [he,Measure.prod_prod,parameterSuccessKernel_mass κ S hS hu,one_mul]

end HardSphere.Comparison

end
end

end

end OAI
