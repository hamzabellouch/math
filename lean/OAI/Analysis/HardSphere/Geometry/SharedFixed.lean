import Mathlib
import OAI.Analysis.HardSphere.Conditioning.SharedTransport

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma ambientShared_constant (s : Finset I) (σ : Equiv.Perm I) (hσ : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E) :
    ambientSharedKernel s σ hσ ξ ρ A e=
      ambientSharedKernel s σ hσ (Kernel.const Unit (ξ e))
        (fun i ↦ Kernel.const Unit (ρ i e)) (Prod.snd ⁻¹' (Prod.mk e ⁻¹' A)) () := by
  rw [ambientSharedKernel_apply_measure,ambientSharedKernel_apply_measure,Kernel.const_apply]
  congr 1
  ext x B hB
  simp only [Kernel.comap_apply]
  rw [ambientRefreshKernel_apply s σ hσ ρ A hA,
    ambientRefreshKernel_apply s σ hσ _ _ (hA.preimage measurable_prodMk_left |>.preimage measurable_snd)]
  simp only [Kernel.const_apply,mem_preimage]

omit [Fintype I] in
lemma ambientShared_constant_of (s : Finset I) (σ : Equiv.Perm I) (hσ : ∀i,i∉s→σ i=i)
    (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E)
    (μ : Measure (∀i,X i)) [IsFiniteMeasure μ]
    (ν : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (ν i)]
    (B : Set (∀i,X i)) (hμ : ξ e=μ) (hν : ∀i,ρ i e=ν i)
    (hB : Prod.mk e ⁻¹' A=B) :
    ambientSharedKernel s σ hσ ξ ρ A e=
      ambientSharedKernel s σ hσ (Kernel.const Unit μ)
        (fun i ↦ Kernel.const Unit (ν i)) (Prod.snd ⁻¹' B) () := by
  simpa only [hμ,hν,hB] using ambientShared_constant s σ hσ ξ ρ A hA e

end HardSphere.Comparison
end
end

end OAI
