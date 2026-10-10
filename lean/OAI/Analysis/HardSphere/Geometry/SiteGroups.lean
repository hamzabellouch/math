import Mathlib
import OAI.Analysis.HardSphere.Allocation.CertificateUseful

namespace OAI

section

section

end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

def siteAllocationKernel (total : ℕ) :
    Kernel (V→Finset I) (V→Allocation total I) :=
  ⟨fun E ↦ Measure.pi (fun v ↦ (allocationPMF (E v) total).toMeasure),measurable_of_countable _⟩

instance siteAllocationKernel_markov (total : ℕ) :
    IsMarkovKernel (siteAllocationKernel (V:=V) (I:=I) total) :=
  ⟨fun _ ↦ by change IsProbabilityMeasure (Measure.pi _); infer_instance⟩

omit [DecidableEq V] in
lemma siteAllocation_joint_half_bad (E B : V→Finset I) (total q : ℕ)
    (group : Fin (2*q)↪Fin total) (T : Finset V)
    (hE : ∀v∈T,total ≤ (E v).card)
    (hB : ∀v∈T,10*(E v∩B v).card ≤ (E v).card) :
    siteAllocationKernel total E
      {a | ∀v∈T,∃f,a v=some f ∧ q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B v)).card}≤
      ENNReal.ofReal ((2/5:ℝ)^q)^T.card := by
  change Measure.pi (fun v ↦ (allocationPMF (E v) total).toMeasure) _ ≤ _
  have he : {a : V→Allocation total I | ∀v∈T,∃f,a v=some f ∧
      q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B v)).card}=
      (↑T : Set V).pi (fun v ↦ {a | ∃f,a=some f ∧
        q ≤ (Finset.univ.filter (fun k ↦ f (group k)∈B v)).card}) := by
    rfl
  rw [he,Measure.pi_pi_finset]
  calc
    _ ≤ ∏v∈T,ENNReal.ofReal ((2/5:ℝ)^q) :=
      Finset.prod_le_prod (fun v hv ↦ allocated_restriction_half_bad
        (E v) (B v) total q (hE v hv) group (hB v hv))
    _ = _ := by simp

end HardSphere.Sampling

namespace HardSphere.Groups
open Sampling Wiener PathCutoff

def physicalAllocationKernel {N K : ℕ} {L : Length} (m total : ℕ)
    (r R C S s₀ : ℝ) (u : Time) :
    Kernel (ConfigurationPath N L) ((Fin 3→Fin K)→Allocation total (Fin N)) :=
  (siteAllocationKernel total).comap
    (fun ω v ↦ eligibleList m r R C S s₀ u v ω)
    (Measurable.of_eval (fun v ↦ eligibleList_measurable m r R C S s₀ u v))

instance physicalAllocationKernel_markov {N K : ℕ} {L : Length} (m total : ℕ)
    (r R C S s₀ : ℝ) (u : Time) :
    IsMarkovKernel (physicalAllocationKernel (N:=N) (K:=K) (L:=L) m total r R C S s₀ u) := by
  unfold physicalAllocationKernel
  infer_instance

end HardSphere.Groups

end
end

end

end OAI
