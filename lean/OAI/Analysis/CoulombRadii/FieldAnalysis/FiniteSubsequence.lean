import Mathlib

namespace OAI

section
open Filter Set
open scoped Topology
noncomputable section
namespace Coulomb
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
variable {X:Type*} [TopologicalSpace X] [Nonempty X]

lemma finite_simultaneous_subsequence (u:ℕ → ι → X)
    (hc:∀ i (φ:ℕ → ℕ),StrictMono φ → ∃ v:X,∃ ψ:ℕ → ℕ,StrictMono ψ ∧
      Tendsto (fun n => u (φ (ψ n)) i) atTop (𝓝 v)) :
    ∃ v:ι → X,∃ φ:ℕ → ℕ,StrictMono φ ∧ ∀ i,Tendsto (fun n => u (φ n) i) atTop (𝓝 (v i)) := by
  have H (s:Finset ι) : ∃ v:ι → X,∃ φ:ℕ → ℕ,StrictMono φ ∧
      ∀ i∈s,Tendsto (fun n => u (φ n) i) atTop (𝓝 (v i)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => Classical.ofNonempty,id,strictMono_id,by simp⟩
    | @insert i s his ih =>
      obtain ⟨v,φ,hφ,hv⟩ := ih
      obtain ⟨w,ψ,hψ,hw⟩ := hc i φ hφ
      refine ⟨Function.update v i w,φ ∘ ψ,hφ.comp hψ,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · simpa only [Function.update_self,Function.comp_def] using hw
      · have hji:j≠i := by intro he; subst j; contradiction
        simpa only [Function.update_of_ne hji,Function.comp_def] using
          (hv j hj).comp hψ.tendsto_atTop
  obtain ⟨v,φ,hφ,hv⟩ := H Finset.univ
  exact ⟨v,φ,hφ,fun i => hv i (Finset.mem_univ i)⟩
end Coulomb
end

end

end OAI
