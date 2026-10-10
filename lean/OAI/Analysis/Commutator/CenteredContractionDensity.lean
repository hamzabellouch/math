import Mathlib
import OAI.Analysis.Commutator.TracialConjugation
import OAI.Analysis.Commutator.TracialL2Tools

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.TracialL2

open TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma exists_centered_contraction_dense_sequence [TopologicalSpace.SeparableSpace τ.GNS] :
    ∃ x : ℕ → A, (∀ j,‖x j‖ ≤ 1) ∧ (∀ j,τ (x j)=0) ∧
      ∀ a : A,‖a‖ ≤ 1 → τ a=0 → ∀ ε : ℝ,0<ε → ∃ j,norm τ (a-x j)<ε := by
  classical
  let C := {a : A // ‖a‖ ≤ 1 ∧ τ a=0}
  let S : Set τ.GNS := Set.range (fun a : C => algebraVector τ a.val)
  have : Nonempty S :=
    ⟨⟨algebraVector τ 0,⟨⟨0,by simp⟩,rfl⟩⟩⟩
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq S
  choose x hx using (fun n => (u n).property)
  refine ⟨fun n => (x n).val,fun n => (x n).property.1,fun n => (x n).property.2,?_⟩
  intro a ha hc ε hε
  obtain ⟨j,hj⟩ := hu.exists_dist_lt ⟨algebraVector τ a,⟨⟨a,ha,hc⟩,rfl⟩⟩ hε
  refine ⟨j,?_⟩
  change dist (algebraVector τ a) (u j).val<ε at hj
  rw [←hx j,dist_eq_norm,←map_sub] at hj
  simpa only [algebraVector_apply,UniformSpace.Completion.norm_coe,norm] using hj

end Kadison.TracialL2

end

end
end

end OAI
