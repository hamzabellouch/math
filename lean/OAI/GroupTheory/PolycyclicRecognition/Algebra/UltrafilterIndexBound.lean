import OAI.GroupTheory.PolycyclicRecognition.Algebra.UltrafilterSubgroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UniformCosetBound

namespace OAI

/-! # A uniform local coset bound survives an ultrafilter limit -/
noncomputable section
namespace PolycyclicRecognition
open Filter
variable {G I : Type} [Group G]

theorem ultrafilterSubgroup_index (U : Ultrafilter I) (K : I → Subgroup G)
    (b : ℕ) (h : ∀ f : Fin (b + 1) → G,
      ∀ᶠ k in U, ∃ i j, i ≠ j ∧ (f i)⁻¹ * f j ∈ K k) :
    (ultrafilterSubgroup U K).FiniteIndex ∧ (ultrafilterSubgroup U K).index ≤ b := by
  apply finiteIndex_of_cosetCollisionBound
  intro f
  have he : ∀ᶠ k in U, ∃ p : Fin (b + 1) × Fin (b + 1),
      p.1 ≠ p.2 ∧ (f p.1)⁻¹ * f p.2 ∈ K k := by
    filter_upwards [h f] with k hk
    obtain ⟨i, j, hij, hm⟩ := hk
    exact ⟨(i, j), hij, hm⟩
  obtain ⟨p, hp⟩ := Ultrafilter.eventually_exists_iff.mp he
  have hne := hp.exists.choose_spec.1
  exact ⟨p.1, p.2, hne, hp.mono (fun _ h => h.2)⟩

end PolycyclicRecognition

end

end OAI
