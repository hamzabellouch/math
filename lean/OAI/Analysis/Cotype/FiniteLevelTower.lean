import OAI.Analysis.Cotype.FiniteLevelLift

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

def FiniteLevelLift (m : ℕ) (D : ℝ) (E F : Submodule ℝ X) : Prop :=
  ∀ z : Fin m → E, ∃ H : Cube m → F,
    (∀ i, moment X (fun ε => (H ε : X)) i = (z i : X)) ∧
    cubeL2 F H ≤ 3 * D * Real.sqrt (∑ i, ‖z i‖^2)

theorem exists_finiteLevel_tower {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDp : 0 < D)
    (E : Submodule ℝ X) [FiniteDimensional ℝ E] :
    ∃ A : ℕ → Submodule ℝ X, A 0 = E ∧ Monotone A ∧
      (∀ l, FiniteDimensional ℝ (A l)) ∧
      ∀ l, FiniteLevelLift m D (A l) (A (l+1)) := by
  classical
  let S := {F : Submodule ℝ X // FiniteDimensional ℝ F}
  have hnext (F : S) : ∃ G : S, F.val ≤ G.val ∧ FiniteLevelLift m D F.val G.val := by
    let := F.property
    obtain ⟨G, hFG, hG, hL⟩ := exists_finiteLevel_lift hD hDp F.val
    exact ⟨⟨G,hG⟩,hFG,hL⟩
  choose next hn hL using hnext
  let A : ℕ → S := fun l => next^[l] ⟨E, inferInstance⟩
  have hA (l : ℕ) : A (l+1) = next (A l) := Function.iterate_succ_apply' _ _ _
  refine ⟨fun l => (A l).val, rfl, ?_, fun l => (A l).property, ?_⟩
  · apply monotone_nat_of_le_succ
    intro l
    rw [hA]
    exact hn _
  · intro l
    change FiniteLevelLift m D (A l).val (A (l+1)).val
    rw [hA]
    exact hL _

end Cotype

end

end OAI
