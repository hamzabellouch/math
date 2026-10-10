import OAI.NumberTheory.Ostmann.Characters.BinaryExposureLeaves
import OAI.NumberTheory.Ostmann.Characters.FrequencyExposure

namespace OAI

noncomputable section
namespace Ostmann.Characters.FrequencyExposure
open BinaryExposure

theorem paired_frequency_leaf_count (ε:ℝ) (hε:0<ε) :
    ∃ C:NNReal, 0<C ∧ ∀ Q:ℕ, ∀ [NeZero Q], ∀ H:Type*,
      ∀ d:List Bool→Data Q, ∀ a:∀p,Coefficients H (d p),
      ∀ left right:List Bool→H→(ZMod Q)ˣ→(ZMod Q)ˣ→H,
      ∀ k p h,
      (Nat.card {z:BinaryHaar.Leaves (ZMod Q)ˣ k //
        leafAdmissible (constraint d a) (update false left) (update true right) k (p,h) z}:ℝ)/
        Nat.card (BinaryHaar.Leaves (ZMod Q)ˣ k) ≤
      ((budget C ε d k p).value:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := paired_frequency_tree_count ε hε
  refine ⟨C,hC,?_⟩
  intro Q _ H d a left right k p h
  rw [leaf_count_eq_average]
  calc
    _ ≤ avg (fun _:(ZMod Q)ˣ=>((budget C ε d k p).value:ℝ)) := by
      apply avg_mono
      intro t
      rw [probability_eq_count]
      exact hbound Q H d a left right k p h t
    _ = _ := avg_const _

end Ostmann.Characters.FrequencyExposure

end

end OAI
