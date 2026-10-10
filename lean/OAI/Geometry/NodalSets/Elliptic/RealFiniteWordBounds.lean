import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.OfFn
import OAI.Geometry.NodalSets.Elliptic.RealFinitePositiveBounds

namespace OAI

namespace Yau
noncomputable section

theorem real_finite_word_positive_majorant (n N : ℕ) (C : List (Fin n) → ℝ) :
    ∃ B > 0, ∀ ds, ds.length ≤ N → C ds ≤ B := by
  obtain ⟨B,hB,hb⟩ := real_finite_positive_majorant
    (fun e : Σ r : Fin (N+1), Fin r.val → Fin n ↦ C (List.ofFn e.2))
  refine ⟨B,hB,fun ds hd ↦ ?_⟩
  simpa only [List.ofFn_get] using hb ⟨⟨ds.length,by omega⟩,ds.get⟩

end
end Yau

end OAI
