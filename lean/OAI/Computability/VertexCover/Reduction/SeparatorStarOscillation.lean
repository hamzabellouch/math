import Mathlib
import OAI.Computability.VertexCover.Reduction.SeparatorContinuousSumOdd

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem query_eq_of_questions (Φ : LabelCover) {d : ℕ} (seed seed' : Φ.Seeds d)
    (j : Fin d)
    (hL : ∀ k (h : j < k), Φ.left (seed ⟨(j,k),h⟩) = Φ.left (seed' ⟨(j,k),h⟩))
    (hR : ∀ k (h : k < j), Φ.right (seed ⟨(k,j),h⟩) = Φ.right (seed' ⟨(k,j),h⟩)) :
    Φ.query seed j = Φ.query seed' j := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Prod.ext
  · funext k; exact hL k.1 k.2
  · funext k; exact hR k.1 k.2

theorem query_replaceSeed_other (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) (j : Fin d)
    (hjl : j ≠ e.1.1) (hjr : j ≠ e.1.2) :
    Φ.query seed j = Φ.query (Φ.replaceSeed seed e c) j := by
  apply Φ.query_eq_of_questions
  · intro k h
    have hn : (⟨(j,k),h⟩ : PositionPair d) ≠ e := by
      intro he; exact hjl (congrArg (fun e : PositionPair d => e.1.1) he)
    simp [replaceSeed, Function.update_of_ne hn]
  · intro k h
    have hn : (⟨(k,j),h⟩ : PositionPair d) ≠ e := by
      intro he; exact hjr (congrArg (fun e : PositionPair d => e.1.2) he)
    simp [replaceSeed, Function.update_of_ne hn]

theorem query_eq_away (Φ : LabelCover) {d : ℕ} (seed seed' : Φ.Seeds d) (k : Fin d)
    (hL : ∀ e : PositionPair d, e.1.1 ≠ k → Φ.left (seed e) = Φ.left (seed' e))
    (hR : ∀ e : PositionPair d, e.1.2 ≠ k → Φ.right (seed e) = Φ.right (seed' e))
    (j : Fin d) (hj : j ≠ k) : Φ.query seed j = Φ.query seed' j := by
  apply Φ.query_eq_of_questions
  · intro l h; exact hL ⟨(j,l),h⟩ hj
  · intro l h; exact hR ⟨(l,j),h⟩ hj

theorem separator_weight_oscillation (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d)
    (s t : Fin d → Fin (Φ.WeightDimension d) → ℝ)
    (hs : Φ.InWeightCube s) (ht : Φ.InWeightCube t) (k : Fin d)
    (heq : ∀ j, j ≠ k → s j = t j) :
    |Φ.separator A hA (Φ.continuousSum seed s) -
      Φ.separator A hA (Φ.continuousSum seed t)| ≤ 2 := by
  apply (Φ.separator_lipschitz A hA _ _).trans
  have h := Φ.continuousSum_change_blocks seed seed s t hs ht {k}
    (fun j hj => ⟨rfl, heq j (by simpa using hj)⟩)
  simpa using h

theorem separator_seed_oscillation (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (hs : Φ.InWeightCube s)
    (e : PositionPair d) (c : Fin Φ.M) :
    |Φ.separator A hA (Φ.continuousSum seed s) -
      Φ.separator A hA (Φ.continuousSum (Φ.replaceSeed seed e c) s)| ≤ 4 := by
  apply (Φ.separator_lipschitz A hA _ _).trans
  have h := Φ.continuousSum_change_blocks seed (Φ.replaceSeed seed e c) s s hs hs
    {e.1.1, e.1.2} (fun j hj => ⟨Φ.query_replaceSeed_other seed e c j
      (fun h => hj (by simp [h]))
      (fun h => hj (by simp [h])), rfl⟩)
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  norm_num [hne] at h
  exact h

theorem separator_star_oscillation (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed seed' : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) (hs : Φ.InWeightCube s)
    (k : Fin d)
    (hL : ∀ e : PositionPair d, e.1.1 ≠ k → Φ.left (seed e) = Φ.left (seed' e))
    (hR : ∀ e : PositionPair d, e.1.2 ≠ k → Φ.right (seed e) = Φ.right (seed' e)) :
    |Φ.separator A hA (Φ.continuousSum seed s) -
      Φ.separator A hA (Φ.continuousSum seed' s)| ≤ 2 := by
  apply (Φ.separator_lipschitz A hA _ _).trans
  have h := Φ.continuousSum_change_blocks seed seed' s s hs hs {k}
    (fun j hj => ⟨Φ.query_eq_away seed seed' k hL hR j (by simpa using hj), rfl⟩)
  simpa using h

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
