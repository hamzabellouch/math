import OAI.NumberTheory.Ostmann.Characters.QuartetMovingAction

namespace OAI

/-! # Classifying a balanced action supported on at most two quartet leaves -/

namespace Ostmann

theorem quartetSign_classification (a b c d : ℤ)
    (ha : a = 0 ∨ a = 1 ∨ a = -1) (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (hc : c = 0 ∨ c = 1 ∨ c = -1) (hd : d = 0 ∨ d = 1 ∨ d = -1)
    (hsum : a + b + c + d = 0)
    (hcard : (if a = 0 then (0 : ℕ) else 1) + (if b = 0 then 0 else 1) +
      (if c = 0 then 0 else 1) + (if d = 0 then 0 else 1) ≤ 2) :
    ∃ choice : QuartetMovingCase, ∃ δ : ℤ,
      (δ = 0 ∨ δ = 1 ∨ δ = -1) ∧
      (((a, b), (c, d)) : (ℤ × ℤ) × (ℤ × ℤ)) =
        treeLeafMap (fun s : ℤ => δ * s) 2 (quartetMovingSign choice) := by
  rcases ha with ha | ha | ha
  all_goals rcases hb with hb | hb | hb
  all_goals rcases hc with hc | hc | hc
  all_goals rcases hd with hd | hd | hd
  all_goals simp only [ha, hb, hc, hd] at hsum hcard ⊢
  all_goals norm_num at hsum
  all_goals norm_num at hcard
  all_goals first
    | exact ⟨.leftPair, 0, by decide, by decide⟩
    | exact ⟨.leftPair, 1, by decide, by decide⟩
    | exact ⟨.leftPair, -1, by decide, by decide⟩
    | exact ⟨.rightPair, 1, by decide, by decide⟩
    | exact ⟨.rightPair, -1, by decide, by decide⟩
    | exact ⟨.cross true true, 1, by decide, by decide⟩
    | exact ⟨.cross true true, -1, by decide, by decide⟩
    | exact ⟨.cross true false, 1, by decide, by decide⟩
    | exact ⟨.cross true false, -1, by decide, by decide⟩
    | exact ⟨.cross false true, 1, by decide, by decide⟩
    | exact ⟨.cross false true, -1, by decide, by decide⟩
    | exact ⟨.cross false false, 1, by decide, by decide⟩
    | exact ⟨.cross false false, -1, by decide, by decide⟩

end Ostmann

end OAI
