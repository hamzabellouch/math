import OAI.Probability.FreeIsing.Estimates.PairCorrelation

namespace OAI

noncomputable section

namespace Problem367

theorem reducedWordDistance_prefixFlipWord {α : Type*} [DecidableEq α]
    (a : α) (u v : List α) (hu : List.IsChain (fun x y : α => x ≠ y) (a :: u)) :
    reducedWordDistance u (prefixFlipWord a v) = reducedWordDistance (a :: u) v := by
  cases v with
  | nil =>
      cases u with
      | nil => rfl
      | cons b u =>
          have hab : a ≠ b := (List.isChain_cons_cons.mp hu).1
          simp only [prefixFlipWord, reducedWordDistance_cons_ne hab.symm,
            List.length_nil, reducedWordDistance_nil_right, List.length_cons]
  | cons b v =>
      by_cases hab : a = b
      · subst b
        simp [prefixFlipWord]
      · simp only [prefixFlipWord, ite_eq_right hab]
        exact reducedWordDistance_move_head a b u v hab hu

theorem exists_treeAut_to_root_distance {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d,
      g.toEquiv u = ⟨[], List.IsChain.nil⟩ ∧
      ∀ v : TreeVertex d, (g.toEquiv v).1.length = reducedWordDistance u.1 v.1 := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil =>
      exact ⟨TreeAut.refl d, rfl, fun v => rfl⟩
  | cons a w ih =>
      obtain ⟨g, hg, hdist⟩ := ih hw.tail
      refine ⟨(prefixTreeAut a).trans g, ?_, ?_⟩
      · change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
        have hflip : prefixFlip a (⟨a :: w, hw⟩ : TreeVertex d) = ⟨w, hw.tail⟩ := by
          apply Subtype.ext
          simp [prefixFlip, prefixFlipWord]
        rw [hflip]
        exact hg
      · intro v
        change (g.toEquiv (prefixFlip a v)).1.length = reducedWordDistance (a :: w) v.1
        rw [hdist (prefixFlip a v)]
        exact reducedWordDistance_prefixFlipWord a w v.1 hw

end Problem367

end

end OAI
