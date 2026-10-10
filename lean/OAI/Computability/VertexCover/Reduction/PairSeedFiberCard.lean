import Mathlib
import OAI.Computability.VertexCover.Reduction.PairHitsProbability
import OAI.Computability.VertexCover.Reduction.HonestSelectionCompatible

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

def leftTemplate (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (x : Fin Φ.u) : Φ.Query d :=
  ⟨e.1.1, Function.update (Φ.query seed e.1.1).2.1 ⟨e.1.2, e.2⟩ x,
    (Φ.query seed e.1.1).2.2⟩

def rightTemplate (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (y : Fin Φ.v) : Φ.Query d :=
  ⟨e.1.2, (Φ.query seed e.1.2).2.1,
    Function.update (Φ.query seed e.1.2).2.2 ⟨e.1.1, e.2⟩ y⟩

theorem leftTemplate_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (x : Fin Φ.u) : x ∈ (Φ.leftTemplate seed e x).scopeU := by
  refine Finset.mem_image.mpr ⟨⟨e.1.2, e.2⟩, Finset.mem_univ _, ?_⟩
  exact Function.update_self _ _ _

theorem rightTemplate_mem (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (y : Fin Φ.v) : y ∈ (Φ.rightTemplate seed e y).scopeV := by
  refine Finset.mem_image.mpr ⟨⟨e.1.1, e.2⟩, Finset.mem_univ _, ?_⟩
  exact Function.update_self _ _ _

def replaceSeed (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) : Φ.Seeds d :=
  Function.update seed e c

theorem query_update_left (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) :
    Φ.query (Φ.replaceSeed seed e c) e.1.1 = Φ.leftTemplate seed e (Φ.left c) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Prod.ext
  · funext k
    dsimp only [query, replaceSeed, leftTemplate] at *
    by_cases hk : k = ⟨e.1.2, e.2⟩
    · subst k
      simp [query, replaceSeed, ]
    · have hne : (⟨(e.1.1, k.1), k.2⟩ : PositionPair d) ≠ e := by
        intro heq
        apply hk
        exact Subtype.ext (congrArg (fun a : PositionPair d => a.1.2) heq)
      simp only [Function.update, dite_eq_right hne]
      split_ifs with h
      · exact False.elim (hk (Subtype.ext (congrArg Subtype.val h)))
      · rfl
  · funext k
    have hne : (⟨(k.1, e.1.1), k.2⟩ : PositionPair d) ≠ e := by
      intro heq
      exact (ne_of_lt e.2) (congrArg (fun a : PositionPair d => a.1.2) heq)
    simp [query, replaceSeed, leftTemplate, Function.update_of_ne hne]

theorem query_update_right (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (e : PositionPair d) (c : Fin Φ.M) :
    Φ.query (Φ.replaceSeed seed e c) e.1.2 = Φ.rightTemplate seed e (Φ.right c) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply Prod.ext
  · funext k
    have hne : (⟨(e.1.2, k.1), k.2⟩ : PositionPair d) ≠ e := by
      intro heq
      exact (ne_of_lt e.2).symm (congrArg (fun a : PositionPair d => a.1.1) heq)
    simp [query, replaceSeed, rightTemplate, Function.update_of_ne hne]
  · funext k
    dsimp only [query, replaceSeed, rightTemplate] at *
    by_cases hk : k = ⟨e.1.1, e.2⟩
    · subst k
      simp [query, replaceSeed, ]
    · have hne : (⟨(k.1, e.1.2), k.2⟩ : PositionPair d) ≠ e := by
        intro heq
        apply hk
        exact Subtype.ext (congrArg (fun a : PositionPair d => a.1.1) heq)
      simp only [Function.update, dite_eq_right hne]
      split_ifs with h
      · exact False.elim (hk (Subtype.ext (congrArg Subtype.val h)))
      · rfl

abbrev PrivateLists (Φ : LabelCover) (d : ℕ) := ∀ i : Φ.Query d, List i.LocalLabel

def PairSeedHit (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (e : PositionPair d) : Prop :=
  ∃ a ∈ L (Φ.query seed e.1.1), ∃ b ∈ L (Φ.query seed e.1.2),
    Φ.Compatible {⟨Φ.query seed e.1.1, a⟩, ⟨Φ.query seed e.1.2, b⟩}

noncomputable def pairSeedFiber (Φ : LabelCover) {d : ℕ} (L : Φ.PrivateLists d)
    (seed : Φ.Seeds d) (e : PositionPair d) : Finset (Fin Φ.M) := by
  classical
  exact Finset.univ.filter (fun c => Φ.PairSeedHit L (Φ.replaceSeed seed e c) e)

theorem pairSeedFiber_card_le (Φ : LabelCover) {d ell : ℕ} {σ : ℝ}
    (hval : Φ.value ≤ σ) (L : Φ.PrivateLists d)
    (hL : ∀ i, (L i).length ≤ ell) (seed : Φ.Seeds d) (e : PositionPair d) :
    ((Φ.pairSeedFiber L seed e).card : ℝ) ≤ (ell : ℝ)^2 * σ * Φ.M := by
  classical
  have heq : Φ.pairSeedFiber L seed e = Decoding.pairHits Φ
      (Φ.leftTemplate seed e) (Φ.rightTemplate seed e)
      (fun x => L (Φ.leftTemplate seed e x)) (fun y => L (Φ.rightTemplate seed e y)) := by
    ext c
    simp only [pairSeedFiber, Decoding.pairHits, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold PairSeedHit Decoding.PairHit
    rw [Φ.query_update_left seed e c, Φ.query_update_right seed e c]
  rw [heq]
  exact Decoding.pairHits_card_le Φ _ _ (Φ.leftTemplate_mem seed e)
    (Φ.rightTemplate_mem seed e) _ _ hval (fun _ => hL _) (fun _ => hL _)

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
