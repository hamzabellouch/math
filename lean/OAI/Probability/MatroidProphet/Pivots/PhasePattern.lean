import OAI.Probability.MatroidProphet.Pivots.Phases

namespace OAI

namespace MatroidProphet.Pivots

open Set Finset

variable {α G Z B : Type*} [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z]
    [Fintype B] [LinearOrder B] {n : ℕ}

lemma lex_lt_true_iff_le_false
    {B : Type u_4} [Fintype B] [LinearOrder B] (p : B ×ₗ Bool) (b : B) :
    p < toLex (b, true) ↔ p ≤ toLex (b, false) := by
  rw [Prod.Lex.lt_iff, Prod.Lex.le_iff]
  cases (ofLex p).2 <;> simp

lemma phase_before_true
    {α : Type u_1} {G : Type u_2} {Z : Type u_3} {B : Type u_4}
    [Fintype α] [LinearOrder α] [Fintype G] [Fintype Z] [Fintype B] [LinearOrder B]
    (F K : B → Set α) (a : G → α) (z : Z → α)
    (θ : G → B) (β : Z → B) (b : B) :
    blockBefore (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, true)) =
      blockPrefix (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) (toLex (b, false)) := by
  unfold blockBefore blockPrefix
  congr 1
  ext o
  exact lex_lt_true_iff_le_false _ _

lemma mem_phase_pattern (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (test : Fin n → α) (f : Fin n) :
    f ∈ blockBirthPattern M (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) test
        (fun p => (ofLex p).2) ↔
      ∃ b, test f ∈ upperPath M F a θ b ∧
        test f ∉ M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b}) := by
  classical
  simp only [blockBirthPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, hafter, hbefore⟩
    change (ofLex p).2 = true at hp
    have hp' : p = toLex ((ofLex p).1, true) := congrArg toLex (Prod.ext rfl hp)
    rw [hp'] at hafter hbefore
    rw [phase_endpoint M hE F K hF hK a z θ β hz] at hafter
    rw [phase_before_true, phase_interior M hE F K hK a z θ β hz] at hbefore
    exact ⟨(ofLex p).1, hafter, hbefore⟩
  · rintro ⟨b, hafter, hbefore⟩
    refine ⟨toLex (b, true), rfl, ?_, ?_⟩
    · rwa [phase_endpoint M hE F K hF hK a z θ β hz]
    · rwa [phase_before_true, phase_interior M hE F K hK a z θ β hz]

noncomputable def residualOfLayers (M : Matroid α) (F K : B → Set α) (a : G → α)
    (z : Z → α) (θ : G → B) (β : Z → B) (test : Fin n → α)
    (P : B → Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun f => ∃ b, f ∈ P b ∧
    test f ∉ M.closure (lowerPath M F a θ b ∪ K b ∪ z '' {w | β w = b})

lemma first_inter_phase_eq_residual (M : Matroid α) (hE : M.E = univ)
    (F K : B → Set α) (hF : Monotone F) (hK : ∀ b, K b ⊆ F b)
    (a : G → α) (z : Z → α) (θ : G → B) (β : Z → B)
    (hz : ∀ w, z w ∈ upperPath M F a θ (β w)) (test : Fin n → α)
    (P : B → Finset (Fin n)) (first : Finset (Fin n))
    (hfirst : ∀ f, f ∈ first ↔ ∃ b, f ∈ P b)
    (hP : ∀ b f, f ∈ P b → test f ∈ upperPath M F a θ b ∧ test f ∉ lowerPath M F a θ b) :
    first ∩ blockBirthPattern M (phaseOld F K) (Sum.elim a z) (phasePlacement θ β) test
        (fun p => (ofLex p).2) = residualOfLayers M F K a z θ β test P := by
  classical
  ext f
  rw [Finset.mem_inter, mem_phase_pattern M hE F K hF hK a z θ β hz]
  simp only [residualOfLayers, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hf, c, hc, hcnot⟩
    obtain ⟨b, hb⟩ := (hfirst f).1 hf
    have hpb := hP b f hb
    have hbc : b = c := by
      rcases lt_trichotomy b c with h | h | h
      · apply False.elim
        apply hcnot
        exact M.subset_closure _ (by simp [hE]) (Or.inl (Or.inl
          (upperPath_subset_lowerPath M F a θ h hpb.1)))
      · exact h
      · exact (hpb.2 (upperPath_subset_lowerPath M F a θ h hc)).elim
    exact ⟨b, hb, hbc.symm ▸ hcnot⟩
  · rintro ⟨b, hb, hnot⟩
    exact ⟨(hfirst f).2 ⟨b, hb⟩, b, (hP b f hb).1, hnot⟩

end MatroidProphet.Pivots

end OAI
