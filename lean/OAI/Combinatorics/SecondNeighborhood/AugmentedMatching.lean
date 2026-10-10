import OAI.Combinatorics.SecondNeighborhood.AugmentedGraph
import OAI.Combinatorics.SecondNeighborhood.MatchingAugmented

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]
    {r : V → V → Prop} {R C : Finset (V × V)}

private theorem alphaLift_image_isMatching
    {N : Finset (↥(Z r R C) × ↥R)}
    (hN : IsMatching (AlphaRelation r R C) N) :
    IsMatching (fun a b => AugmentedEdge r R C a b ∧ b.isRight)
      (N.image (alphaLift (r := r) (R := R) (C := C))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hN.1 f hf, by simp [alphaLift]⟩
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg alphaLift (hN.2.2 he' hf' (Sum.inl.inj hef))
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg alphaLift (hN.2.1 he' hf' (Sum.inr.inj hef))

private theorem betaLift_image_isMatching
    {N : Finset (↥(Z r R C) × ↥C)}
    (hN : IsMatching (BetaRelation r R C) N) :
    IsMatching (fun a b => AugmentedEdge r R C a b ∧ ¬a.isLeft)
      (N.image (betaLift (r := r) (R := R) (C := C))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hN.1 f hf, by simp [betaLift]⟩
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg betaLift (hN.2.1 he' hf' (Sum.inr.inj hef))
  · intro e he f hf hef
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f', hf', rfl⟩ := Finset.mem_image.mp hf
    exact congrArg betaLift (hN.2.2 he' hf' (Sum.inl.inj hef))

theorem alphaEdges_isMaximumMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    (hα : IsMaximumMatching
      (fun a b => AugmentedEdge r R C a b ∧ b.isRight)
      (M.filter (fun e => e.2.isRight))) :
    IsMaximumMatching (AlphaRelation r R C) (alphaEdges M) := by
  classical
  refine ⟨alphaEdges_isMatching hM, ?_⟩
  intro N hN
  have h := hα.2 (N.image alphaLift) (alphaLift_image_isMatching hN)
  rw [Finset.card_image_of_injective _ alphaLift_injective] at h
  have hcard : (M.filter (fun e => e.2.isRight)).card = (alphaEdges M).card := by
    rw [← alphaEdges_image hM, Finset.card_image_of_injective _ alphaLift_injective]
  simpa only [hcard] using h

theorem betaEdges_isMaximumMatching
    {M : Finset (LeftVertex r R C × RightVertex r R C)}
    (hM : IsMatching (AugmentedEdge r R C) M)
    (hβ : IsMaximumMatching
      (fun a b => AugmentedEdge r R C a b ∧ ¬a.isLeft)
      (M.filter (fun e => ¬e.1.isLeft))) :
    IsMaximumMatching (BetaRelation r R C) (betaEdges M) := by
  classical
  refine ⟨betaEdges_isMatching hM, ?_⟩
  intro N hN
  have h := hβ.2 (N.image betaLift) (betaLift_image_isMatching hN)
  rw [Finset.card_image_of_injective _ betaLift_injective] at h
  have hfilter : M.filter (fun e => ¬e.1.isLeft) =
      M.filter (fun e => e.1.isRight) := by
    ext ⟨a, b⟩
    cases a <;> simp
  have hcard : (M.filter (fun e => ¬e.1.isLeft)).card = (betaEdges M).card := by
    rw [hfilter, ← betaEdges_image hM,
      Finset.card_image_of_injective _ betaLift_injective]
  simpa only [hcard] using h

theorem exists_augmented_maximum_matching (r : V → V → Prop)
    (R C : Finset (V × V)) :
    ∃ M : Finset (LeftVertex r R C × RightVertex r R C),
      IsMaximumMatching (AugmentedEdge r R C) M ∧
      IsMaximumMatching (AlphaRelation r R C) (alphaEdges M) ∧
      IsMaximumMatching (BetaRelation r R C) (betaEdges M) := by
  classical
  have hblock : ∀ a b, AugmentedEdge r R C a b → b.isRight → a.isLeft := by
    intro a b hab hb
    cases a <;> cases b <;> simp_all [AugmentedEdge]
  obtain ⟨M, hM, hα, hβ⟩ := exists_maximum_matching_with_maximum_blocks
    (fun a : LeftVertex r R C => a.isLeft)
    (fun b : RightVertex r R C => b.isRight) hblock
  exact ⟨M, hM, alphaEdges_isMaximumMatching hM.1 hα,
    betaEdges_isMaximumMatching hM.1 hβ⟩

end SeymourSecondNeighborhood.Pruning

end OAI
