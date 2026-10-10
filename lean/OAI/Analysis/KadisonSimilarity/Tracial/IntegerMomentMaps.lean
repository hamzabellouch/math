import OAI.Analysis.KadisonSimilarity.Tracial.TracialMomentContinuity

namespace OAI

/-! Naturality and coefficient reindexing for finite integer-power words. -/

namespace KadisonSimilarity
open HochschildPatching
variable {A B I J : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem integerEval_hom (φ : A →⋆ₐ[ℂ] B) (F : I → A) (u : unitary A)
    (a : Option I) (l : List (IntAtom I)) :
    φ (integerEval F u a l) = integerEval (φ ∘ F) (mapUnitary φ u) a l := by
  simp only [integerEval, map_mul, wordCoeff_hom, map_list_prod, List.map_map]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro b _
  simp only [Function.comp_apply, map_mul, wordCoeff_hom, mapUnitary_zpow]

theorem integerEval_reindex (F : J → A) (f : I → J) (u : unitary A)
    (a : Option I) (l : List (IntAtom I)) :
    integerEval F u (a.map f) (l.map (fun b => (b.1, b.2.map f))) =
      integerEval (F ∘ f) u a l := by
  simp only [integerEval, List.map_map]
  congr 1
  · exact wordCoeff_map F f a
  · apply congrArg List.prod
    apply List.map_congr_left
    intro b _
    simp only [Function.comp_apply, wordCoeff_map]

omit [CStarAlgebra A] [CStarAlgebra B] in
theorem admissibleIntTail_reindex (f : I → J) (l : List (IntAtom I))
    (hl : admissibleIntTail l) :
    admissibleIntTail (l.map (fun b => (b.1, b.2.map f))) := by
  refine ⟨fun h => hl.1 (List.map_eq_nil_iff.mp h), ?_⟩
  intro b hb
  rw [← List.map_dropLast] at hb
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact fun h => hl.2 c hc (Option.map_eq_none_iff.mp h)

end KadisonSimilarity

end OAI
