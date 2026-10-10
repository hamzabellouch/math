import OAI.Analysis.BoundedHochschild.Main

namespace OAI

/-! Ordinary bounded Hochschild cocycles in degrees at least two are coboundaries. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u

theorem main_result
    {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] [WStarAlgebra M]
    (n : ℕ) (f : Cochain M (n + 2))
    (hf : ∀ x : Fin (n + 3) → M, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x : Fin (n + 2) → M,
      differentialValue g x = f x := by
  obtain ⟨X, hX, hXS, hXC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := M)
  let := hX
  let := hXS
  let := hXC
  have hf' : differential f = 0 := by
    ext x
    simpa only [differential_apply, zero_apply] using hf x
  obtain ⟨g, hg⟩ := bounded_primitive e f hf'
  refine ⟨g, ?_⟩
  intro x
  have h := congrArg (fun h : Cochain M (n + 2) => h x) hg
  simpa only [differential_apply] using h

end BoundedHochschild.KadisonRingrose

end

end OAI
