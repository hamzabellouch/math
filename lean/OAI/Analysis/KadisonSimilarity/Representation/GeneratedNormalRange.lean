import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry

namespace OAI

/-! The bounded L²-generated algebra has a normal range whenever the
ambient tracial geometry has a faithful normal left range. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge

namespace TracialCornerGeometry
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry A H)

theorem exists_l2Generated_normal_range (h1 : G.trace 1 = 1)
    (hf : Function.Injective G.vector) (M : VonNeumannAlgebra H)
    (hrange : G.left.range = M.toStarSubalgebra) (S : StarSubalgebra ℂ A) :
    ∃ N : VonNeumannAlgebra H, (G.l2GeneratedAlgebra S).map G.left = N.toStarSubalgebra := by
  let e := equivalenceOfConcreteRange M G.left (G.left_injective hf) hrange
  let τ := G.normalTracialRepresentation h1 hf M hrange
  let S₀ := S.topologicalClosure
  let S₁ : StarSubalgebra ℂ M.toStarSubalgebra := S₀.map e.toStarAlgHom
  have hS₀ : IsClosed (S₀ : Set A) := S.isClosed_topologicalClosure
  let : IsClosed (S₀ : Set A) := hS₀
  have hS₁ : IsClosed (S₁ : Set M.toStarSubalgebra) := by
    change IsClosed (e '' (S₀ : Set A))
    exact (StarAlgEquiv.isometry e).isClosedEmbedding.isClosedMap _ hS₀
  let : IsClosed (S₁ : Set M.toStarSubalgebra) := hS₁
  let N := tracialSeedVonNeumann S₁
  have hN : N ≤ M := tracialSeedVonNeumann_le S₁
  have hv (a : A) : Generator.Tracial.baseVector τ (e a) = G.vector a := by
    change G.left a (G.vector 1) = G.vector a
    rw [G.left_vector, mul_one]
  have hset : Generator.Tracial.baseVector τ '' (S₁ : Set M.toStarSubalgebra) =
      Set.range (G.baseAlgebraVectors S₀) := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, heq⟩ := hb
      change e a = b at heq
      subst b
      exact ⟨⟨a, ha⟩, (hv a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e (a : A), ⟨(a : A), a.property, rfl⟩, hv (a : A)⟩
  have hmem (a : A) : G.left a ∈ N ↔ a ∈ G.l2GeneratedAlgebra S := by
    have h := normal_mem_iff_traceVector_mem_seed_closure S₁ τ (e a)
    rw [hv, hset] at h
    exact h
  refine ⟨N, ?_⟩
  ext T
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hmem a).mpr ha
  · intro hT
    have hTM : T ∈ G.left.range := by
      rw [hrange]
      exact hN hT
    obtain ⟨a, rfl⟩ := hTM
    exact ⟨a, (hmem a).mp hT, rfl⟩

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
