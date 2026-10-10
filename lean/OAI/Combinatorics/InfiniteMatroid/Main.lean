import OAI.Combinatorics.InfiniteMatroid.TransfiniteConstruction
import OAI.Combinatorics.InfiniteMatroid.RankDescent
import OAI.Combinatorics.InfiniteMatroid.PackingCovering

namespace OAI

section

open Set Filter Matroid
namespace InfiniteMatroidCounterexample

theorem main :
    Countable E ∧ Infinite E ∧
    ∃ M₀ M₁ : Matroid E,
      M₀.E = Set.univ ∧ M₁.E = Set.univ ∧
      M₀.dual = M₀ ∧ M₁.dual = M₁ ∧
      (∀ I₀ I₁ : Set E, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ Set.univ) ∧
      ¬ HasPackingCovering M₀ M₁ := by
  obtain ⟨R,hK⟩ := exists_concrete_rank
  obtain ⟨S,hS⟩ := R.exists_basisSystem hK
  let Q : Matroid E0 := S.matroid
  have hE : Q.E = Set.univ := S.ground
  have hQ : Q.dual = Q := S.self_dual
  have hanti : ∀ ⦃X Y : Set D⦄, X ∈ R.ultra → Y ∈ R.ultra → X ⊆ Y →
      R.rank Y ≤ R.rank X :=
    fun _ _ hX hY hXY ↦ R.antitone hX hY (R.ideal.modSubset_of_subset hXY)
  have hb : ∀ B, Q.IsBase B → (Prod.mk · false) ⁻¹' B ∈ R.ultra →
      ((Prod.mk · true) ⁻¹' B)ᶜ ∈ R.ultra ∧
      R.rank ((Prod.mk · true) ⁻¹' B)ᶜ < R.rank ((Prod.mk · false) ⁻¹' B) := by
    intro B hB hl
    have ha : R.Admissible B := hS B ((S.isBase_iff B).mp hB)
    rcases ha with ha | ha
    · exact ha.2
    · exact (ha.1 hl).elim
  have hn : ∀ I J : Set E, (rayMatroid Q false).Indep I →
      (rayMatroid Q true).Indep J → I ∪ J ≠ Set.univ :=
    no_independent_cover Q R.ultra R.rank hanti hb
  refine ⟨inferInstance, inferInstance, rayMatroid Q false, rayMatroid Q true,
    rayMatroid_ground Q hE false, rayMatroid_ground Q hE true,
    rayMatroid_selfDual Q hE hQ false, rayMatroid_selfDual Q hE hQ true, hn, ?_⟩
  intro h
  obtain ⟨I,J,hI,hJ,hIJ⟩ := independent_cover_of_packing_covering
    (rayMatroid Q false) (rayMatroid Q true)
    (rayMatroid_ground Q hE false) (rayMatroid_ground Q hE true)
    (rayMatroid_selfDual Q hE hQ false) (rayMatroid_selfDual Q hE hQ true) h
  exact hn I J hI hJ hIJ

end InfiniteMatroidCounterexample
end

end OAI
