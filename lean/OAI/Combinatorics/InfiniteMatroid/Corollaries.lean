import OAI.Combinatorics.InfiniteMatroid.Partitional
import OAI.Combinatorics.InfiniteMatroid.IntersectionReduction
import OAI.Combinatorics.InfiniteMatroid.SeparateCounterexamples
import OAI.Combinatorics.InfiniteMatroid.Main

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

theorem partitional_intersection_counterexample :
    Countable E ∧ Infinite E ∧
    ∃ Q : Matroid E0, Q.E = univ ∧ Q.dual = Q ∧ IsUniform Q ∧
      let M₀ := rayMatroid Q false
      let M₁ := rayMatroid Q true
      M₀.E = univ ∧ M₁.E = univ ∧ M₀.dual = M₀ ∧ M₁.dual = M₁ ∧
      IsPartitional M₀ ∧ IsPartitional M₁ ∧
      (∀ I₀ I₁ : Set E, M₀.Indep I₀ → M₁.Indep I₁ → I₀ ∪ I₁ ≠ univ) ∧
      ¬ HasPackingCovering M₀ M₁ ∧ ¬ HasIntersection M₀ M₁ := by
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
  have hnot : ¬ HasPackingCovering (rayMatroid Q false) (rayMatroid Q true) := by
    intro h
    obtain ⟨I,J,hI,hJ,hIJ⟩ := independent_cover_of_packing_covering
      (rayMatroid Q false) (rayMatroid Q true)
      (rayMatroid_ground Q hE false) (rayMatroid_ground Q hE true)
      (rayMatroid_selfDual Q hE hQ false) (rayMatroid_selfDual Q hE hQ true) h
    exact hn I J hI hJ hIJ
  refine ⟨inferInstance, inferInstance, Q, hE, hQ, S.isUniform,
    rayMatroid_ground Q hE false, rayMatroid_ground Q hE true,
    rayMatroid_selfDual Q hE hQ false, rayMatroid_selfDual Q hE hQ true,
    rayMatroid_isPartitional Q S.isUniform false,
    rayMatroid_isPartitional Q S.isUniform true, hn, hnot, ?_⟩
  intro h
  apply hnot
  have hr := packingCovering_of_intersection
    ((rayMatroid_ground Q hE true).trans (rayMatroid_ground Q hE false).symm) h
  rwa [rayMatroid_selfDual Q hE hQ true] at hr

end InfiniteMatroidCounterexample

end OAI
