import OAI.Analysis.FreeGroupFactor.InfiniteGeneration

namespace OAI

noncomputable section

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain

namespace InfiniteGeneration

 theorem one_step_none (ε : ℝ) (hε : 0 < ε) :
    ∃ α : M ≃⋆ₐ[ℂ] M,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : ℕ, α (extra (some k) : M) = (extra (some k) : M)) ∧
      ∃ w : FreeGroup (Fin 3),
        (∀ i, ‖α (initial i : M)-(initial i : M)‖ < ε) ∧
        twoNorm (α (Generation.word initial w)-(extra none : M)) < ε := by
  obtain ⟨α,ht,hfix,w,hA,hw⟩ := FiniteActive.one_step (κ := ℕ) 3 (by rfl) hε
  refine ⟨α,ht,hfix,w,hA,?_⟩
  rw [word_initial]
  exact hw

 theorem generating_tuple :
    ∃ U : Tuple,
      (∀ g : FreeGroup (Fin 3), canonicalTrace (Generation.word U g) = if g = 1 then 1 else 0) ∧
      ⊤ ≤ (Submodule.span ℂ (Set.range (fun g => groupL2 (Generation.word U g)))).topologicalClosure := by
  apply generating_haar_tuple
  apply orbit_local_approximation
  intro Φ ht s θ hθ
  apply orbit_step _ Φ ht s hθ
  intro s ε hε
  apply finite_absorption _ s ε hε
  intro q ε hε
  exact one_step_extra_of_none one_step_none q hε

 theorem rank_three_to_index : HasNormalTracialIso (FreeGroupRank 3) Group := by
  classical
  obtain ⟨U,ht,htotal⟩ := generating_tuple
  apply normalTracialIso_of_haar_total (Generation.word U)
  · intro g
    exact (Generation.word_inv U g).symm
  · exact ht
  · exact htotal

 def indexEquivNat : Index ≃ ℕ := by
  letI : Denumerable Index := Denumerable.ofEncodableOfInfinite Index
  exact Denumerable.eqv Index

end InfiniteGeneration

theorem rankThreeInfinite : HasNormalTracialIso (FreeGroupRank 3) (FreeGroup ℕ) :=
  InfiniteGeneration.rank_three_to_index.trans
    (normalTracialIso_of_groupEquiv (FreeGroup.freeGroupCongr InfiniteGeneration.indexEquivNat))

end FreeGroupFactorMain

end

end OAI
