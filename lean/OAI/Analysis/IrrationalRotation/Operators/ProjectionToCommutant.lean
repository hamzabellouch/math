import OAI.Analysis.IrrationalRotation.Operators.Commutant
import OAI.Analysis.IrrationalRotation.Operators.HyperinvariantProjection
import OAI.Analysis.IrrationalRotation.Operators.CommutantProper
import OAI.Analysis.IrrationalRotation.Spectral.QuasinilpotentNonscalar

namespace OAI

open Filter
open scoped Topology

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem hyperinvariant_subspace_trivial_of_invariant_projection_trivial
    (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T ∈ M)
    (hproj : ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1)
    (S : Submodule ℂ H) (hS : IsClosed (S : Set H))
    (hhyper : ∀ A : H →L[ℂ] H, Commute A T →
      S ∈ Module.End.invtSubmodule A) :
    S = ⊥ ∨ S = ⊤ := by
  let : CompleteSpace S := hS.completeSpace_coe
  obtain ⟨hmem, hinv⟩ := hyperinvariant_subspace_projection_mem M hT S hhyper
  rcases hproj S.starProjection hmem isStarProjection_starProjection hinv with hp | hp
  · left
    rw [← Submodule.range_starProjection S, hp]
    simp
  · right
    rw [← Submodule.range_starProjection S, hp]
    exact LinearMap.range_eq_top.mpr Function.surjective_id

omit [CompleteSpace H] in

theorem commutant_proper_of_nonzero_norm_quasinilpotent [Nontrivial H]
    {T : H →L[ℂ] H} (hT : T ≠ 0)
    (hq : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0)) :
    Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) ≠ ⊤ := by
  apply centralizer_singleton_ne_top_of_nonscalar
  rintro ⟨c, hc⟩
  exact InvariantProjection.continuousLinearMap_not_scalar_of_nonzero_norm_root_tendsto
    hT hq c hc

theorem no_hyperinvariant_of_invariant_projection_trivial
    (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T ∈ M)
    (hproj : ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1) :
    HasNoNontrivialHyperinvariantSubspace T := by
  intro S hS
  apply hyperinvariant_subspace_trivial_of_invariant_projection_trivial M hT hproj S hS.1
  intro A hA
  have hmem : A ∈ operatorCommutant T := by
    rw [operatorCommutant_mem_iff]
    exact hA.eq.symm
  exact hS.2 A hmem

theorem proper_stronglyClosed_transitive_commutant_of_projection_obstruction
    [Nontrivial H] (M : VonNeumannAlgebra H) {T : H →L[ℂ] H}
    (hT : T ∈ M) (hne : T ≠ 0)
    (hq : Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 0))
    (hproj : ∀ p : H →L[ℂ] H, p ∈ M → IsStarProjection p →
      (1 - p) * T * p = 0 → p = 0 ∨ p = 1) :
    HasNoNontrivialHyperinvariantSubspace T ∧
      operatorCommutant T ≠ ⊤ ∧ IsStronglyClosed (operatorCommutant T) ∧
      IsTransitive (operatorCommutant T) := by
  have hh := no_hyperinvariant_of_invariant_projection_trivial M hT hproj
  exact ⟨hh, commutant_proper_of_nonzero_norm_quasinilpotent hne hq,
    operatorCommutant_stronglyClosed T, (operatorCommutant_transitive_iff T).mpr hh⟩

end Invariant233

end OAI
