import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Basic.Denumerable
import Mathlib.Topology.Bases
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

noncomputable section

namespace Invariant233.UnitaryTransport

open scoped Topology
open TopologicalSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem countable_orthonormal_index [SeparableSpace E] {ι : Type*}
    {v : ι → E} (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (fun i j : ι =>
      Disjoint (Metric.ball (v i) (1 / 2 : ℝ)) (Metric.ball (v j) (1 / 2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hs : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    have hn := norm_nonneg (v i - v j)
    nlinarith
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, by simp⟩)

theorem infinite_hilbertBasis_index [CompleteSpace E] {ι : Type*}
    (b : HilbertBasis ι ℂ E) (hE : ¬ FiniteDimensional ℂ E) : Infinite ι := by
  classical
  by_contra h
  let : Finite ι := not_infinite_iff_finite.mp h
  let : Fintype ι := Fintype.ofFinite ι
  exact hE b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

theorem exists_nat_hilbertBasis [CompleteSpace E] [SeparableSpace E]
    (hE : ¬ FiniteDimensional ℂ E) : Nonempty (HilbertBasis ℕ ℂ E) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ E
  let : Countable w := countable_orthonormal_index b.orthonormal
  let : Infinite w := infinite_hilbertBasis_index b hE
  let e : ℕ ≃ w := Classical.choice inferInstance
  have hv : Orthonormal ℂ (fun n : ℕ => b (e n)) :=
    b.orthonormal.comp e e.injective
  refine ⟨HilbertBasis.mk hv ?_⟩
  have hr : Set.range (fun n : ℕ => b (e n)) = Set.range b := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  rw [hr, b.dense_span]

theorem nonempty_linearIsometryEquiv [CompleteSpace E] [CompleteSpace F]
    [SeparableSpace E] [SeparableSpace F]
    (hE : ¬ FiniteDimensional ℂ E) (hF : ¬ FiniteDimensional ℂ F) :
    Nonempty (E ≃ₗᵢ[ℂ] F) := by
  obtain ⟨bE⟩ := exists_nat_hilbertBasis hE
  obtain ⟨bF⟩ := exists_nat_hilbertBasis hF
  exact ⟨bE.repr.trans bF.repr.symm⟩

section Conjugation

variable [CompleteSpace E] [CompleteSpace F]

theorem norm_conj (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    ‖e.conjStarAlgEquiv T‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro x
    simpa using T.le_opNorm (e.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (e.conjStarAlgEquiv T))
    intro x
    simpa using (e.conjStarAlgEquiv T).le_opNorm (e x)

theorem norm_conj_pow (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (n : ℕ) :
    ‖(e.conjStarAlgEquiv T) ^ n‖ = ‖T ^ n‖ := by
  rw [← map_pow, norm_conj]

theorem norm_quasinilpotent_conj_iff (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    Filter.Tendsto (fun n : ℕ => ‖(e.conjStarAlgEquiv T) ^ n‖ ^ (1 / (n : ℝ)))
        Filter.atTop (𝓝 (0 : ℝ)) ↔
      Filter.Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ)))
        Filter.atTop (𝓝 (0 : ℝ)) := by
  simp only [norm_conj_pow]

theorem conj_ne_zero_iff (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    e.conjStarAlgEquiv T ≠ 0 ↔ T ≠ 0 := by
  exact not_congr (map_eq_zero_iff _ e.conjStarAlgEquiv.injective)

theorem no_hyperinvariant_subspace_conj
    (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E)
    (hT : ∀ S : Submodule ℂ E, IsClosed (S : Set E) →
      (∀ A : E →L[ℂ] E, Commute A T → ∀ x ∈ S, A x ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∀ S : Submodule ℂ F, IsClosed (S : Set F) →
      (∀ A : F →L[ℂ] F, Commute A (e.conjStarAlgEquiv T) →
        ∀ x ∈ S, A x ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS hInv
  let S' : Submodule ℂ E := S.comap e.toLinearEquiv.toLinearMap
  have hS' : IsClosed (S' : Set E) := hS.preimage e.continuous
  have hInv' : ∀ A : E →L[ℂ] E, Commute A T → ∀ x ∈ S', A x ∈ S' := by
    intro A hA x hx
    have h := hInv (e.conjStarAlgEquiv A) (hA.map e.conjStarAlgEquiv) (e x) hx
    simpa [S'] using h
  rcases hT S' hS' hInv' with hbot | htop
  · left
    apply le_antisymm _ bot_le
    intro y hy
    have hx : e.symm y ∈ S' := by simpa [S'] using hy
    rw [hbot, Submodule.mem_bot] at hx
    simpa using congrArg e hx
  · right
    apply le_antisymm le_top
    intro y _
    have hx : e.symm y ∈ S' := by rw [htop]; trivial
    simpa [S'] using hx

theorem transport_counterexample (e : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E)
    (hne : T ≠ 0)
    (hquasi : Filter.Tendsto (fun n : ℕ => ‖T ^ n‖ ^ (1 / (n : ℝ)))
      Filter.atTop (𝓝 (0 : ℝ)))
    (hhyper : ∀ S : Submodule ℂ E, IsClosed (S : Set E) →
      (∀ A : E →L[ℂ] E, Commute A T → ∀ x ∈ S, A x ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ T' : F →L[ℂ] F, T' ≠ 0 ∧
      Filter.Tendsto (fun n : ℕ => ‖T' ^ n‖ ^ (1 / (n : ℝ)))
        Filter.atTop (𝓝 (0 : ℝ)) ∧
      (∀ S : Submodule ℂ F, IsClosed (S : Set F) →
        (∀ A : F →L[ℂ] F, Commute A T' → ∀ x ∈ S, A x ∈ S) → S = ⊥ ∨ S = ⊤) := by
  exact ⟨e.conjStarAlgEquiv T, (conj_ne_zero_iff e T).2 hne,
    (norm_quasinilpotent_conj_iff e T).2 hquasi,
    no_hyperinvariant_subspace_conj e T hhyper⟩

end Conjugation

end Invariant233.UnitaryTransport

end

end OAI
