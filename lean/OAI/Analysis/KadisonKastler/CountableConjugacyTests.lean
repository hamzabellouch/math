import OAI.Analysis.KadisonKastler.AmenableEmbedding
import OAI.Analysis.KadisonKastler.StrongCommutantTests
import OAI.Analysis.KadisonKastler.UnitBallClosure
import OAI.Analysis.KadisonKastler.WeakCPLimits

namespace OAI

/-! # Countable tests for the implementer relation

Strongly dense contraction families determine both inclusions of a
unitary conjugacy. This is the algebraic equivalence used when forming
the measurable implementer relation in the central decomposition.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitBall_subset_algebra_iff (M N : VonNeumannAlgebra H) :
    unitBall M ⊆ N ↔ M ≤ N := by
  constructor
  · intro h x hx
    have hclip : unitBallClip x ∈ N :=
      h ⟨unitBallClip_mem M.toStarSubalgebra.toSubalgebra.toSubmodule hx,
        unitBallClip_norm_le x⟩
    have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have heq : ((max 1 ‖x‖ : ℝ) : ℂ) • unitBallClip x = x := by
      rw [unitBallClip, smul_smul]
      have hn : ((max 1 ‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      simp only [Complex.ofReal_inv, mul_inv_cancel₀ hn, one_smul]
    rw [← heq]
    exact N.toStarSubalgebra.smul_mem hclip _
  · exact fun h _ hx => h hx.1

theorem unitaryConj_mem_of_strong_tests (N : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (T : ℕ → H →L[ℂ] H) (x : H →L[ℂ] H)
    (hlim : ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (x ξ)))
    (hT : ∀ n, unitaryConj v (T n) ∈ N) : unitaryConj v x ∈ N := by
  let b (n : ℕ) : Algebra N := ⟨unitaryConj v (T n), hT n⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) N b (unitaryConj v x)
  intro ξ η
  have h := ((v : H →L[ℂ] H).continuous.tendsto _).comp
    (hlim (star (v : H →L[ℂ] H) ξ))
  have h' : Tendsto
      (fun n => inner ℂ η ((v : H →L[ℂ] H) (T n (star (v : H →L[ℂ] H) ξ)))) atTop
      (𝓝 (inner ℂ η ((v : H →L[ℂ] H) (x (star (v : H →L[ℂ] H) ξ))))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)).inner (𝕜 := ℂ) h
  simpa only [b, unitaryConj, mul_apply_eq_comp] using h'

theorem unitaryConj_inclusion_of_dense_tests
    (M N : VonNeumannAlgebra H) (v : unitary (H →L[ℂ] H))
    (E : Set (H →L[ℂ] H))
    (hdense : ∀ x ∈ unitBall M, ∃ T : ℕ → H →L[ℂ] H,
      (∀ n, T n ∈ E) ∧ ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (x ξ)))
    (hE : ∀ x ∈ E, unitaryConj v x ∈ N) :
    unitaryConjugateAlgebra v M ≤ N := by
  apply (unitBall_subset_algebra_iff _ _).mp
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (unitaryConj_unitBall
    (conjugates_unitaryConjugateAlgebra v M)).symm ▸ hy
  obtain ⟨T, hTE, hlim⟩ := hdense x hx
  exact unitaryConj_mem_of_strong_tests N v T x hlim (fun n => hE (T n) (hTE n))

/-- There are two countable contraction families that determine exactly
which ambient unitaries conjugate the two algebras. -/
theorem exists_countable_conjugacy_tests [SeparableSpace H]
    (M N : VonNeumannAlgebra H) :
    ∃ E F : Set (H →L[ℂ] H), E.Countable ∧ F.Countable ∧
      E ⊆ unitBall M ∧ F ⊆ unitBall N ∧
      ∀ v : unitary (H →L[ℂ] H), Conjugates v M N ↔
        (∀ x ∈ E, unitaryConj v x ∈ N) ∧
        (∀ y ∈ F, unitaryConj (star v) y ∈ M) := by
  obtain ⟨E, hEc, hEM, hE⟩ := exists_countable_strong_dense_contractions
    (unitBall M) (fun _ hx => hx.2)
  obtain ⟨F, hFc, hFN, hF⟩ := exists_countable_strong_dense_contractions
    (unitBall N) (fun _ hx => hx.2)
  refine ⟨E, F, hEc, hFc, hEM, hFN, fun v => ⟨?_, ?_⟩⟩
  · intro hv
    constructor
    · intro x hx
      exact hv.subset ⟨x, (hEM hx).1, rfl⟩
    · intro y hy
      exact hv.symm.subset ⟨y, (hFN hy).1, rfl⟩
  · rintro ⟨hEN, hFM⟩
    have hMN := unitaryConj_inclusion_of_dense_tests M N v E hE hEN
    have hNM := unitaryConj_inclusion_of_dense_tests N M (star v) F hF hFM
    apply Set.Subset.antisymm
    · exact hMN
    · intro y hy
      have hyM : unitaryConj (star v) y ∈ M := hNM ⟨y, hy, rfl⟩
      exact ⟨unitaryConj (star v) y, hyM, by
        simpa only [star_star] using unitaryConj_star_unitaryConj (star v) y⟩

end

end KadisonKastler

end OAI
