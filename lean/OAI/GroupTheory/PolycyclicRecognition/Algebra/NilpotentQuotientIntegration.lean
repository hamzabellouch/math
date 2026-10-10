import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationInput
import Mathlib.Topology.ContinuousMap.Basic

namespace OAI

/-! # Integrating a nilpotent algebra quotient with a continuous section

Lee's Lie correspondence supplies the integrated homomorphism.
Surjectivity, the kernel description, and compact lifts follow from
the exponential charts.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN N EQ Q : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [NormedAddCommGroup EQ] [NormedSpace ℝ EQ] [FiniteDimensional ℝ EQ]
  [TopologicalSpace Q] [ChartedSpace EQ Q] [Group Q] [LieGroup (𝓘(ℝ, EQ)) ⊤ Q]

/-- A surjective Lie algebra homomorphism integrates to a surjective group
homomorphism with a continuous section obtained from a linear section in
logarithmic coordinates. -/
theorem exists_surjective_integration_with_section
    [SimplyConnectedSpace N]
    (integrate : NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EQ) (G := Q))
    (hnil : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, EN)) N))
    (j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EQ)) Q)
    (hj : Function.Surjective j)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, EQ)) Q → Q)
    (hExpN : IsGroupExponential ExpN) (hExpQ : IsGroupExponential ExpQ)
    (cN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hcN : ∀ x, cN x = ExpN x)
    (cQ : GroupLieAlgebra (𝓘(ℝ, EQ)) Q ≃ₜ Q) (hcQ : ∀ x, cQ x = ExpQ x) :
    ∃ (π : N →* Q) (s : C(Q, N)),
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EQ)) ∞ π ∧
      (∀ x, π (ExpN x) = ExpQ (j x)) ∧
      (∀ x, cQ.symm (π x) = j (cN.symm x)) ∧
      (∀ y, π (s y) = y) ∧ Function.Surjective π ∧
      (π.ker : Set N) = cN '' (j.ker : Set (GroupLieAlgebra (𝓘(ℝ, EN)) N)) ∧
      ∀ K : Set Q, IsCompact K → ∃ C : Set N, IsCompact C ∧ π '' C = K := by
  obtain ⟨π, hsmooth, _hdiff, hπexp⟩ :=
    integrate inferInstance hnil j ExpN ExpQ hExpN hExpQ
  obtain ⟨σ, hσ⟩ := j.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hj)
  have hσapply (y) : j (σ y) = y :=
    LinearMap.congr_fun hσ y
  let s : C(Q, N) :=
    ⟨fun y => cN (σ (cQ.symm y)),
      cN.continuous.comp (σ.toContinuousLinearMap.continuous.comp cQ.symm.continuous)⟩
  have hchart (x) : π (cN x) = cQ (j x) := by rw [hcN, hcQ, hπexp]
  have hlog (x : N) : cQ.symm (π x) = j (cN.symm x) := by
    obtain ⟨v, rfl⟩ := cN.surjective x
    rw [hchart, cQ.symm_apply_apply, cN.symm_apply_apply]
  have hc0 : cQ (0 : GroupLieAlgebra (𝓘(ℝ, EQ)) Q) = 1 :=
    (hcQ 0).trans hExpQ.map_zero
  have hlog0 : cQ.symm 1 = 0 := by
    apply cQ.injective
    rw [cQ.apply_symm_apply]
    exact hc0.symm
  have hs (y : Q) : π (s y) = y := by
    change π (cN (σ (cQ.symm y))) = y
    rw [hchart, hσapply, cQ.apply_symm_apply]
  refine ⟨π, s, hsmooth, hπexp, hlog, hs, (fun y => ⟨s y, hs y⟩), ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hx' : π x = 1 := hx
      refine ⟨cN.symm x, ?_, cN.apply_symm_apply x⟩
      change j (cN.symm x) = 0
      rw [← hlog, hx']
      exact hlog0
    · rintro ⟨v, hv, rfl⟩
      change π (cN v) = 1
      rw [hchart, show j v = 0 from hv, hcQ, hExpQ.map_zero]
  · intro K hK
    refine ⟨s '' K, hK.image s.continuous, ?_⟩
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hs]
    · intro hy
      exact ⟨s y, ⟨y, hy, rfl⟩, hs y⟩

end PolycyclicRecognition

end

end OAI
