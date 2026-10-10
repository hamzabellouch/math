import OAI.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
import OAI.Combinatorics.Progressions.Nilpotent.LocalNiltestFixedNativePartners

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem frequencyCodeKernel_eq_of_no_pivots
    {V J : Type*} [AddCommGroup V] [Module ℚ V] {r : ℕ}
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    (code : Fin r → Option J) (hnone : ∀ i, code i = none) :
    frequencyCodeKernel P eta code = P := by
  ext v
  rw [mem_frequencyCodeKernel]
  constructor
  · exact And.left
  · intro hv
    refine ⟨hv, ?_⟩
    intro i j hij
    rw [hnone i] at hij
    cases hij

namespace RationalFilteredNilmanifold.Niltest

variable {L X Y Ω J : Type*} [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L 1 d} {w : Y → ℕ}

theorem exists_noPivot_ambient_realization
    (S : D.Niltest w) (tests : Ω → D.Niltest w)
    (hcommon : ∀ a, (tests a).observable = S.observable)
    (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)
    (hnone : ∀ i, code i = none)
    (hinv : ∀ z : D.RealGroup,
      z.coord ∈ (frequencyCodeKernel (D.filtration.layer 1) eta code).baseChange ℝ →
      ∀ x, S.observable (z • x) = S.observable x)
    {p : ℝ} (hcomplexity : S.ComplexityLE p) (hunit : S.UnitIntervalValued) :
    ∃ ambient : D.Niltest (fun _ : X => 1),
      ambient.observable = S.observable ∧ ambient.UnitIntervalValued ∧
      ambient.ComplexityLE p ∧
      ∀ a x y, ambient.eval x = (tests a).eval y := by
  have hkernel : frequencyCodeKernel (D.filtration.layer 1) eta code = ⊤ := by
    rw [frequencyCodeKernel_eq_of_no_pivots _ _ _ hnone, D.filtration.one_eq_top]
  have hconst (g : D.RealGroup) :
      S.observable (QuotientGroup.mk g) =
        S.observable (QuotientGroup.mk (1 : D.RealGroup)) := by
    have hg : g.coord ∈ (frequencyCodeKernel (D.filtration.layer 1) eta code).baseChange ℝ := by
      rw [hkernel, Submodule.baseChange_top]
      trivial
    simpa using hinv g hg (QuotientGroup.mk (1 : D.RealGroup))
  refine ⟨S.withOrbit 1, rfl, hunit, hcomplexity, ?_⟩
  intro a x y
  change S.observable _ = (tests a).observable _
  rw [hcommon a]
  exact (hconst _).trans (hconst _).symm

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
