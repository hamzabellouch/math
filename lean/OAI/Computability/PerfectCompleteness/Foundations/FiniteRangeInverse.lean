import Mathlib.LinearAlgebra.Dual.Lemmas
import OAI.Computability.PerfectCompleteness.Algebra.BilinearGramCompressionLemmas
import OAI.Computability.PerfectCompleteness.Algebra.MatrixInverseConstantsLemmas
import OAI.Computability.PerfectCompleteness.Foundations.PartialTableInverse

namespace OAI

section

namespace PerfectCompleteness.FiniteRangeInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.PartialTableInverse

attribute [local instance] linearMapFintype

universe u v w

variable {H : Type u} {K : Type v} {Y : Type w}
  [AddCommGroup H] [Module F2 H] [AddCommGroup K] [Module F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]

def matrixStep (X : Module.Dual F2 H →ₗ[F2] K) (a : K) (h : H) :
    Module.Dual F2 H →ₗ[F2] K :=
  X + (Module.Dual.eval F2 H h).smulRight a

omit [Fintype H] [Fintype K] [FiniteDimensional F2 H] [FiniteDimensional F2 K] in
@[simp] theorem matrixStep_apply (X : Module.Dual F2 H →ₗ[F2] K) (a : K)
    (h : H) (q : Module.Dual F2 H) : matrixStep X a h q = X q + q h • a := rfl

def agreement (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y) : ℝ :=
  𝔼 a : {a : K // a ≠ 0}, 𝔼 X : Module.Dual F2 H →ₗ[F2] K,
    𝔼 h : H, definedEquality f X (matrixStep X a.val h)

omit [Fintype Y] [FiniteDimensional F2 K] in
theorem agreement_eq_nonzeroAgreement
    (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y) :
    agreement f = nonzeroAgreement f := by
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro X _
  exact Fintype.expect_equiv (Module.evalEquiv F2 H).toEquiv
    (fun h : H => definedEquality f X (matrixStep X a.val h))
    (fun φ : Module.Dual F2 (Module.Dual F2 H) =>
      definedEquality f X (X + φ.smulRight a.val)) (fun _ => rfl)

theorem dense_slice_of_parameters [Nontrivial K]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : UniqueGamesTheorem.Fourier.MatrixLevelBridge.levelCutoffConstant r ρ +
      UniqueGamesTheorem.Appendix.RankLevelFilter.node (r + 1) < η)
    (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y) (hagreement : η ≤ agreement f) :
    ∃ (y : Y) (W : Submodule F2 (Module.Dual F2 H)) (C' : Submodule F2 K)
      (T : Module.Dual F2 H →ₗ[F2] K),
      order W C' ≤ r ∧
      ρ < (𝔼 X : MatrixSlice.Slice W C' T, indicator f y X.val) := by
  rw [agreement_eq_nonzeroAgreement] at hagreement
  obtain ⟨y, W, C', T, horder, hdensity⟩ :=
    exists_dense_slice_nonzero r ρ η hρ hρ1 hconstants f hagreement
  refine ⟨y, W, C', T, horder, ?_⟩
  rwa [MatrixSlice.expect_restrict_eq_slice] at hdensity

theorem inverse {η : ℝ} (hη : 0 < η) :
    ∃ r : Nat, 1 ≤ r ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ (H : Type u) (K : Type v) (Y : Type w)
        [AddCommGroup H] [Module F2 H] [AddCommGroup K] [Module F2 K]
        [Fintype H] [Fintype K] [Fintype Y]
        [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Nontrivial K]
        (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y),
        η ≤ agreement f →
        ∃ (y : Y) (W : Submodule F2 (Module.Dual F2 H)) (C' : Submodule F2 K)
          (T : Module.Dual F2 H →ₗ[F2] K),
          order W C' ≤ r ∧
          ρ < (𝔼 X : MatrixSlice.Slice W C' T, indicator f y X.val) := by
  obtain ⟨r, hr, ρ, hρ, hρ1, hconstants⟩ := MatrixInverseConstants.exists_cutoff_density hη
  refine ⟨r, hr, ρ, hρ, hρ1, ?_⟩
  intro H K Y _ _ _ _ _ _ _ _ _ _ f hagreement
  exact dense_slice_of_parameters r ρ η hρ hρ1 hconstants f hagreement

end
end PerfectCompleteness.FiniteRangeInverse

end

end OAI
