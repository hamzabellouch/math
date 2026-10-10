import OAI.Computability.PerfectCompleteness.Algebra.MatrixInverse
import OAI.Computability.PerfectCompleteness.Foundations.DummyEliminationLemmas

namespace OAI

section

namespace PerfectCompleteness.PartialTableInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixNoise
open UniqueGamesTheorem.Fourier.MatrixRestrictions UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.MatrixInverse

variable {Ω Y : Type*} [Fintype Y]

def indicator (f : Ω → Option Y) (y : Y) (X : Ω) : ℝ :=
  if f X = some y then 1 else 0

def definedEquality (f : Ω → Option Y) (X X' : Ω) : ℝ :=
  if ∃ y, f X = some y ∧ f X' = some y then 1 else 0

omit [Fintype Y] in
theorem indicator_boolean (f : Ω → Option Y) (y : Y) : IsBoolean (indicator f y) := by
  intro X
  unfold indicator
  split_ifs <;> simp

theorem sum_indicator_sq_le (f : Ω → Option Y) (X : Ω) :
    (∑ y, indicator f y X ^ 2) ≤ 1 := by
  cases h : f X <;> simp [indicator, h, eq_comm]

theorem definedEquality_eq_sum (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' = ∑ y, indicator f y X * indicator f y X' := by
  cases h : f X <;> cases h' : f X' <;>
    simp [definedEquality, indicator, h, h', mul_ite, eq_comm]

omit [Fintype Y] in
theorem definedEquality_le_self (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' ≤ definedEquality f X X := by
  unfold definedEquality
  split_ifs with h h' h'
  · exact le_rfl
  · obtain ⟨y, hy, _⟩ := h
    exact (h' ⟨y, hy, hy⟩).elim
  · norm_num
  · exact le_rfl

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

def stepAgreement (f : (E →ₗ[F2] F) → Option Y) (a : F) : ℝ :=
  𝔼 X, 𝔼 h : E →ₗ[F2] F2, definedEquality f X (X + h.smulRight a)

def allAgreement (f : (E →ₗ[F2] F) → Option Y) : ℝ :=
  𝔼 a : F, stepAgreement f a

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem uniform_operator_eq_average (g : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator (fun _ : F => (Fintype.card F : ℝ)⁻¹) g X =
      𝔼 a : F, 𝔼 h : E →ₗ[F2] F2, g (X + h.smulRight a) := by
  unfold linearRealNoiseOperator
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] in
theorem noiseEnergy_eq_average (g : (E →ₗ[F2] F) → ℝ) :
    noiseEnergy g =
      𝔼 X, 𝔼 a : F, 𝔼 h : E →ₗ[F2] F2, g X * g (X + h.smulRight a) := by
  unfold noiseEnergy
  simp_rw [uniform_operator_eq_average, Finset.mul_expect]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] in
theorem allAgreement_eq_sum (f : (E →ₗ[F2] F) → Option Y) :
    allAgreement f = ∑ y, noiseEnergy (indicator f y) := by
  unfold allAgreement stepAgreement
  rw [Finset.expect_comm]
  simp_rw [definedEquality_eq_sum, Finset.expect_sum_comm, ← noiseEnergy_eq_average]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype F] [Fintype (E →ₗ[F2] F2)] [Fintype (F →ₗ[F2] E)] in
theorem indicator_mass_le_one (f : (E →ₗ[F2] F) → Option Y) :
    (∑ y, 𝔼 X, indicator f y X ^ 2) ≤ 1 := by
  rw [← Finset.expect_sum_comm]
  calc
    _ ≤ 𝔼 _X : E →ₗ[F2] F, (1 : ℝ) :=
      Finset.expect_le_expect fun X _ => sum_indicator_sq_le f X
    _ = 1 := Fintype.expect_const _

theorem exists_dense_slice_all (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ allAgreement f) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (indicator f y) W C' T N) := by
  apply exists_dense_restriction_of_family r ρ η hρ hρ1 hconstants (indicator f)
    (indicator_boolean f) (indicator_mass_le_one f)
  rwa [← allAgreement_eq_sum]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype F] [Fintype (F →ₗ[F2] E)] [Fintype Y] in
theorem stepAgreement_le_zero (f : (E →ₗ[F2] F) → Option Y) (a : F) :
    stepAgreement f a ≤ stepAgreement f 0 := by
  apply Finset.expect_le_expect
  intro X _
  apply Finset.expect_le_expect
  intro h _
  simpa using definedEquality_le_self f X (X + h.smulRight a)

def nonzeroAgreement (f : (E →ₗ[F2] F) → Option Y) : ℝ :=
  𝔼 a : {a : F // a ≠ 0}, stepAgreement f a.val

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] [Fintype Y] in
theorem nonzeroAgreement_le_all [Nontrivial F]
    (f : (E →ₗ[F2] F) → Option Y) :
    nonzeroAgreement f ≤ allAgreement f :=
  PerfectCompleteness.NonzeroAverage.nonzero_expect_le_expect
    (stepAgreement f) (stepAgreement_le_zero f)

theorem exists_dense_slice_nonzero [Nontrivial F]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ nonzeroAgreement f) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (indicator f y) W C' T N) :=
  exists_dense_slice_all r ρ η hρ hρ1 hconstants f
    (hagreement.trans (nonzeroAgreement_le_all f))

end
end PerfectCompleteness.PartialTableInverse

end

end OAI
