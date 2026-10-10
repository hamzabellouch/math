import OAI.Computability.PerfectCompleteness.Foundations.PartialTableInverse

namespace OAI

section

namespace PerfectCompleteness.MatrixErasure

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open PerfectCompleteness.PartialTableInverse

variable {Ω Y : Type*}

def erase (f : Ω → Option Y) (T : Ω → Prop) (X : Ω) : Option Y :=
  if T X then none else f X

def uniformMass [Fintype Ω] (T : Ω → Prop) : ℝ :=
  𝔼 X, if T X then (1 : ℝ) else 0

@[simp] theorem erase_eq_none_of (f : Ω → Option Y) (T : Ω → Prop)
    {X : Ω} (hX : T X) : erase f T X = none := by
  simp [erase, hX]

theorem erase_eq_of_not (f : Ω → Option Y) (T : Ω → Prop)
    {X : Ω} (hX : ¬T X) : erase f T X = f X := by
  simp [erase, hX]

theorem erase_eq_some_iff (f : Ω → Option Y) (T : Ω → Prop) (X : Ω) (y : Y) :
    erase f T X = some y ↔ ¬T X ∧ f X = some y := by
  by_cases hX : T X <;> simp [erase, hX]

theorem indicator_erase_le (f : Ω → Option Y) (T : Ω → Prop) (y : Y) (X : Ω) :
    indicator (erase f T) y X ≤ indicator f y X := by
  by_cases hX : T X
  · simp only [indicator, erase, ite_eq_left hX, reduceCtorEq, ite_false]
    split_ifs <;> norm_num
  · simp [indicator, erase, hX]

theorem definedEquality_erase (f : Ω → Option Y) (T : Ω → Prop) (X X' : Ω) :
    definedEquality (erase f T) X X' =
      if T X ∨ T X' then 0 else definedEquality f X X' := by
  by_cases hX : T X <;> by_cases hX' : T X' <;>
    simp [definedEquality, erase, hX, hX']

theorem definedEquality_le_one (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' ≤ 1 := by
  unfold definedEquality
  split_ifs <;> norm_num

theorem definedEquality_nonneg (f : Ω → Option Y) (X X' : Ω) :
    0 ≤ definedEquality f X X' := by
  unfold definedEquality
  split_ifs <;> norm_num

theorem definedEquality_erase_le (f : Ω → Option Y) (T : Ω → Prop) (X X' : Ω) :
    definedEquality (erase f T) X X' ≤ definedEquality f X X' := by
  rw [definedEquality_erase]
  split_ifs
  · exact definedEquality_nonneg f X X'
  · exact le_rfl

theorem definedEquality_le_erase_add (f : Ω → Option Y) (T : Ω → Prop) (X X' : Ω) :
    definedEquality f X X' ≤ definedEquality (erase f T) X X' +
      (if T X then (1 : ℝ) else 0) + (if T X' then (1 : ℝ) else 0) := by
  have hbound := definedEquality_le_one f X X'
  by_cases hX : T X <;> by_cases hX' : T X' <;>
    simp [definedEquality_erase, hX, hX'] <;> linarith

theorem uniformMass_nonneg [Fintype Ω] (T : Ω → Prop) : 0 ≤ uniformMass T := by
  apply Finset.expect_nonneg
  intro X _
  split_ifs <;> norm_num

theorem expect_add_right [AddGroup Ω] [Fintype Ω] (g : Ω → ℝ) (v : Ω) :
    (𝔼 X, g (X + v)) = (𝔼 X, g X) :=
  Fintype.expect_equiv (Equiv.addRight v) _ _ (fun _ => rfl)

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] F)]

omit [Fintype F] in
theorem step_second_marginal (g : (E →ₗ[F2] F) → ℝ) (a : F) :
    (𝔼 X, 𝔼 h : E →ₗ[F2] F2, g (X + h.smulRight a)) = (𝔼 X, g X) := by
  rw [Finset.expect_comm]
  simp_rw [expect_add_right]
  exact Fintype.expect_const _

theorem nonzero_second_marginal [Nontrivial F] (g : (E →ₗ[F2] F) → ℝ) :
    (𝔼 a : {a : F // a ≠ 0},
      𝔼 X, 𝔼 h : E →ₗ[F2] F2, g (X + h.smulRight a.val)) = (𝔼 X, g X) := by
  obtain ⟨a, ha⟩ := exists_ne (0 : F)
  let : Nonempty {a : F // a ≠ 0} := ⟨⟨a, ha⟩⟩
  simp_rw [step_second_marginal]
  exact Fintype.expect_const _

omit [Fintype F] in
theorem stepAgreement_erase_bound (f : (E →ₗ[F2] F) → Option Y)
    (T : (E →ₗ[F2] F) → Prop) (a : F) :
    stepAgreement f a ≤ stepAgreement (erase f T) a + 2 * uniformMass T := by
  have havg : stepAgreement f a ≤
      𝔼 X, 𝔼 h : E →ₗ[F2] F2,
        (definedEquality (erase f T) X (X + h.smulRight a) +
          (if T X then (1 : ℝ) else 0) +
          (if T (X + h.smulRight a) then (1 : ℝ) else 0)) := by
    apply Finset.expect_le_expect
    intro X _
    apply Finset.expect_le_expect
    intro h _
    exact definedEquality_le_erase_add f T X (X + h.smulRight a)
  simp_rw [Finset.expect_add_distrib, Fintype.expect_const] at havg
  rw [step_second_marginal (fun X => if T X then (1 : ℝ) else 0) a] at havg
  change stepAgreement f a ≤
    stepAgreement (erase f T) a + uniformMass T + uniformMass T at havg
  linarith

theorem nonzeroAgreement_erase [Nontrivial F] (f : (E →ₗ[F2] F) → Option Y)
    (T : (E →ₗ[F2] F) → Prop) :
    nonzeroAgreement f - 2 * uniformMass T ≤ nonzeroAgreement (erase f T) := by
  obtain ⟨a, ha⟩ := exists_ne (0 : F)
  let : Nonempty {a : F // a ≠ 0} := ⟨⟨a, ha⟩⟩
  have havg : nonzeroAgreement f ≤
      𝔼 a : {a : F // a ≠ 0}, (stepAgreement (erase f T) a.val + 2 * uniformMass T) := by
    unfold nonzeroAgreement
    apply Finset.expect_le_expect
    intro a _
    exact stepAgreement_erase_bound f T a.val
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  change nonzeroAgreement f ≤ nonzeroAgreement (erase f T) + 2 * uniformMass T at havg
  linarith

end
end PerfectCompleteness.MatrixErasure

end

end OAI
