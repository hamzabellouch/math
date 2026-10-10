import OAI.NumberTheory.Ostmann.Arithmetic.MovingOuterKernel
import OAI.NumberTheory.Ostmann.Construction.SelectedPrimeFubini

namespace OAI

/-! # Retaining the inactive regular density under the bulk prime average -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def inactiveRegularDensity {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (x : σ → A) : ℝ :=
  ∏ j, if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹

theorem inactiveRegularDensity_bounds {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (reg : J → σ) (active : J → Bool) (x : σ → A) :
    0 ≤ inactiveRegularDensity prime reg active x ∧
      inactiveRegularDensity prime reg active x ≤ 1 := by
  have hlocal (j : J) : 0 ≤ (if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹) ∧
      (if active j then 1 else 1 - (prime (x (reg j)) : ℝ)⁻¹) ≤ 1 := by
    have hp : (1 : ℝ) ≤ prime (x (reg j)) := by exact_mod_cast (hprime _).one_le
    cases active j
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hp),
        sub_le_self _ (by positivity)⟩
    · simp
  exact ⟨Finset.prod_nonneg (fun j _ => (hlocal j).1),
    Finset.prod_le_one₀ (fun j _ => (hlocal j).1) (fun j _ => (hlocal j).2)⟩

/-- Inactive factors use only the fixed nonbulk coordinates. -/
theorem inactiveRegularDensity_joinBulkNonbulk {A σ J K : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (slot : K ↪ σ)
    (hfixed : ∀ j, active j = false → reg j ∉ Set.range slot)
    (x : σ → A) (z : K → A) :
    inactiveRegularDensity prime reg active (joinBulkNonbulk slot z (fun i => x i)) =
      inactiveRegularDensity prime reg active x := by
  apply Finset.prod_congr rfl
  intro j _
  cases ha : active j
  · have hj : reg j ∉ Set.range slot := hfixed j ha
    have he := joinBulkNonbulk_nonbulk slot z (fun i => x i) ⟨reg j, hj⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [he]
  · simp only [ite_true]

noncomputable def diagonalOuterMajorant (B D : ℝ) (diagonal : Bool) : ℝ :=
  1 + giantOuterScalar diagonal * (2 * B + D * (Real.exp 2 - 1)) ^ 2 *
    (if diagonal then 1 + Real.exp 2 else 2)

theorem diagonalOuterMajorant_pos (B D : ℝ) (diagonal : Bool) :
    0 < diagonalOuterMajorant B D diagonal := by
  unfold diagonalOuterMajorant
  have hs : 0 ≤ giantOuterScalar diagonal := by
    cases diagonal <;> simp [giantOuterScalar, (Real.exp_pos _).le]
  have hh : 0 ≤ (if diagonal then 1 + Real.exp 2 else (2 : ℝ)) := by
    cases diagonal <;> positivity
  positivity

noncomputable def movingDiagonalOuterWeight {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) : ℂ :=
  (giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v) *
    (inactiveRegularDensity prime reg active x : ℂ)) /
      (diagonalOuterMajorant B D diagonal : ℂ)

theorem movingDiagonalOuterWeight_norm {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) :
    ‖movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x‖ ≤ 1 := by
  have hc := diagonalOuterMajorant_pos B D diagonal
  have hd := inactiveRegularDensity_bounds prime hprime reg active x
  have ho := giantOuterWeight_norm φ Jleft Jright B D hB hD hφ hlip hout diagonal
    (Real.exp u) (Real.exp v)
  unfold movingDiagonalOuterWeight
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd.1,
    Complex.norm_real, Real.norm_of_nonneg hc.le]
  apply (div_le_one hc).mpr
  calc
    _ ≤ ‖giantOuterWeight φ Jleft Jright diagonal (Real.exp u) (Real.exp v)‖ * 1 :=
      mul_le_mul_of_nonneg_left hd.2 (norm_nonneg _)
    _ ≤ diagonalOuterMajorant B D diagonal := by
      rw [mul_one]
      exact ho.trans (by unfold diagonalOuterMajorant; linarith)

theorem movingDiagonalOuterWeight_measurable {A σ J : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (diagonal : Bool) (x : σ → A) :
    Measurable (fun z : ℝ × ℝ => movingDiagonalOuterWeight prime reg active φ
      Jleft Jright B D diagonal z.1 z.2 x) := by
  have hm := (measurable_giantOuterWeight φ Jleft Jright B D hB hD hφ hlip hout diagonal).comp
    ((Real.continuous_exp.measurable.comp measurable_fst).prodMk
      (Real.continuous_exp.measurable.comp measurable_snd))
  exact (hm.mul_const _).div_const _

theorem movingDiagonalOuterWeight_bulk {A σ J K : Type*} [Fintype J]
    (prime : A → ℕ) (reg : J → σ) (active : J → Bool) (slot : K ↪ σ)
    (hfixed : ∀ j, active j = false → reg j ∉ Set.range slot)
    (φ : ℝ → ℝ) (Jleft Jright B D : ℝ) (diagonal : Bool)
    (u v : ℝ) (x : σ → A) (z : K → A) :
    movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v
      (joinBulkNonbulk slot z (fun i => x i)) =
    movingDiagonalOuterWeight prime reg active φ Jleft Jright B D diagonal u v x := by
  unfold movingDiagonalOuterWeight
  rw [inactiveRegularDensity_joinBulkNonbulk prime reg active slot hfixed]

end Ostmann

end OAI
