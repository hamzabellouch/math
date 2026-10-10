import OAI.Computability.UniqueGames.Inverse.RowErasureConcentration

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

def randomizedMatches {X Y : Type*} (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) : ℝ :=
  ∑ x ∈ s, indicator (B x ∧ replacement x = target x)

private theorem randomizedMatches_eq_masked_sum
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    randomizedMatches s B target replacement =
      ∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
  classical
  symm
  calc
    (∑ x, indicator (x ∈ s ∧ B x ∧ replacement x = target x)) =
        ∑ x ∈ s, indicator (x ∈ s ∧ B x ∧ replacement x = target x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro x _ hx
      simp [indicator, hx]
    _ = randomizedMatches s B target replacement := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [indicator, hx]

private theorem randomizedMatches_exp_product
    {X Y : Type*} [Fintype X] (s : Finset X) (B : X → Prop)
    (target replacement : X → Y) :
    Real.exp (randomizedMatches s B target replacement / 2) =
      ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2) := by
  rw [randomizedMatches_eq_masked_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul, Real.exp_sum]

private theorem table_randomizedMatches_mgf_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) =
      ∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) := by
  classical
  calc
    _ = Finset.univ.expect (fun replacement : X → Y =>
        ∏ x, Real.exp (indicator (x ∈ s ∧ B x ∧ replacement x = target x) / 2)) := by
      apply Finset.expect_congr rfl
      intro replacement _
      exact randomizedMatches_exp_product s B target replacement
    _ = _ := table_expect_prod (X := X) (Y := Y)
      (fun x y => Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))

private theorem table_randomizedMatches_product_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    (∏ x, Finset.univ.expect (fun y : Y =>
      Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  classical
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hpoint : ∀ x : X,
      Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2)) ≤
      Real.exp (if x ∈ s then c else 0) := by
    intro x
    by_cases hx : x ∈ s
    · simpa only [hx, true_and, ite_true] using table_coordinate_exp_le (B x) (target x)
    · simp [hx, indicator]
  calc
    (∏ x, Finset.univ.expect (fun y : Y =>
        Real.exp (indicator (x ∈ s ∧ B x ∧ y = target x) / 2))) ≤
        ∏ x, Real.exp (if x ∈ s then c else 0) := by
      apply Finset.prod_le_prod₀
      · intro x _
        exact Finset.expect_nonneg fun _ _ => (Real.exp_pos _).le
      · intro x _
        exact hpoint x
    _ = Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
      rw [← Real.exp_sum]
      congr 1
      simp [c, mul_comm]

theorem table_randomizedMatches_mgf_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y) :
    Finset.univ.expect (fun replacement : X → Y =>
      Real.exp (randomizedMatches s B target replacement / 2)) ≤
      Real.exp (3 / (4 * (Fintype.card Y : ℝ)) * s.card) := by
  rw [table_randomizedMatches_mgf_eq]
  exact table_randomizedMatches_product_le s B target

theorem uniformMass_mono {R : Type*} [Fintype R]
    {p q : R → Prop} (h : ∀ r, p r → q r) : uniformMass p ≤ uniformMass q := by
  classical
  apply Finset.expect_le_expect
  intro r _
  by_cases hp : p r
  · simp [indicator, hp, h r hp]
  · simpa [indicator, hp] using indicator_nonneg (q r)

/-- A full uniform table supplies independent coordinate samples. Only the
entries in `B ∩ s` contribute; all other entries deterministically contribute 0. -/
theorem table_randomizedMatches_tail_le
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : Finset X) (B : X → Prop) (target : X → Y)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) :
    uniformMass (fun replacement : X → Y =>
      α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
      Real.exp (-(α ^ 2 * s.card) / 32) := by
  classical
  let N : ℝ := s.card
  let c : ℝ := 3 / (4 * (Fintype.card Y : ℝ))
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hp : ∀ replacement : X → Y,
      indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Real.exp (randomizedMatches s B target replacement / 2) := by
    intro replacement
    by_cases h : α * s.card / 4 ≤ randomizedMatches s B target replacement
    · rw [show indicator (α * s.card / 4 ≤ randomizedMatches s B target replacement) = 1
          from by simp [indicator, h], ← Real.exp_add]
      apply Real.one_le_exp
      dsimp [N]
      linarith
    · simp only [indicator, ite_eq_right h]
      positivity
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun replacement _ => hp replacement)
  change uniformMass _ ≤ _ at hm
  rw [← Finset.mul_expect] at hm
  have hmgf := table_randomizedMatches_mgf_le s B target
  have hc : c ≤ 3 * α / 32 := by
    dsimp [c]
    calc
      3 / (4 * (Fintype.card Y : ℝ)) = (3 / 4) * (1 / (Fintype.card Y : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ 3 * α / 32 := by nlinarith [hsmall]
  have hexponent : -(α * N) / 8 + c * N ≤ -(α ^ 2 * N) / 32 := by
    have hcN := mul_le_mul_of_nonneg_right hc hN
    have hsq : α ^ 2 ≤ α := by
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hαone)]
    have hsqN := mul_le_mul_of_nonneg_right hsq hN
    nlinarith
  calc
    uniformMass (fun replacement : X → Y =>
        α * s.card / 4 ≤ randomizedMatches s B target replacement) ≤
        Real.exp (-(α * N) / 8) *
          Finset.univ.expect (fun replacement : X → Y =>
            Real.exp (randomizedMatches s B target replacement / 2)) := hm
    _ ≤ Real.exp (-(α * N) / 8) * Real.exp (c * N) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-(α * N) / 8 + c * N) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-(α ^ 2 * s.card) / 32) := Real.exp_le_exp.mpr hexponent

/-- The per-description bound used by the simultaneous erasure union bound. -/
theorem SliceFamily.randomizedAgreement_probability_le
    {X Y A S D : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (F : SliceFamily X Y A S D) (B : X → Prop) (α : ℝ)
    (hα : 0 < α) (hαone : α ≤ 1)
    (hsmall : 1 / (Fintype.card Y : ℝ) ≤ α / 8) (d : D) :
    uniformMass (fun replacement : X → Y =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d) ≤
      Real.exp (-(α ^ 2 * (F.points d).card) / 32) := by
  apply le_trans (uniformMass_mono ?_) (table_randomizedMatches_tail_le
    (F.points d) B (F.target d) α hα hαone hsmall)
  intro replacement h
  have hcard : (0 : ℝ) < (F.points d).card := Nat.cast_pos.mpr h.1.card_pos
  have hmass := h.2
  rw [SliceFamily.randomizedAgreement, Finset.expect_eq_sum_div_card] at hmass
  have hm := (le_div_iff₀ hcard).mp hmass
  dsimp [randomizedMatches]
  nlinarith

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI
