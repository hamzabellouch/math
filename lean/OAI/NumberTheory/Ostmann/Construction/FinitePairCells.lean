import OAI.NumberTheory.Ostmann.Construction.FiniteCellPrior

namespace OAI

/-! # Joint cells for the two different giant sampling spaces -/

namespace Ostmann

open scoped BigOperators Classical

theorem sum_cellPrior_mul {A C : Type*} [Fintype A] [Fintype C]
    (μ : A → ℝ) (cell : A → C) (F : C → ℂ) :
    (∑ a, (μ a : ℂ) * F (cell a)) = ∑ c, (cellPrior μ cell c : ℂ) * F c := by
  simp only [cellPrior, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem sum_pair_cells {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (μ : A → ℝ) (ρ : B → ℝ) (c : A → C) (d : B → D) (F : C × D → ℂ) :
    (∑ x : A × B, ((μ x.1 * ρ x.2 : ℝ) : ℂ) * F (c x.1, d x.2)) =
      ∑ y : C × D, ((cellPrior μ c y.1 * cellPrior ρ d y.2 : ℝ) : ℂ) * F y := by
  simp only [Fintype.sum_prod_type, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
  calc
    _ = ∑ a, (μ a : ℂ) * ∑ j, (cellPrior ρ d j : ℂ) * F (c a, j) := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact sum_cellPrior_mul ρ d (fun j => F (c a, j))
    _ = _ := sum_cellPrior_mul μ c
      (fun i => ∑ j, (cellPrior ρ d j : ℂ) * F (i, j))

theorem pair_prior_l1 {A B : Type*} [Fintype A] [Fintype B]
    (μ ν : A → ℝ) (ρ σ : B → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hρ : ∀ b, 0 ≤ ρ b)
    (hmassρ : ∑ b, ρ b ≤ 1) (hmassν : ∑ a, ν a ≤ 2)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (_hε : 0 ≤ ε)
    (hμν : ∑ a, |μ a - ν a| ≤ δ) (hρσ : ∑ b, |ρ b - σ b| ≤ ε) :
    (∑ x : A × B, |μ x.1 * ρ x.2 - ν x.1 * σ x.2|) ≤ δ + 2 * ε := by
  have hp (a : A) (b : B) : |μ a * ρ b - ν a * σ b| ≤
      |μ a - ν a| * ρ b + ν a * |ρ b - σ b| := by
    calc
      _ = |(μ a - ν a) * ρ b + ν a * (ρ b - σ b)| := by ring_nf
      _ ≤ _ := by
        simpa only [abs_mul, abs_of_nonneg (hρ b), abs_of_nonneg (hν a)]
          using abs_add_le ((μ a - ν a) * ρ b) (ν a * (ρ b - σ b))
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ a, ∑ b, (|μ a - ν a| * ρ b + ν a * |ρ b - σ b|) :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hp a b
    _ = (∑ a, |μ a - ν a|) * (∑ b, ρ b) +
        (∑ a, ν a) * (∑ b, |ρ b - σ b|) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ δ * 1 + 2 * ε := add_le_add
      (mul_le_mul hμν hmassρ (Finset.sum_nonneg fun b _ => hρ b) hδ)
      (mul_le_mul hmassν hρσ (Finset.sum_nonneg fun b _ => abs_nonneg _) (by norm_num))
    _ = _ := by ring

private theorem weighted_sum_difference {X : Type*} [Fintype X]
    (μ ν : X → ℝ) (F : X → ℂ) (B δ : ℝ) (hB : 0 ≤ B)
    (hF : ∀ x, ‖F x‖ ≤ B) (hdist : ∑ x, |μ x - ν x| ≤ δ) :
    ‖(∑ x, (μ x : ℂ) * F x) - ∑ x, (ν x : ℂ) * F x‖ ≤ B * δ := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, ← Complex.ofReal_sub]
  calc
    _ ≤ ∑ x, ‖((μ x - ν x : ℝ) : ℂ) * F x‖ := norm_sum_le _ _
    _ ≤ ∑ x, |μ x - ν x| * B := Finset.sum_le_sum fun x _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hF x) (abs_nonneg _)
    _ = (∑ x, |μ x - ν x|) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ δ * B := mul_le_mul_of_nonneg_right hdist hB
    _ = _ := mul_comm _ _

/-- The two giant spaces can be different. The original priors have mass
at most one; the ideal mass bound is derived from their cell errors. -/
theorem finite_pair_cell_idealization {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (μ : A → ℝ) (ρ : B → ℝ) (c : A → C) (d : B → D)
    (ν : C → ℝ) (σ : D → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hρ : ∀ b, 0 ≤ ρ b) (hν : ∀ a, 0 ≤ ν a)
    (hmassμ : ∑ a, μ a ≤ 1) (hmassρ : ∑ b, ρ b ≤ 1)
    (δ ε K η : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hsmall : Fintype.card C * δ ≤ 1)
    (hdistμ : ∀ a, |cellPrior μ c a - ν a| ≤ δ)
    (hdistρ : ∀ b, |cellPrior ρ d b - σ b| ≤ ε)
    (H : A × B → ℂ) (F : C × D → ℂ)
    (hF : ∀ y, ‖F y‖ ≤ K) (hfreeze : ∀ x, ‖H x - F (c x.1, d x.2)‖ ≤ η) :
    ‖(∑ x : A × B, ((μ x.1 * ρ x.2 : ℝ) : ℂ) * H x) -
      ∑ y : C × D, ((ν y.1 * σ y.2 : ℝ) : ℂ) * F y‖ ≤
      η + K * (Fintype.card C * δ + 2 * (Fintype.card D * ε)) := by
  have hmass : (∑ x : A × B, μ x.1 * ρ x.2) ≤ 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    exact (mul_le_mul hmassμ hmassρ
      (Finset.sum_nonneg fun b _ => hρ b) zero_le_one).trans_eq (by ring)
  have hf : ‖(∑ x : A × B, ((μ x.1 * ρ x.2 : ℝ) : ℂ) * H x) -
      ∑ x : A × B, ((μ x.1 * ρ x.2 : ℝ) : ℂ) * F (c x.1, d x.2)‖ ≤ η := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      _ ≤ ∑ x : A × B, ‖((μ x.1 * ρ x.2 : ℝ) : ℂ) *
          (H x - F (c x.1, d x.2))‖ := norm_sum_le _ _
      _ ≤ ∑ x : A × B, (μ x.1 * ρ x.2) * η := Finset.sum_le_sum fun x _ => by
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (hμ x.1) (hρ x.2))]
        exact mul_le_mul_of_nonneg_left (hfreeze x) (mul_nonneg (hμ x.1) (hρ x.2))
      _ = (∑ x : A × B, μ x.1 * ρ x.2) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * η := mul_le_mul_of_nonneg_right hmass hη
      _ = η := one_mul _
  rw [sum_pair_cells μ ρ c d F] at hf
  have hmν : ∑ a, ν a ≤ 2 :=
    (cellPrior_mass_comparison μ c ν δ hdistμ).trans (by linarith)
  have hp := pair_prior_l1 (cellPrior μ c) ν (cellPrior ρ d) σ hν
    (cellPrior_nonneg ρ d hρ) (by rw [cellPrior_mass]; exact hmassρ) hmν
    (Fintype.card C * δ) (Fintype.card D * ε)
    (mul_nonneg (Nat.cast_nonneg _) hδ) (mul_nonneg (Nat.cast_nonneg _) hε)
    (cellPrior_l1_le μ c ν δ hdistμ) (cellPrior_l1_le ρ d σ ε hdistρ)
  have hi := weighted_sum_difference
    (fun y : C × D => cellPrior μ c y.1 * cellPrior ρ d y.2)
    (fun y : C × D => ν y.1 * σ y.2) F K _ hK hF hp
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hf hi)

end Ostmann

end OAI
