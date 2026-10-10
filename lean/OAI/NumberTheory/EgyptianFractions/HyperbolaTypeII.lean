import OAI.NumberTheory.EgyptianFractions.HyperbolaCorrelation
import OAI.NumberTheory.EgyptianFractions.VaughanBilinear

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.HyperbolaCorrelation

lemma phase_eq_vaughan (x : ℝ) : phase x = VaughanBilinear.phase x := rfl

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Translation of an integer interval does not affect its geometric-sum bound. -/
theorem phase_sum_Icc_le (x : ℝ) (L U : ℕ) :
    ‖∑ m ∈ Finset.Icc L U, phase (x * (m : ℝ))‖ ≤
      VaughanBilinear.geometricBound (U + 1 - L) x := by
  have hI : Finset.Icc L U = Finset.Ico L (U + 1) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have hsum : (∑ m ∈ Finset.range (U + 1 - L), phase (x * ((L + m : ℕ) : ℝ))) =
      phase (x * L) * ∑ m ∈ Finset.range (U + 1 - L), phase (x * (m : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Nat.cast_add, mul_add, phase_add]
  rw [hsum, norm_mul, norm_phase, one_mul]
  exact VaughanBilinear.phase_sum_le_geometricBound x (U + 1 - L)

lemma geometricBound_mono {M N : ℕ} (hMN : M ≤ N) (x : ℝ) :
    VaughanBilinear.geometricBound M x ≤ VaughanBilinear.geometricBound N x := by
  unfold VaughanBilinear.geometricBound
  split_ifs
  · exact_mod_cast hMN
  · exact min_le_min_right _ (by exact_mod_cast hMN)

lemma geometricBound_nonneg (M : ℕ) (x : ℝ) :
    0 ≤ VaughanBilinear.geometricBound M x := by
  unfold VaughanBilinear.geometricBound
  split_ifs <;> positivity

/-- A hyperbolic correlation admits the same geometric majorant as a full
interval of rows. The moving endpoint introduces no additional loss. -/
theorem column_correlation_le (α : ℝ) (X L U n₁ n₂ : ℕ)
    (hn : 0 < max n₁ n₂) :
    ‖∑ m ∈ Finset.Icc L U, column α X n₁ m * conj (column α X n₂ m)‖ ≤
      VaughanBilinear.geometricBound (U + 1 - L) (α * ((n₁ : ℝ) - (n₂ : ℝ))) := by
  rw [column_correlation α X L U n₁ n₂ hn]
  have heq : (fun m : ℕ => phase (α * (m : ℝ) * ((n₁ : ℝ) - (n₂ : ℝ)))) =
      (fun m : ℕ => phase ((α * ((n₁ : ℝ) - (n₂ : ℝ))) * (m : ℝ))) := by
    funext m
    congr 1
    ring
  simp_rw [heq]
  exact (phase_sum_Icc_le _ L (min U (X / max n₁ n₂))).trans
    (geometricBound_mono (by omega) _)

/-- Type-II Cauchy--Schwarz for the actual region `m*n ≤ X`, with arbitrary
complex coefficients and all correlations replaced by explicit geometric bounds. -/
theorem norm_hyperbolic_bilinear_sq_le (α : ℝ) (X L U : ℕ) (t : Finset ℕ)
    (a b : ℕ → ℂ) (ht : ∀ n ∈ t, 0 < n) :
    ‖∑ m ∈ Finset.Icc L U, a m * ∑ n ∈ t, b n * column α X n m‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc L U, ‖a m‖ ^ 2) *
        (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
          VaughanBilinear.geometricBound (U + 1 - L) (α * ((n : ℝ) - (k : ℝ)))) := by
  apply (VaughanBilinear.norm_bilinear_sq_le (Finset.Icc L U) t a b
    (fun m n => column α X n m)).trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left
    (column_correlation_le α X L U n k ((ht n hn).trans_le (le_max_left _ _)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Separating the resonant diagonal in the geometric correlation majorant. -/
theorem geometric_correlation_sum_split (α : ℝ) (N : ℕ) (t : Finset ℕ) :
    (∑ n ∈ t, ∑ k ∈ t,
      VaughanBilinear.geometricBound N (α * ((n : ℝ) - (k : ℝ)))) =
      (N : ℝ) * t.card + ∑ n ∈ t, ∑ k ∈ t.erase n,
        VaughanBilinear.geometricBound N (α * ((n : ℝ) - (k : ℝ))) := by
  have hpoint (n : ℕ) (hn : n ∈ t) :
      (∑ k ∈ t, VaughanBilinear.geometricBound N (α * ((n : ℝ) - (k : ℝ)))) =
        (N : ℝ) + ∑ k ∈ t.erase n,
          VaughanBilinear.geometricBound N (α * ((n : ℝ) - (k : ℝ))) := by
    rw [← Finset.sum_erase_add (s := t)
      (fun k => VaughanBilinear.geometricBound N (α * ((n : ℝ) - (k : ℝ)))) hn]
    have hzero : VaughanBilinear.geometricBound N 0 = (N : ℝ) := by
      simp [VaughanBilinear.geometricBound, VaughanBilinear.phase]
    rw [sub_self, mul_zero, hzero]
    ring
  calc
    _ = ∑ n ∈ t, ((N : ℝ) + ∑ k ∈ t.erase n,
        VaughanBilinear.geometricBound N (α * ((n : ℝ) - (k : ℝ)))) :=
      Finset.sum_congr rfl hpoint
    _ = _ := by rw [Finset.sum_add_distrib]; simp [mul_comm]

/-- Bounded inner coefficients give a diagonal/off-diagonal Type-II estimate
on a hyperbola with exactly the same row-length factor as the rectangular case. -/
theorem norm_hyperbolic_bilinear_sq_le_offDiagonal
    (α : ℝ) (X L U : ℕ) (t : Finset ℕ) (a b : ℕ → ℂ)
    (ht : ∀ n ∈ t, 0 < n) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ n ∈ t, ‖b n‖ ≤ B) :
    ‖∑ m ∈ Finset.Icc L U, a m * ∑ n ∈ t, b n * column α X n m‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc L U, ‖a m‖ ^ 2) * B ^ 2 *
        (((U + 1 - L : ℕ) : ℝ) * t.card + ∑ n ∈ t, ∑ k ∈ t.erase n,
          VaughanBilinear.geometricBound (U + 1 - L) (α * ((n : ℝ) - (k : ℝ)))) := by
  have hweight : (∑ n ∈ t, ∑ k ∈ t, ‖b n‖ * ‖b k‖ *
      VaughanBilinear.geometricBound (U + 1 - L) (α * ((n : ℝ) - (k : ℝ)))) ≤
      B ^ 2 * ∑ n ∈ t, ∑ k ∈ t,
        VaughanBilinear.geometricBound (U + 1 - L) (α * ((n : ℝ) - (k : ℝ))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_right _ (geometricBound_nonneg _ _)
    simpa only [pow_two] using mul_le_mul (hb n hn) (hb k hk) (norm_nonneg _) hB
  calc
    _ ≤ _ := norm_hyperbolic_bilinear_sq_le α X L U t a b ht
    _ ≤ (∑ m ∈ Finset.Icc L U, ‖a m‖ ^ 2) *
        (B ^ 2 * ∑ n ∈ t, ∑ k ∈ t,
          VaughanBilinear.geometricBound (U + 1 - L) (α * ((n : ℝ) - (k : ℝ)))) :=
      mul_le_mul_of_nonneg_left hweight (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [geometric_correlation_sum_split]; ring

/-- A geometric row bound retains both coefficient energies for the actual
hyperbolic region. The cutoff costs no extra factor in the Schur estimate. -/
theorem norm_hyperbolic_bilinear_sq_le_energy
    (α : ℝ) (X L U : ℕ) (t : Finset ℕ) (a b : ℕ → ℂ)
    (ht : ∀ n ∈ t, 0 < n) (C : ℝ)
    (hrow : ∀ n ∈ t, (∑ k ∈ t,
      VaughanBilinear.geometricBound (U + 1 - L) (α * ((n : ℝ) - (k : ℝ)))) ≤ C) :
    ‖∑ m ∈ Finset.Icc L U, a m * ∑ n ∈ t, b n * column α X n m‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc L U, ‖a m‖ ^ 2) * C * (∑ n ∈ t, ‖b n‖ ^ 2) := by
  apply VaughanBilinear.norm_bilinear_sq_le_energy (Finset.Icc L U) t a b
    (fun m n => column α X n m) C
  intro n hn
  calc
    _ ≤ ∑ k ∈ t, VaughanBilinear.geometricBound (U + 1 - L)
        (α * ((n : ℝ) - (k : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact column_correlation_le α X L U n k
        ((ht n hn).trans_le (le_max_left _ _))
    _ ≤ C := hrow n hn

end Problem337.HyperbolaCorrelation

end

end OAI
